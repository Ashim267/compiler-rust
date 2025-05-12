use std::process;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::collections::HashSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use sexp::{Atom, Sexp};
use im::HashMap;

// ========== Register & Instruction Definitions ==========

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Register {
    RAX,
    RBX,
    RSP,
    RBP,
    RDI,
    RSI,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Imm(i64),                   // Immediate constant value
    Reg(Register),              // Direct register reference
    RegOffset(Register, i32),   // Memory at offset from register
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    IMov(Value, Value),         // mov dst, src
    IAdd(Value, Value),         // add dst, src
    ISub(Value, Value),         // sub dst, src
    IMul(Value, Value),         // imul dst, src
    ICmp(Value, Value),         // cmp lhs, rhs
    ILabel(String),             // label:
    IJmp(String),               // jmp label
    IJe(String),                // je label (jump if equal)
    IJne(String),               // jne label (jump if not equal)
    IJl(String),                // jl label (jump if less)
    IJle(String),               // jle label (jump if less or equal)
    IJg(String),                // jg label (jump if greater)
    IJge(String),               // jge label (jump if greater or equal)
    IJno(String),               // jno label (jump if no overflow)
    ICall(String),              // call function
    Ret,                        // return
}

// Convert a register enum to its string representation
fn reg_to_str(r: Register) -> &'static str {
    match r {
        Register::RAX => "rax",
        Register::RBX => "rbx",
        Register::RSP => "rsp",
        Register::RBP => "rbp",
        Register::RDI => "rdi",
        Register::RSI => "rsi",
    }
}

// Convert a value enum into string form for assembly code
fn val_to_str(v: &Value) -> String {
    match v {
        Value::Imm(n)             => format!("{}", n),
        Value::Reg(r)             => reg_to_str(*r).to_string(),
        Value::RegOffset(r, off)  => {
            let base = reg_to_str(*r);
            if *off >= 0 {
                format!("[{} + {}]", base, off)
            } else {
                format!("[{} - {}]", base, -off)
            }
        }
    }
}

// Convert an instruction enum into corresponding assembly instruction
fn instr_to_str(i: &Instruction) -> String {
    match i {
        Instruction::IMov(dst, src)   => format!("mov {}, {}",   val_to_str(dst), val_to_str(src)),
        Instruction::IAdd(dst, src)   => format!("add {}, {}",   val_to_str(dst), val_to_str(src)),
        Instruction::ISub(dst, src)   => format!("sub {}, {}",   val_to_str(dst), val_to_str(src)),
        Instruction::IMul(dst, src)   => format!("imul {}, {}",  val_to_str(dst), val_to_str(src)),
        Instruction::ICmp(a, b)       => format!("cmp {}, {}",   val_to_str(a), val_to_str(b)),
        Instruction::ILabel(label)    => format!("{}:",          label),
        Instruction::IJmp(label)      => format!("jmp {}",       label),
        Instruction::IJe(label)       => format!("je {}",        label),
        Instruction::IJne(label)      => format!("jne {}",       label),
        Instruction::IJl(label)       => format!("jl {}",        label),
        Instruction::IJle(label)      => format!("jle {}",       label),
        Instruction::IJg(label)       => format!("jg {}",        label),
        Instruction::IJge(label)      => format!("jge {}",       label),
        Instruction::IJno(label)      => format!("jno {}",       label),
        Instruction::ICall(name)      => format!("call {}",      name),
        Instruction::Ret              => "ret".to_string(),
    }
}

// ========== AST Definitions ==========

#[derive(Debug, Clone, PartialEq, Eq)]
enum UnaryOp { Add1, Sub1 }

#[derive(Debug, Clone, PartialEq, Eq)]
enum BinaryOp {
    Plus, Minus, Times,
    Equal, Less, Greater,
    LessEqual, GreaterEqual,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expression {
    Number(i32),
    Boolean(bool),
    Input,
    Identifier(String),
    Let(Vec<(String, Expression)>, Box<Expression>),
    Unary(UnaryOp, Box<Expression>),
    Binary(BinaryOp, Box<Expression>, Box<Expression>),
    Set(String, Box<Expression>),
    If(Box<Expression>, Box<Expression>, Box<Expression>),
    Block(Vec<Expression>),
    RepeatUntil(Box<Expression>, Box<Expression>),
}

// ========== Parser Utilities ==========

// Check if a given string is a language keyword
fn is_keyword(sym: &str) -> bool {
    matches!(sym,
        "let" | "add1" | "sub1"
      | "+" | "-" | "*"
      | "true" | "false" | "input"
      | "set!" | "if" | "block"
      | "repeat-until"
      | "<" | "<=" | ">" | ">=" | "="
    )
}

// Parse a single `let` binding from S-expression form
fn parse_binding(sexp: &Sexp) -> (String, Expression) {
    if let Sexp::List(items) = sexp {
        if items.len() != 2 {
            panic!("Invalid binding: must contain exactly two elements");
        }

        let name = if let Sexp::Atom(Atom::S(sym)) = &items[0] {
            if is_keyword(sym) {
                panic!("Invalid binding name: '{}'", sym);
            }
            sym.clone()
        } else {
            panic!("Invalid binding name: expected symbol");
        };

        let value_expr = parse_expr(&items[1]);
        (name, value_expr)
    } else {
        panic!("Invalid binding: not a list");
    }
}

// Parses a single S-expression into an Expression enum (AST node)
fn parse_expr(s: &Sexp) -> Expression {
    match s {
        // Integer literal
        Sexp::Atom(Atom::I(n)) => {
            if *n < i32::MIN as i64 || *n > i32::MAX as i64 {
                eprintln!("Invalid number range");
                process::exit(1);
            }
            Expression::Number(*n as i32)
        }

        // Identifier, keyword, or special constants
        Sexp::Atom(Atom::S(sym)) => match sym.as_str() {
            "true"  => Expression::Boolean(true),
            "false" => Expression::Boolean(false),
            "input" => Expression::Input,
            s if is_keyword(s) => panic!("Invalid identifier: {}", s),
            _ => Expression::Identifier(sym.clone()),
        },

        // Complex expressions (Lists)
        Sexp::List(list) => {
            if list.is_empty() { panic!("Empty expression"); }

            let head = &list[0];
            if let Sexp::Atom(Atom::S(op)) = head {
                match op.as_str() {
                    // let bindings
                    "let" => {
                        let binds = if let Sexp::List(bs) = &list[1] {
                            bs.iter().map(parse_binding).collect()
                        } else {
                            panic!("Invalid let bindings");
                        };
                        let body = parse_expr(&list[2]);
                        Expression::Let(binds, Box::new(body))
                    }

                    // Unary operations
                    "add1" => Expression::Unary(UnaryOp::Add1, Box::new(parse_expr(&list[1]))),
                    "sub1" => Expression::Unary(UnaryOp::Sub1, Box::new(parse_expr(&list[1]))),

                    // Binary operations
                    "+"  => Expression::Binary(BinaryOp::Plus,         Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),
                    "-"  => Expression::Binary(BinaryOp::Minus,        Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),
                    "*"  => Expression::Binary(BinaryOp::Times,        Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),
                    "<"  => Expression::Binary(BinaryOp::Less,         Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),
                    "<=" => Expression::Binary(BinaryOp::LessEqual,    Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),
                    ">"  => Expression::Binary(BinaryOp::Greater,      Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),
                    ">=" => Expression::Binary(BinaryOp::GreaterEqual, Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),
                    "="  => Expression::Binary(BinaryOp::Equal,        Box::new(parse_expr(&list[1])), Box::new(parse_expr(&list[2]))),

                    // Variable mutation
                    "set!" => {
                        if list.len() != 3 { panic!("Invalid set! form"); }
                        let name = if let Sexp::Atom(Atom::S(n)) = &list[1] {
                            if is_keyword(n) { panic!("Invalid set! target"); }
                            n.clone()
                        } else {
                            panic!("Invalid set! target");
                        };
                        Expression::Set(name, Box::new(parse_expr(&list[2])))
                    }

                    // If expressions
                    "if" => {
                        if list.len() != 4 { panic!("Invalid if form"); }
                        Expression::If(
                            Box::new(parse_expr(&list[1])),
                            Box::new(parse_expr(&list[2])),
                            Box::new(parse_expr(&list[3])),
                        )
                    }

                    // Blocks of multiple expressions
                    "block" => {
                        if list.len() < 2 { panic!("block needs at least one expr"); }
                        let mut exprs = Vec::new();
                        for e in &list[1..] {
                            exprs.push(parse_expr(e));
                        }
                        Expression::Block(exprs)
                    }

                    // Repeat-until loops
                    "repeat-until" => {
                        if list.len() != 3 { panic!("Invalid repeat-until form"); }
                        Expression::RepeatUntil(
                            Box::new(parse_expr(&list[1])), // loop body
                            Box::new(parse_expr(&list[2])), // condition
                        )
                    }

                    other => panic!("Unknown operator: {}", other),
                }
            } else {
                panic!("Invalid expression form");
            }
        }

        _ => panic!("Invalid expression"),
    }
}

// ========== Static Type Checking ==========

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Type { Number, Boolean }

// Recursively checks types and ensures type correctness for expressions
fn type_check(expr: &Expression, env: &HashMap<String, Type>) -> Type {
    match expr {
        Expression::Number(_)       => Type::Number,
        Expression::Boolean(_)      => Type::Boolean,
        Expression::Input           => Type::Number,
        Expression::Identifier(n)   => *env.get(n)
                                      .unwrap_or_else(|| panic!("Unbound variable identifier {}", n)),

        // Type check let bindings and extend environment
        Expression::Let(bindings, body) => {
            let mut seen = HashSet::new();
            let mut env2 = env.clone();
            for (name, expr) in bindings {
                if !seen.insert(name) {
                    panic!("Duplicate binding {}", name);
                }
                let t = type_check(expr, &env2);
                env2 = env2.update(name.clone(), t);
            }
            type_check(body, &env2)
        }

        // Type check unary operation (only valid for numbers)
        Expression::Unary(_, sub_expr) => {
            let t = type_check(sub_expr, env);
            if t != Type::Number {
                panic!("Unary operator expects number");
            }
            Type::Number
        }

        // Type check binary operations
        Expression::Binary(op, left, right) => {
            let t_left = type_check(left, env);
            let t_right = type_check(right, env);

            match op {
                BinaryOp::Plus | BinaryOp::Minus | BinaryOp::Times
                    if t_left == Type::Number && t_right == Type::Number => Type::Number,

                BinaryOp::Less | BinaryOp::LessEqual |
                BinaryOp::Greater | BinaryOp::GreaterEqual
                    if t_left == Type::Number && t_right == Type::Number => Type::Boolean,

                BinaryOp::Equal if t_left == t_right => Type::Boolean,

                _ => panic!("type mismatch in binary operation"),
            }
        }

        // Type check variable mutation
        Expression::Set(name, new_expr) => {
            if !env.contains_key(name) {
                panic!("Unbound variable identifier {}", name);
            }
            let expr_type = type_check(new_expr, env);
            let expected = env.get(name).unwrap();
            if *expected != expr_type {
                panic!("type mismatch in set!");
            }
            expr_type
        }

        // If expressions must have Boolean condition and matching branches
        Expression::If(cond, then_expr, else_expr) => {
            if type_check(cond, env) != Type::Boolean {
                panic!("Condition must be boolean in if-expression");
            }
            let t_then = type_check(then_expr, env);
            let t_else = type_check(else_expr, env);
            if t_then != t_else {
                panic!("Branches of if-expression have different types");
            }
            t_then
        }

        // Block returns type of last expression
        Expression::Block(exprs) => {
            if exprs.is_empty() { panic!("block needs at least one expr"); }
            let mut last_type = Type::Number;
            for e in exprs {
                last_type = type_check(e, env);
            }
            last_type
        }

        // repeat-until returns type of loop body, condition must be Boolean
        Expression::RepeatUntil(body_expr, cond_expr) => {
            let t_body = type_check(body_expr, env);
            if type_check(cond_expr, env) != Type::Boolean {
                panic!("Condition in repeat-until must be boolean");
            }
            t_body
        }
    }
}
 
// ========== Code Generation ==========

// Global counter to generate fresh unique labels
static LABEL_COUNTER: AtomicUsize = AtomicUsize::new(0);

// Generates a new label in the form .L0, .L1, ...
fn fresh_label() -> String {
    let n = LABEL_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!(".L{}", n)
}

// Compiles an expression into a list of x86-64 instructions
fn compile_expr(e: &Expression, env: &HashMap<String, i32>, stack_offset: i32) -> Vec<Instruction> {
    let mut code = Vec::new();
    match e {
        // Load constant number into RAX
        Expression::Number(n) => {
            code.push(Instruction::IMov(Value::Reg(Register::RAX), Value::Imm(*n as i64)));
        }

        // Boolean literal: true = 1, false = 0
        Expression::Boolean(b) => {
            let imm = if *b { 1 } else { 0 };
            code.push(Instruction::IMov(Value::Reg(Register::RAX), Value::Imm(imm)));
        }

        // Read input from RDI (first argument)
        Expression::Input => {
            code.push(Instruction::IMov(Value::Reg(Register::RAX), Value::Reg(Register::RDI)));
        }

        // Load variable from environment stack offset
        Expression::Identifier(name) => {
            let off = *env.get(name)
                .expect(&format!("Unbound variable identifier {}", name));
            code.push(Instruction::IMov(Value::Reg(Register::RAX), Value::RegOffset(Register::RBP, off)));
        }

        // Let expression with multiple bindings
        Expression::Let(bindings, body) => {
            let mut new_env = env.clone();
            let mut seen = HashSet::new();
            for (n, _) in bindings {
                if !seen.insert(n) {
                    panic!("Duplicate binding {}", n);
                }
            }
            let total_size = bindings.len() * 8;
            let aligned = ((total_size + 15) / 16) * 16;

            // Allocate stack space
            code.push(Instruction::ISub(Value::Reg(Register::RSP), Value::Imm(aligned as i64)));

            for (i, (n, expr)) in bindings.iter().enumerate() {
                code.extend(compile_expr(expr, &new_env, stack_offset));
                let off = stack_offset + (i as i32 * 8);
                code.push(Instruction::IMov(
                    Value::RegOffset(Register::RBP, -off),
                    Value::Reg(Register::RAX),
                ));
                new_env = new_env.update(n.clone(), -off);
            }

            let new_so = stack_offset + aligned as i32;
            code.extend(compile_expr(body, &new_env, new_so));

            // Deallocate stack space
            code.push(Instruction::IAdd(Value::Reg(Register::RSP), Value::Imm(aligned as i64)));
        }

        // Unary operations
        Expression::Unary(op, sub) => {
            code.extend(compile_expr(sub, env, stack_offset));
            match op {
                UnaryOp::Add1 => code.push(Instruction::IAdd(Value::Reg(Register::RAX), Value::Imm(1))),
                UnaryOp::Sub1 => code.push(Instruction::ISub(Value::Reg(Register::RAX), Value::Imm(1))),
            }
        }

        // Binary operations
        Expression::Binary(op, a, b) => {
            // Save RBX to stack
            code.push(Instruction::ISub(Value::Reg(Register::RSP), Value::Imm(8)));
            code.push(Instruction::IMov(Value::RegOffset(Register::RSP, 0), Value::Reg(Register::RBX)));

            code.extend(compile_expr(a, env, stack_offset));
            code.push(Instruction::IMov(Value::Reg(Register::RBX), Value::Reg(Register::RAX)));
            code.extend(compile_expr(b, env, stack_offset));

            match op {
                BinaryOp::Plus => code.push(Instruction::IAdd(Value::Reg(Register::RAX), Value::Reg(Register::RBX))),
                BinaryOp::Minus => {
                    code.push(Instruction::ISub(Value::Reg(Register::RBX), Value::Reg(Register::RAX)));
                    code.push(Instruction::IMov(Value::Reg(Register::RAX), Value::Reg(Register::RBX)));
                }
                BinaryOp::Times => {
                    // Signed multiplication with overflow check
                    code.push(Instruction::IMul(Value::Reg(Register::RAX), Value::Reg(Register::RBX)));
                    let ok_lbl = fresh_label();
                    code.push(Instruction::IJno(ok_lbl.clone()));
                    code.push(Instruction::IMov(Value::Reg(Register::RDI), Value::Imm(1)));
                    code.push(Instruction::ICall("snek_error".to_string()));
                    code.push(Instruction::ILabel(ok_lbl));
                }

                BinaryOp::Equal => {
                    code.push(Instruction::ICmp(Value::Reg(Register::RBX), Value::Reg(Register::RAX)));
                    code.push(Instruction::ICall("set_equal_flag".to_string()));
                }

                _ => {
                    // Comparison operators: <, <=, >, >=
                    let lbl_true = fresh_label();
                    let lbl_end = fresh_label();
                    code.push(Instruction::ICmp(Value::Reg(Register::RBX), Value::Reg(Register::RAX)));

                    let jmp_instr = match op {
                        BinaryOp::Less         => Instruction::IJl(lbl_true.clone()),
                        BinaryOp::LessEqual    => Instruction::IJle(lbl_true.clone()),
                        BinaryOp::Greater      => Instruction::IJg(lbl_true.clone()),
                        BinaryOp::GreaterEqual => Instruction::IJge(lbl_true.clone()),
                        _ => unreachable!(),
                    };

                    code.push(jmp_instr);
                    code.push(Instruction::IMov(Value::Reg(Register::RAX), Value::Imm(0)));
                    code.push(Instruction::IJmp(lbl_end.clone()));
                    code.push(Instruction::ILabel(lbl_true));
                    code.push(Instruction::IMov(Value::Reg(Register::RAX), Value::Imm(1)));
                    code.push(Instruction::ILabel(lbl_end));
                }
            }

            // Restore RBX from stack
            code.push(Instruction::IMov(Value::Reg(Register::RBX), Value::RegOffset(Register::RSP, 0)));
            code.push(Instruction::IAdd(Value::Reg(Register::RSP), Value::Imm(8)));
        }

        // Set a variable in the environment
        Expression::Set(name, sub) => {
            code.extend(compile_expr(sub, env, stack_offset));
            let off = *env.get(name)
                .expect(&format!("Unbound variable identifier {}", name));
            code.push(Instruction::IMov(Value::RegOffset(Register::RBP, off), Value::Reg(Register::RAX)));
        }

        // If-else expression
        Expression::If(cond, then_expr, else_expr) => {
            let else_lbl = fresh_label();
            let end_lbl = fresh_label();
            code.extend(compile_expr(cond, env, stack_offset));
            code.push(Instruction::ICmp(Value::Reg(Register::RAX), Value::Imm(0)));
            code.push(Instruction::IJe(else_lbl.clone()));
            code.extend(compile_expr(then_expr, env, stack_offset));
            code.push(Instruction::IJmp(end_lbl.clone()));
            code.push(Instruction::ILabel(else_lbl));
            code.extend(compile_expr(else_expr, env, stack_offset));
            code.push(Instruction::ILabel(end_lbl));
        }

        // Sequential block of expressions
        Expression::Block(exprs) => {
            for e in exprs {
                code.extend(compile_expr(e, env, stack_offset));
            }
        }

        // Repeat-Until loop
        Expression::RepeatUntil(body, cond) => {
            let loop_lbl = fresh_label();
            let end_lbl = fresh_label();

            code.push(Instruction::ILabel(loop_lbl.clone()));

            // Compile loop body
            code.extend(compile_expr(body, env, stack_offset));

            // Save result of body
            code.push(Instruction::ISub(Value::Reg(Register::RSP), Value::Imm(8)));
            code.push(Instruction::IMov(
                Value::RegOffset(Register::RSP, 0),
                Value::Reg(Register::RAX),
            ));

            // Compile condition
            code.extend(compile_expr(cond, env, stack_offset));
            code.push(Instruction::ICmp(Value::Reg(Register::RAX), Value::Imm(0)));

            // If condition != 0, jump to end
            code.push(Instruction::IJne(end_lbl.clone()));

            // Otherwise loop again
            code.push(Instruction::IAdd(Value::Reg(Register::RSP), Value::Imm(8)));
            code.push(Instruction::IJmp(loop_lbl.clone()));

            // Exit loop and restore saved result
            code.push(Instruction::ILabel(end_lbl.clone()));
            code.push(Instruction::IMov(
                Value::Reg(Register::RAX),
                Value::RegOffset(Register::RSP, 0),
            ));
            code.push(Instruction::IAdd(Value::Reg(Register::RSP), Value::Imm(8)));
        }
    }
    code
}

// ========== Top-Level Compilation ==========

// Compile full expression into complete assembly string
fn compile(expr: &Expression, top_type: Type) -> String {
    let mut instrs = vec![
        // Function prologue: set up base pointer
        Instruction::ISub(Value::Reg(Register::RSP), Value::Imm(8)),
        Instruction::IMov(Value::RegOffset(Register::RSP, 0), Value::Reg(Register::RBP)),
        Instruction::IMov(Value::Reg(Register::RBP), Value::Reg(Register::RSP)),
    ];

    // Compile the expression body
    instrs.extend(compile_expr(expr, &HashMap::new(), 8));

    // Move result to rdi (for printing), rsi = is_bool flag (1 if boolean)
    let flag = if top_type == Type::Boolean { 1 } else { 0 };
    instrs.push(Instruction::IMov(Value::Reg(Register::RDI), Value::Reg(Register::RAX)));
    instrs.push(Instruction::IMov(Value::Reg(Register::RSI), Value::Imm(flag)));
    instrs.push(Instruction::ICall("snek_print".to_string()));

    // Function epilogue: restore stack frame and return
    instrs.push(Instruction::IMov(Value::Reg(Register::RSP), Value::Reg(Register::RBP)));
    instrs.push(Instruction::IMov(Value::Reg(Register::RBP), Value::RegOffset(Register::RSP, 0)));
    instrs.push(Instruction::IAdd(Value::Reg(Register::RSP), Value::Imm(8)));
    instrs.push(Instruction::Ret);

    // Convert instruction list to assembly string
    let mut output = String::new();
    output.push_str("section .text\n");
    output.push_str("global our_code_starts_here\n");
    output.push_str("extern snek_print\n");
    output.push_str("extern snek_error\n");
    output.push_str("our_code_starts_here:\n");

    for instr in instrs {
        output.push_str("  ");
        output.push_str(&instr_to_str(&instr));
        output.push_str("\n");
    }

    output
}

// ========== Main Entry Point ==========

// Entry point: parse input file → type check → compile → write .s output
fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();
    let in_name  = &args[1];
    let out_name = &args[2];

    // Read input file contents
    let mut text = String::new();
    File::open(in_name)?.read_to_string(&mut text)?;

    // Parse the S-expression into an Expression AST
    let sexp = sexp::parse(&text).expect("Invalid S-expression");
    let expr = parse_expr(&sexp);

    // Type check the expression
    let top_t = type_check(&expr, &HashMap::new());

    // Generate assembly code
    let asm = compile(&expr, top_t);

    // Write output to .s file
    File::create(out_name)?.write_all(asm.as_bytes())?;

    Ok(())
}
