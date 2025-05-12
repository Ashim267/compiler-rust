section .text
global our_code_starts_here
extern snek_print
extern snek_error
our_code_starts_here:
  sub rsp, 8
  mov [rsp + 0], rbp
  mov rbp, rsp
  sub rsp, 48
  mov rax, 2
  mov [rbp - 8], rax
  mov rax, 3
  mov [rbp - 16], rax
  mov rax, 0
  mov [rbp - 24], rax
  mov rax, 0
  mov [rbp - 32], rax
  mov rax, 0
  mov [rbp - 40], rax
  .L0:
  mov rax, 0
  mov [rbp - 40], rax
  .L2:
  mov rax, [rbp - 40]
  add rax, 1
  mov [rbp - 40], rax
  mov rax, [rbp - 24]
  sub rax, 1
  mov [rbp - 24], rax
  sub rsp, 8
  mov [rsp + 0], rax
  sub rsp, 8
  mov [rsp + 0], rbx
  mov rax, [rbp - 40]
  mov rbx, rax
  mov rax, [rbp - 16]
  cmp rbx, rax
  jge .L4
  mov rax, 0
  jmp .L5
  .L4:
  mov rax, 1
  .L5:
  mov rbx, [rsp + 0]
  add rsp, 8
  cmp rax, 0
  jne .L3
  add rsp, 8
  jmp .L2
  .L3:
  mov rax, [rsp + 0]
  add rsp, 8
  mov rax, [rbp - 32]
  add rax, 1
  mov [rbp - 32], rax
  mov rax, [rbp - 24]
  sub rsp, 8
  mov [rsp + 0], rax
  sub rsp, 8
  mov [rsp + 0], rbx
  mov rax, [rbp - 32]
  mov rbx, rax
  mov rax, [rbp - 8]
  cmp rbx, rax
  jge .L6
  mov rax, 0
  jmp .L7
  .L6:
  mov rax, 1
  .L7:
  mov rbx, [rsp + 0]
  add rsp, 8
  cmp rax, 0
  jne .L1
  add rsp, 8
  jmp .L0
  .L1:
  mov rax, [rsp + 0]
  add rsp, 8
  add rsp, 48
  mov rdi, rax
  mov rsi, 0
  call snek_print
  mov rsp, rbp
  mov rbp, [rsp + 0]
  add rsp, 8
  ret
