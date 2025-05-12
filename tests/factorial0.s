section .text
global our_code_starts_here
extern snek_print
extern snek_error
our_code_starts_here:
  sub rsp, 8
  mov [rsp + 0], rbp
  mov rbp, rsp
  sub rsp, 16
  mov rax, 1
  mov [rbp - 8], rax
  mov rax, 1
  mov [rbp - 16], rax
  .L0:
  sub rsp, 8
  mov [rsp + 0], rbx
  mov rax, [rbp - 16]
  mov rbx, rax
  mov rax, [rbp - 8]
  imul rax, rbx
  jno .L2
  mov rdi, 1
  call snek_error
  .L2:
  mov rbx, [rsp + 0]
  add rsp, 8
  mov [rbp - 16], rax
  sub rsp, 8
  mov [rsp + 0], rbx
  mov rax, [rbp - 8]
  mov rbx, rax
  mov rax, 1
  add rax, rbx
  mov rbx, [rsp + 0]
  add rsp, 8
  mov [rbp - 8], rax
  mov rax, [rbp - 16]
  sub rsp, 8
  mov [rsp + 0], rax
  sub rsp, 8
  mov [rsp + 0], rbx
  mov rax, [rbp - 8]
  mov rbx, rax
  mov rax, rdi
  cmp rbx, rax
  jg .L3
  mov rax, 0
  jmp .L4
  .L3:
  mov rax, 1
  .L4:
  mov rbx, [rsp + 0]
  add rsp, 8
  cmp rax, 0
  jne .L1
  add rsp, 8
  jmp .L0
  .L1:
  mov rax, [rsp + 0]
  add rsp, 8
  add rsp, 16
  mov rdi, rax
  mov rsi, 0
  call snek_print
  mov rsp, rbp
  mov rbp, [rsp + 0]
  add rsp, 8
  ret
