section .text
global our_code_starts_here
extern snek_print
extern snek_error
our_code_starts_here:
  sub rsp, 8
  mov [rsp + 0], rbp
  mov rbp, rsp
  sub rsp, 16
  mov rax, 5
  mov [rbp - 8], rax
  sub rsp, 8
  mov [rsp + 0], rbx
  mov rax, [rbp - 8]
  mov rbx, rax
  mov rax, 1
  add rax, rbx
  mov rbx, [rsp + 0]
  add rsp, 8
  mov [rbp - 8], rax
  add rsp, 16
  mov rdi, rax
  mov rsi, 0
  call snek_print
  mov rsp, rbp
  mov rbp, [rsp + 0]
  add rsp, 8
  ret
