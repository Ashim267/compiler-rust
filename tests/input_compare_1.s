section .text
global our_code_starts_here
extern snek_print
extern snek_error
our_code_starts_here:
  sub rsp, 8
  mov [rsp + 0], rbp
  mov rbp, rsp
  sub rsp, 8
  mov [rsp + 0], rbx
  mov rax, rdi
  mov rbx, rax
  mov rax, 5
  cmp rbx, rax
  jg .L2
  mov rax, 0
  jmp .L3
  .L2:
  mov rax, 1
  .L3:
  mov rbx, [rsp + 0]
  add rsp, 8
  cmp rax, 0
  je .L0
  mov rax, 1
  jmp .L1
  .L0:
  mov rax, 0
  .L1:
  mov rdi, rax
  mov rsi, 1
  call snek_print
  mov rsp, rbp
  mov rbp, [rsp + 0]
  add rsp, 8
  ret
