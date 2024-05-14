big_call:
    subq $8, %rsp
big_call.block_0:     # entry
    xorq %r8, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
main:
    subq $8, %rsp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    pushq %rbp
    pushq %rbx
main.block_0:     # entry
    movq A(%rip), %rdi
    movq B(%rip), %rsi
    movq C(%rip), %r11
    movq D(%rip), %rcx
    movq E(%rip), %r8
    movq F(%rip), %r9
    movq G(%rip), %r12
    movq H(%rip), %r13
    movq I(%rip), %r14
    movq J(%rip), %r15
    movq K(%rip), %rbx
    movq L(%rip), %rbp
    movq M(%rip), %r10
    subq $8, %rsp
    pushq %r10
    pushq %rbp
    pushq %rbx
    pushq %r15
    pushq %r14
    pushq %r13
    pushq %r12
    movq %r11, %rdx
    call big_call
    addq $64, %rsp
    movq %rax, %rdi
    call use_result
    xorq %rax, %rax
    popq %rbx
    popq %rbp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    addq $8, %rsp
    ret