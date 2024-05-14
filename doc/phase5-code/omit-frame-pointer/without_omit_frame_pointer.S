big_call:
    pushq %rbp
    movq %rsp, %rbp
big_call.block_0:     # entry
    xorq %r8, %r8
    movq %r8, %rax
    leave
    ret
main:
    pushq %rbp
    movq %rsp, %rbp
    subq $8, %rsp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    pushq %rbx
main.block_0:     # entry
    movq A(%rip), %rdi
    movq B(%rip), %rsi
    movq C(%rip), %r15
    movq D(%rip), %rcx
    movq E(%rip), %r8
    movq F(%rip), %r9
    movq G(%rip), %r12
    movq H(%rip), %r11
    movq I(%rip), %rbx
    movq J(%rip), %r13
    movq K(%rip), %r14
    movq L(%rip), %r10
    movq %r10, -8(%rbp) # Must spill here!
    movq M(%rip), %r10
    subq $8, %rsp
    pushq %r10
    pushq -8(%rbp)
    pushq %r14
    pushq %r13
    pushq %rbx
    pushq %r11
    pushq %r12
    movq %r15, %rdx
    call big_call
    addq $64, %rsp
    movq %rax, %rdi
    call use_result
    xorq %rax, %rax
    popq %rbx
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    leave
    ret