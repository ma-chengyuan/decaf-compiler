main.block_4: # Not absorbing the const offset also causes bounds check fusion to fail.
    leaq (%r13, %r12), %r9
    leaq -1(%r9), %r8
    cmpq $129999, %r8
    ja main.bound_check_fail.r8.0.130000.20
    movq imageIn(, %r8, 8), %rbx
    cmpq $129999, %r9
    ja main.bound_check_fail.r9.0.130000.20
    movq imageIn(, %r9, 8), %rdi
    leaq 1(%r9), %r8
    cmpq $129999, %r8
    ja main.bound_check_fail.r8.0.130000.22
    movq imageIn(, %r8, 8), %rbp
    leaq 303(%r9), %r10
    leaq 302(%r9), %r8
    cmpq $129999, %r8
    ja main.bound_check_fail.r8.0.130000.23
    movq imageIn(, %r8, 8), %rcx
    cmpq $129999, %r10
    ja main.bound_check_fail.r10.0.130000.23
    movq imageIn(, %r10, 8), %rsi
    leaq 304(%r9), %r8
    cmpq $129999, %r8
    ja main.bound_check_fail.r8.0.130000.25
    movq imageIn(, %r8, 8), %r11
    leaq 606(%r9), %r14
    leaq 605(%r9), %r8
    cmpq $129999, %r8
    ja main.bound_check_fail.r8.0.130000.26
    movq imageIn(, %r8, 8), %r8
    cmpq $129999, %r14
    ja main.bound_check_fail.r14.0.130000.26
    movq imageIn(, %r14, 8), %r14
    addq $607, %r9
    cmpq $129999, %r9
    ja main.bound_check_fail.r9.0.130000.28
    movq imageIn(, %r9, 8), %r15
    movq %rcx, %r9
    subq %rbx, %r9