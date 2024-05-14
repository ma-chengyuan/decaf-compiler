main.block_4:     # for loop body at line 18
    leaq (%r9, %r14), %r8
    leaq -1(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8._1.130000.20
    .set imageIn._1, imageIn + -8
    movq imageIn._1(, %r8, 8), %rbx
    cmpq $129999, %r8
    ja main.bound_check_fail.r8.0.130000.20
    movq imageIn(, %r8, 8), %r13
    leaq 1(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.1.130000.20
    .set imageIn.1, imageIn + 8
    movq imageIn.1(, %r8, 8), %rbp
    leaq 302(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.302.130000.20
    .set imageIn.302, imageIn + 2416
    movq imageIn.302(, %r8, 8), %r15
    leaq 303(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.303.130000.20
    .set imageIn.303, imageIn + 2424
    movq imageIn.303(, %r8, 8), %rdi
    leaq 304(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.304.130000.20
    .set imageIn.304, imageIn + 2432
    movq imageIn.304(, %r8, 8), %r12
    leaq 605(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.605.130000.20
    .set imageIn.605, imageIn + 4840
    movq imageIn.605(, %r8, 8), %rcx
    leaq 606(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.606.130000.20
    .set imageIn.606, imageIn + 4848
    movq imageIn.606(, %r8, 8), %r11
    leaq 607(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.607.130000.20
    .set imageIn.607, imageIn + 4856
    movq imageIn.607(, %r8, 8), %rsi
    movq %r15, %r10
    subq %rbx, %r10
    # Terminating block main.block_4