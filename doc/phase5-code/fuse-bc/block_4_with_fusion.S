main.block_4:     # for loop body at line 18
    leaq (%r9, %rbx), %rcx
    leaq -1(%rcx), %rax
    cmpq $129391, %rax
    ja main.bound_check_fail.rcx._1.130000.20
    .set imageIn._1, imageIn + -8
    movq imageIn._1(, %rcx, 8), %r10
    movq imageIn(, %rcx, 8), %r11
    .set imageIn.1, imageIn + 8
    movq imageIn.1(, %rcx, 8), %rbp
    .set imageIn.302, imageIn + 2416
    movq imageIn.302(, %rcx, 8), %rsi
    .set imageIn.303, imageIn + 2424
    movq imageIn.303(, %rcx, 8), %r13
    .set imageIn.304, imageIn + 2432
    movq imageIn.304(, %rcx, 8), %rdi
    .set imageIn.605, imageIn + 4840
    movq imageIn.605(, %rcx, 8), %r8
    .set imageIn.606, imageIn + 4848
    movq imageIn.606(, %rcx, 8), %r12
    .set imageIn.607, imageIn + 4856
    movq imageIn.607(, %rcx, 8), %r15
    movq %rsi, %r14
    subq %r10, %r14