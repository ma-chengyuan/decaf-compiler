main:
    subq $8, %rsp
    pushq %r14
    pushq %r15
    pushq %rbp
    pushq %rbx
main.block_0:     # entry
    xorq %r8, %r8
    movq $3, %rcx
    movq %r8, %r11
    .p2align 4,,10
    .p2align 3
main.block_2:     # for loop condition at line 20
    movq rows(%rip), %r9
    cmpq %r9, %r8
    jge main.block_3
main.block_1:     # for loop body at line 20
    cmpq $799997, %r11
    ja main.bound_check_fail.r11.0.800000.22
    movq image(, %r11, 8), %r14
    .set image.1, image + 8
    movq image.1(, %r11, 8), %rbx
    .set image.2, image + 16
    movq image.2(, %r11, 8), %r10
    movq %rcx, %rbp
    .p2align 4,,10
    .p2align 3
main.block_5:     # for loop condition at line 25
    movq cols(%rip), %r9
    cmpq %r9, %rbp
    jge main.block_6
main.block_4:     # for loop body at line 25
    imulq $4433, %r14, %r9
    imulq $54006, %rbx, %rdi
    addq %rdi, %r9
    imulq $242036, %r10, %rdi
    leaq (%r9, %rdi), %rsi
    leaq (%rbp, %r11), %rdi
    cmpq $799996, %rdi
    ja main.bound_check_fail.rdi.0.800000.30
    movq image(, %rdi, 8), %r15
    imulq $399050, %r15, %r9
    addq %r9, %rsi
    .set image.1, image + 8
    movq image.1(, %rdi, 8), %r9
    imulq $242036, %r9
    addq %r9, %rsi
    .set image.2, image + 16
    movq image.2(, %rdi, 8), %r9
    imulq $54006, %r9
    addq %r9, %rsi
    .set image.3, image + 24
    movq image.3(, %rdi, 8), %r9
    imulq $4433, %r9
    addq %rsi, %r9
    movabsq $-8775337516792518218, %rax
    imulq %r9
    addq %r9, %rdx
    sarq $19, %rdx
    shrq $63, %r9
    addq %rdx, %r9
    movq %r9, image(, %rdi, 8)
    addq $1, %rbp
    movq %rbx, %r14
    movq %r10, %rbx
    movq %r15, %r10
    jmp main.block_5
main.block_6:
    addq $1, %r8
    addq $768, %r11
    jmp main.block_2
main.block_3:
    xorq %rax, %rax
    popq %rbx
    popq %rbp
    popq %r15
    popq %r14
    addq $8, %rsp
    ret
main.bound_check_fail.r11.0.800000.22:
    movq %r11, %rcx
    movq $22, %rsi
    movq $800000, %rdx
    jmp bounds_check.fail
main.bound_check_fail.rdi.0.800000.30:
    movq %rdi, %rcx
    movq $30, %rsi
    movq $800000, %rdx
bounds_check.fail:
    leaq index_out_of_bounds_msg(%rip), %rdi
    call printf
    movq $-1, %rdi
    call exit

