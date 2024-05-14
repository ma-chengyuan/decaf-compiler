main:
    subq $8, %rsp
    pushq %r12
    pushq %r14
    pushq %rbp
    pushq %rbx
main.block_0:     # entry
    movq $0, %r14
    movq $3, %rbp
    movq %r14, %r11
    jmp main.block_2
    .p2align 4,,10
    .p2align 3
main.block_2:     # for loop condition at line 20
    movq rows(%rip), %r8
    cmpq %r8, %r14
    jl main.block_1
    jmp main.block_3
main.block_1:     # for loop body at line 20
    cmpq $799997, %r11
    ja main.bound_check_fail.r11.0.800000.22
    movq image(, %r11, 8), %rbx
    .set image.1, image + 8
    movq image.1(, %r11, 8), %r12
    .set image.2, image + 16
    movq image.2(, %r11, 8), %rsi
    movq %rbp, %rcx
    jmp main.block_5
    .p2align 4,,10
    .p2align 3
main.block_5:     # for loop condition at line 25
    movq cols(%rip), %r8
    cmpq %r8, %rcx
    jl main.block_4
    jmp main.block_6
main.block_4:     # for loop body at line 25
    imulq $4433, %rbx, %r8
    imulq $54006, %r12, %r9
    addq %r8, %r9
    imulq $242036, %rsi, %r8
    addq %r8, %r9
    leaq (%rcx, %r11), %rdi
    cmpq $799996, %rdi
    ja main.bound_check_fail.rdi.0.800000.30
    movq image(, %rdi, 8), %r10
    imulq $399050, %r10, %r8
    addq %r9, %r8
    .set image.1, image + 8
    movq image.1(, %rdi, 8), %r9
    imulq $242036, %r9
    addq %r8, %r9
    .set image.2, image + 16
    movq image.2(, %rdi, 8), %r8
    imulq $54006, %r8
    addq %r9, %r8
    .set image.3, image + 24
    movq image.3(, %rdi, 8), %r9
    imulq $4433, %r9
    addq %r9, %r8
    movabsq $-8775337516792518218, %rax
    imulq %r8
    addq %r8, %rdx
    sarq $19, %rdx
    shrq $63, %r8
    addq %rdx, %r8
    movq %r8, image(, %rdi, 8)
    addq $1, %rcx
    movq %r12, %rbx
    movq %rsi, %r12
    movq %r10, %rsi
    jmp main.block_5
main.block_6:
    addq $1, %r14
    addq $768, %r11
    jmp main.block_2
main.block_3:
    movq $0, %rax
    popq %rbx
    popq %rbp
    popq %r14
    popq %r12
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
    jmp bounds_check.fail
bounds_check.fail:
    leaq index_out_of_bounds_msg(%rip), %rdi
    call printf
    movq $-1, %rdi
    call exit