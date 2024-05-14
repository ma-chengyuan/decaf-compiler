main:
    subq $24, %rsp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    pushq %rbp
    pushq %rbx
main.block_0:     # entry
    movq $1, %rsi
    # No annotation available for inst load_const 303
    movq $303, %r15
    # No annotation available for inst load_const -303
    # No annotation available for inst load_const -1
    # No annotation available for inst load_const 304
    # No annotation available for inst load_const 302
    # Phi reg: {(6, 6), (10, 10), (6, 9)} mem: {}
    movq %rsi, %r14
    # Terminating block main.block_0
    .p2align 4,,10
    .p2align 3
main.block_2:     # for loop condition at line 17
    # No annotation available for inst phi { block_0 -> %1, block_6 -> %120 }
    movq rows(%rip), %r8
    addq $-1, %r8
    # Terminating block main.block_2
    cmpq %r8, %rsi
    jge main.block_3
main.block_1:     # for loop body at line 17
    leaq -303(%r15), %r12
    leaq 303(%r15), %r8
    # No annotation available for inst add %11, %1
    leaq 1(%rsi), %r9
    # No annotation available for inst store stack_0 %9
    movq %r9, 64(%rsp)
    movq %r8, 56(%rsp)
    # Phi reg: {(9, 3), (9, 9)} mem: {}
    movq %r14, %r11
    # Terminating block main.block_1
    .p2align 4,,10
    .p2align 3
main.block_5:     # for loop condition at line 18
    # No annotation available for inst phi { block_1 -> %119, block_46 -> %118 }
    movq cols(%rip), %r8
    addq $-1, %r8
    # Terminating block main.block_5
    cmpq %r8, %r14
    jge main.block_6
main.block_4:     # for loop body at line 18
    leaq (%r14, %r12), %r10
    leaq -1(%r10), %rax
    cmpq $129391, %rax
    ja main.bound_check_fail.r10._1.130000.20
    .set imageIn._1, imageIn + -8
    movq imageIn._1(, %r10, 8), %rsi
    movq imageIn(, %r10, 8), %rbx
    .set imageIn.1, imageIn + 8
    movq imageIn.1(, %r10, 8), %r15
    .set imageIn.302, imageIn + 2416
    movq imageIn.302(, %r10, 8), %r9
    .set imageIn.303, imageIn + 2424
    movq imageIn.303(, %r10, 8), %rbp
    .set imageIn.304, imageIn + 2432
    movq imageIn.304(, %r10, 8), %r11
    # No annotation available for inst load_const 606
    # No annotation available for inst load_const 605
    .set imageIn.605, imageIn + 4840
    movq imageIn.605(, %r10, 8), %rdi
    .set imageIn.606, imageIn + 4848
    movq imageIn.606(, %r10, 8), %r8
    # No annotation available for inst load_const 607
    .set imageIn.607, imageIn + 4856
    movq imageIn.607(, %r10, 8), %r13
    movq %r9, %rcx
    subq %rsi, %rcx
    # Terminating block main.block_4
    cmpq $0, %rcx
    jge main.block_47
main.block_7:     # if-then block at line 30
    # Phi reg: {(6, 1), (1, 6)} mem: {}
    xchg %r9, %rsi
    # Terminating block main.block_7
main.block_47:
    # Phi reg: {(1, 1), (6, 6)} mem: {}
    # Terminating block main.block_47
main.block_8:
    movq %rbp, %rcx
    subq %rbx, %rcx
    # Terminating block main.block_8
    cmpq $0, %rcx
    jge main.block_48
main.block_9:     # if-then block at line 35
    # Phi reg: {(11, 12), (12, 11)} mem: {}
    xchg %rbp, %rbx
    # Terminating block main.block_9
main.block_48:
    # Phi reg: {(12, 12), (11, 11)} mem: {}
    # Terminating block main.block_48
main.block_10:
    movq %r11, %rcx
    subq %r15, %rcx
    # Terminating block main.block_10
    cmpq $0, %rcx
    jge main.block_49
    # Phi reg: {(10, 10), (3, 3)} mem: {}
    # Terminating block main.block_11
    jmp main.block_12
main.block_49:
    # Phi reg: {(10, 3), (3, 10)} mem: {}
    xchg %r11, %r15
    # Terminating block main.block_49
main.block_12:
    movq %rbx, %rcx
    subq %rsi, %rcx
    # Terminating block main.block_12
    cmpq $0, %rcx
    jge main.block_50
main.block_13:     # if-then block at line 45
    # Phi reg: {(6, 11), (11, 6)} mem: {}
    xchg %rbx, %rsi
    # Terminating block main.block_13
main.block_50:
    # Phi reg: {(11, 11), (6, 6)} mem: {}
    # Terminating block main.block_50
main.block_14:
    movq %r11, %rcx
    subq %rsi, %rcx
    # Terminating block main.block_14
    cmpq $0, %rcx
    jge main.block_51
main.block_15:     # if-then block at line 50
    # Phi reg: {(6, 3)} mem: {}
    movq %rsi, %r11
    # Terminating block main.block_15
main.block_51:
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_51
main.block_16:
    movq %r15, %rcx
    subq %rbp, %rcx
    # Terminating block main.block_16
    cmpq $0, %rcx
    jge main.block_52
main.block_17:     # if-then block at line 55
    # Phi reg: {(12, 10), (10, 12)} mem: {}
    xchg %r15, %rbp
    # Terminating block main.block_17
main.block_52:
    # Phi reg: {(10, 10), (12, 12)} mem: {}
    # Terminating block main.block_52
main.block_18:
    movq %r15, %rcx
    subq %r9, %rcx
    # Terminating block main.block_18
    cmpq $0, %rcx
    jge main.block_53
main.block_19:     # if-then block at line 60
    # Phi reg: {(10, 1)} mem: {}
    movq %r15, %r9
    # Terminating block main.block_19
main.block_53:
    # Phi reg: {(1, 1)} mem: {}
    # Terminating block main.block_53
main.block_20:
    movq %r11, %rcx
    subq %rbx, %rcx
    # Terminating block main.block_20
    cmpq $0, %rcx
    jge main.block_54
    # Phi reg: {(3, 3), (11, 11)} mem: {}
    # Terminating block main.block_21
    jmp main.block_22
main.block_54:
    # Phi reg: {(11, 3), (3, 11)} mem: {}
    xchg %r11, %rbx
    # Terminating block main.block_54
main.block_22:
    movq %rbp, %rcx
    subq %r9, %rcx
    # Terminating block main.block_22
    cmpq $0, %rcx
    jge main.block_55
main.block_23:     # if-then block at line 70
    # Phi reg: {(12, 1), (1, 12)} mem: {}
    xchg %r9, %rbp
    # Terminating block main.block_23
main.block_55:
    # Phi reg: {(12, 12), (1, 1)} mem: {}
    # Terminating block main.block_55
main.block_24:
    movq %r9, %rcx
    subq %r11, %rcx
    # Terminating block main.block_24
    cmpq $0, %rcx
    jge main.block_56
    # Phi reg: {(3, 3), (1, 1)} mem: {}
    # Terminating block main.block_25
    jmp main.block_26
main.block_56:
    # Phi reg: {(3, 1), (1, 3)} mem: {}
    xchg %r9, %r11
    # Terminating block main.block_56
main.block_26:
    movq %rdi, %rcx
    subq %r9, %rcx
    # Terminating block main.block_26
    cmpq $0, %rcx
    jge main.block_57
    # Phi reg: {(1, 1)} mem: {}
    # Terminating block main.block_27
    jmp main.block_28
main.block_57:
    # Phi reg: {(5, 1)} mem: {}
    movq %rdi, %r9
    # Terminating block main.block_57
main.block_28:
    movq %r9, %rcx
    subq %rbp, %rcx
    # Terminating block main.block_28
    cmpq $0, %rcx
    jge main.block_58
main.block_29:     # if-then block at line 85
    # Phi reg: {(12, 1), (1, 12)} mem: {}
    xchg %r9, %rbp
    # Terminating block main.block_29
main.block_58:
    # Phi reg: {(12, 12), (1, 1)} mem: {}
    # Terminating block main.block_58
main.block_30:
    movq %r9, %rcx
    subq %rbx, %rcx
    # Terminating block main.block_30
    cmpq $0, %rcx
    jge main.block_59
    # Phi reg: {(1, 1)} mem: {}
    # Terminating block main.block_31
    jmp main.block_32
main.block_59:
    # Phi reg: {(11, 1)} mem: {}
    movq %rbx, %r9
    # Terminating block main.block_59
main.block_32:
    movq %r11, %rcx
    subq %r9, %rcx
    # Terminating block main.block_32
    cmpq $0, %rcx
    jge main.block_60
main.block_33:     # if-then block at line 95
    # Phi reg: {(3, 1), (1, 3)} mem: {}
    xchg %r9, %r11
    # Terminating block main.block_33
main.block_60:
    # Phi reg: {(3, 3), (1, 1)} mem: {}
    # Terminating block main.block_60
main.block_34:
    movq %r8, %rcx
    subq %rbp, %rcx
    # Terminating block main.block_34
    cmpq $0, %rcx
    jge main.block_61
main.block_35:     # if-then block at line 100
    # Phi reg: {(0, 12), (12, 0)} mem: {}
    xchg %rbp, %r8
    # Terminating block main.block_35
main.block_61:
    # Phi reg: {(0, 0), (12, 12)} mem: {}
    # Terminating block main.block_61
main.block_36:
    movq %rbp, %rcx
    subq %r9, %rcx
    # Terminating block main.block_36
    cmpq $0, %rcx
    jge main.block_62
main.block_37:     # if-then block at line 105
    # Phi reg: {(1, 12)} mem: {}
    movq %r9, %rbp
    # Terminating block main.block_37
main.block_62:
    # Phi reg: {(12, 12)} mem: {}
    # Terminating block main.block_62
main.block_38:
    movq %r8, %r9
    subq %r11, %r9
    # Terminating block main.block_38
    cmpq $0, %r9
    jge main.block_63
main.block_39:     # if-then block at line 110
    # Phi reg: {(0, 3)} mem: {}
    movq %r8, %r11
    # Terminating block main.block_39
main.block_63:
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_63
main.block_40:
    movq %r13, %r8
    subq %rbp, %r8
    # Terminating block main.block_40
    cmpq $0, %r8
    jge main.block_64
    # Phi reg: {(8, 8), (12, 12)} mem: {}
    # Terminating block main.block_41
    jmp main.block_42
main.block_64:
    # Phi reg: {(8, 12), (12, 8)} mem: {}
    xchg %rbp, %r13
    # Terminating block main.block_64
main.block_42:
    movq %rbp, %r8
    subq %r11, %r8
    # Terminating block main.block_42
    cmpq $0, %r8
    jge main.block_65
main.block_43:     # if-then block at line 120
    # Phi reg: {(12, 3)} mem: {}
    movq %rbp, %r11
    # Terminating block main.block_43
main.block_65:
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_65
main.block_44:
    movq %r13, %r8
    subq %r11, %r8
    # Terminating block main.block_44
    cmpq $0, %r8
    jge main.block_66
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_45
    jmp main.block_46
main.block_66:
    # Phi reg: {(8, 3)} mem: {}
    movq %r13, %r11
    # Terminating block main.block_66
main.block_46:
    # No annotation available for inst store_array global:imageOut[%15] %111
    leaq 303(%r10), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r10.303.130000.20
    .set imageOut.303, imageOut + 2424
    movq %r11, imageOut.303(, %r10, 8)
    # No annotation available for inst add %38, %1
    addq $1, %r14
    movq $1, %r11
    # Phi reg: {(9, 9), (3, 3)} mem: {}
    # Terminating block main.block_46
    jmp main.block_5
main.block_6:
    # No annotation available for inst load stack_0
    movq 64(%rsp), %rsi
    movq 56(%rsp), %r15
    # Phi reg: {(3, 9), (10, 10), (6, 6)} mem: {}
    movq %r11, %r14
    # Terminating block main.block_6
    jmp main.block_2
main.block_3:
    # Terminating block main.block_3
    xorq %rax, %rax
    popq %rbx
    popq %rbp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    addq $24, %rsp
    ret
main.bound_check_fail.r10._1.130000.20:
    movq %r10, %rcx
    addq $-1, %rcx
    movq $20, %rsi
    movq $130000, %rdx
    jmp bounds_check.fail
main.bound_check_fail.r10.303.130000.20:
    movq %r10, %rcx
    addq $303, %rcx
    movq $20, %rsi
    movq $130000, %rdx
bounds_check.fail:
    leaq index_out_of_bounds_msg(%rip), %rdi
    call printf
    movq $-1, %rdi
    call exit