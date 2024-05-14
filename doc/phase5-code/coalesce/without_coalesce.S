main:
    .loc 0 14 13
    subq $24, %rsp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    pushq %rbp
    pushq %rbx
main.block_0:     # entry
    .loc 0 15 7                        # i
    .loc 0 17 12                       # 1
    movq $1, %r8
    # No annotation available for inst load_const 303
    movq $303, %r9
    # No annotation available for inst load_const -1
    # No annotation available for inst load_const 302
    # No annotation available for inst load_const -303
    # No annotation available for inst load_const 304
    # Phi reg: {(0, 0), (1, 1), (0, 2)} mem: {}
    movq %r8, %r10
    # Terminating block main.block_0
    .p2align 4,,10
    .p2align 3
main.block_2:     # for loop condition at line 17
    # No annotation available for inst phi { block_6 -> %120, block_0 -> %1 }
    # No annotation available for inst phi { block_6 -> %117, block_0 -> %2 }
    .loc 0 15 7                        # i
    .loc 0 17 19                       # rows
    movq rows(%rip), %r11
    .loc 0 17 19                       # rows-1
    addq $-1, %r11
    .loc 0 17 15                       # i < rows-1
    # Terminating block main.block_2
    cmpq %r11, %r10
    jge main.block_3
main.block_1:     # for loop body at line 17
    leaq 303(%r9), %r11
    addq $-303, %r9
    # No annotation available for inst add %11, %1
    addq $1, %r10
    movq %r11, 64(%rsp)
    # No annotation available for inst store stack_1 %9
    movq %r10, 56(%rsp)
    # Phi reg: {(0, 0), (0, 2)} mem: {}
    movq %r8, %r10
    # Terminating block main.block_1
    .p2align 4,,10
    .p2align 3
main.block_5:     # for loop condition at line 18
    # No annotation available for inst phi { block_46 -> %118, block_1 -> %119 }
    .loc 0 15 10                       # j
    .loc 0 18 21                       # cols
    movq cols(%rip), %r11
    .loc 0 18 21                       # cols-1
    addq $-1, %r11
    .loc 0 18 17                       # j < cols-1
    # Terminating block main.block_5
    cmpq %r11, %r10
    jge main.block_6
main.block_4:     # for loop body at line 18
    .loc 0 20 20                       # (i-1)*303 + j
    leaq (%r10, %r9), %r8
    .loc 0 20 20                       # (i-1)*303 + j-1
    .loc 0 20 12                       # imageIn[(i-1)*303 + j-1]
    leaq -1(%r8), %rax
    cmpq $129391, %rax
    ja main.bound_check_fail.r8._1.130000.20
    .set imageIn._1, imageIn + -8
    movq imageIn._1(, %r8, 8), %r11
    .loc 0 21 12                       # imageIn[(i-1)*303 + j]
    movq imageIn(, %r8, 8), %rcx
    .loc 0 22 20                       # (i-1)*303 + j+1
    .loc 0 22 12                       # imageIn[(i-1)*303 + j+1]
    .set imageIn.1, imageIn + 8
    movq imageIn.1(, %r8, 8), %rdi
    .loc 0 23 20                       # i*303 + j
    .loc 0 23 20                       # i*303 + j-1
    .loc 0 23 12                       # imageIn[i*303 + j-1]
    .set imageIn.302, imageIn + 2416
    movq imageIn.302(, %r8, 8), %rsi
    .loc 0 24 12                       # imageIn[i*303 + j]
    .set imageIn.303, imageIn + 2424
    movq imageIn.303(, %r8, 8), %r12
    .loc 0 25 20                       # i*303 + j+1
    .loc 0 25 12                       # imageIn[i*303 + j+1]
    .set imageIn.304, imageIn + 2432
    movq imageIn.304(, %r8, 8), %r13
    # No annotation available for inst load_const 606
    .loc 0 26 20                       # (i+1)*303 + j
    # No annotation available for inst load_const 605
    .loc 0 26 20                       # (i+1)*303 + j-1
    .loc 0 26 12                       # imageIn[(i+1)*303 + j-1]
    .set imageIn.605, imageIn + 4840
    movq imageIn.605(, %r8, 8), %r14
    .loc 0 27 12                       # imageIn[(i+1)*303 + j]
    .set imageIn.606, imageIn + 4848
    movq imageIn.606(, %r8, 8), %r15
    # No annotation available for inst load_const 607
    .loc 0 28 20                       # (i+1)*303 + j+1
    .loc 0 28 12                       # imageIn[(i+1)*303 + j+1]
    .set imageIn.607, imageIn + 4856
    movq imageIn.607(, %r8, 8), %rbx
    .loc 0 29 14                       # p4 - p1
    movq %rsi, %rbp
    subq %r11, %rbp
    .loc 0 30 10                       # t[0] < 0
    # Terminating block main.block_4
    cmpq $0, %rbp
    jge main.block_47
    # Phi reg: {(3, 3), (6, 6)} mem: {}
    # Terminating block main.block_7
    jmp main.block_8
main.block_47:
    # Phi reg: {(6, 3), (3, 6)} mem: {}
    xchg %r11, %rsi
    # Terminating block main.block_47
main.block_8:
    .loc 0 19 23                       # p4
    .loc 0 19 11                       # p1
    .loc 0 34 14                       # p5 - p2
    movq %r12, %rbp
    subq %rcx, %rbp
    .loc 0 35 10                       # t[1] < 0
    # Terminating block main.block_8
    cmpq $0, %rbp
    jge main.block_48
    # Phi reg: {(7, 7), (4, 4)} mem: {}
    # Terminating block main.block_9
    jmp main.block_10
main.block_48:
    # Phi reg: {(7, 4), (4, 7)} mem: {}
    xchg %rcx, %r12
    # Terminating block main.block_48
main.block_10:
    .loc 0 19 27                       # p5
    .loc 0 19 15                       # p2
    .loc 0 39 14                       # p6 - p3
    movq %r13, %rbp
    subq %rdi, %rbp
    .loc 0 40 10                       # t[2] < 0
    # Terminating block main.block_10
    cmpq $0, %rbp
    jge main.block_49
    # Phi reg: {(5, 5), (8, 8)} mem: {}
    # Terminating block main.block_11
    jmp main.block_12
main.block_49:
    # Phi reg: {(5, 8), (8, 5)} mem: {}
    xchg %r13, %rdi
    # Terminating block main.block_49
main.block_12:
    .loc 0 19 31                       # p6
    .loc 0 19 19                       # p3
    .loc 0 44 14                       # p2 - p1
    movq %r12, %rbp
    subq %rsi, %rbp
    .loc 0 45 10                       # t[3] < 0
    # Terminating block main.block_12
    cmpq $0, %rbp
    jge main.block_50
    # Phi reg: {(6, 6), (7, 7)} mem: {}
    # Terminating block main.block_13
    jmp main.block_14
main.block_50:
    # Phi reg: {(6, 7), (7, 6)} mem: {}
    xchg %r12, %rsi
    # Terminating block main.block_50
main.block_14:
    .loc 0 19 15                       # p2
    .loc 0 19 11                       # p1
    .loc 0 49 14                       # p3 - p1
    movq %r13, %rbp
    subq %r12, %rbp
    .loc 0 50 10                       # t[4] < 0
    # Terminating block main.block_14
    cmpq $0, %rbp
    jge main.block_51
    # Phi reg: {(7, 7)} mem: {}
    # Terminating block main.block_15
    jmp main.block_16
main.block_51:
    # Phi reg: {(8, 7)} mem: {}
    movq %r13, %r12
    # Terminating block main.block_51
main.block_16:
    .loc 0 19 19                       # p3
    .loc 0 54 14                       # p6 - p5
    movq %rdi, %r13
    subq %rcx, %r13
    .loc 0 55 10                       # t[5] < 0
    # Terminating block main.block_16
    cmpq $0, %r13
    jge main.block_52
    # Phi reg: {(5, 5), (4, 4)} mem: {}
    # Terminating block main.block_17
    jmp main.block_18
main.block_52:
    # Phi reg: {(5, 4), (4, 5)} mem: {}
    xchg %rcx, %rdi
    # Terminating block main.block_52
main.block_18:
    .loc 0 19 31                       # p6
    .loc 0 19 27                       # p5
    .loc 0 59 14                       # p6 - p4
    movq %rcx, %r13
    subq %r11, %r13
    .loc 0 60 10                       # t[6] < 0
    # Terminating block main.block_18
    cmpq $0, %r13
    jge main.block_53
main.block_19:     # if-then block at line 60
    # Phi reg: {(4, 3)} mem: {}
    movq %rcx, %r11
    # Terminating block main.block_19
main.block_53:
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_53
main.block_20:
    .loc 0 19 23                       # p4
    .loc 0 64 14                       # p3 - p2
    movq %r12, %rcx
    subq %rsi, %rcx
    .loc 0 65 10                       # t[7] < 0
    # Terminating block main.block_20
    cmpq $0, %rcx
    jge main.block_54
main.block_21:     # if-then block at line 65
    # Phi reg: {(6, 4), (7, 6)} mem: {}
    movq %rsi, %rcx
    movq %r12, %rsi
    # Terminating block main.block_21
    jmp main.block_22
main.block_54:
    # Phi reg: {(6, 6), (7, 4)} mem: {}
    movq %r12, %rcx
    # Terminating block main.block_54
main.block_22:
    .loc 0 19 19                       # p3
    .loc 0 19 15                       # p2
    .loc 0 69 14                       # p5 - p4
    movq %rdi, %r12
    subq %r11, %r12
    .loc 0 70 10                       # t[8] < 0
    # Terminating block main.block_22
    cmpq $0, %r12
    jge main.block_55
    # Phi reg: {(5, 5), (3, 3)} mem: {}
    # Terminating block main.block_23
    jmp main.block_24
main.block_55:
    # Phi reg: {(3, 5), (5, 3)} mem: {}
    xchg %rdi, %r11
    # Terminating block main.block_55
main.block_24:
    .loc 0 19 27                       # p5
    .loc 0 19 23                       # p4
    .loc 0 74 14                       # p4 - p2
    movq %rdi, %r12
    subq %rsi, %r12
    .loc 0 75 10                       # t[9] < 0
    # Terminating block main.block_24
    cmpq $0, %r12
    jge main.block_56
main.block_25:     # if-then block at line 75
    # Phi reg: {(6, 5), (5, 6)} mem: {}
    xchg %rdi, %rsi
    # Terminating block main.block_25
main.block_56:
    # Phi reg: {(5, 5), (6, 6)} mem: {}
    # Terminating block main.block_56
main.block_26:
    .loc 0 19 23                       # p4
    .loc 0 19 15                       # p2
    .loc 0 79 15                       # p7 - p2
    movq %r14, %r12
    subq %rsi, %r12
    .loc 0 80 10                       # t[10] < 0
    # Terminating block main.block_26
    cmpq $0, %r12
    jge main.block_57
    # Phi reg: {(6, 6)} mem: {}
    # Terminating block main.block_27
    jmp main.block_28
main.block_57:
    # Phi reg: {(9, 6)} mem: {}
    movq %r14, %rsi
    # Terminating block main.block_57
main.block_28:
    .loc 0 19 35                       # p7
    .loc 0 84 15                       # p7 - p5
    movq %rsi, %r12
    subq %r11, %r12
    .loc 0 85 10                       # t[11] < 0
    # Terminating block main.block_28
    cmpq $0, %r12
    jge main.block_58
    # Phi reg: {(3, 3), (6, 6)} mem: {}
    # Terminating block main.block_29
    jmp main.block_30
main.block_58:
    # Phi reg: {(3, 6), (6, 3)} mem: {}
    xchg %rsi, %r11
    # Terminating block main.block_58
main.block_30:
    .loc 0 19 35                       # p7
    .loc 0 19 27                       # p5
    .loc 0 89 15                       # p7 - p3
    movq %r11, %r12
    subq %rcx, %r12
    .loc 0 90 10                       # t[12] < 0
    # Terminating block main.block_30
    cmpq $0, %r12
    jge main.block_59
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_31
    jmp main.block_32
main.block_59:
    # Phi reg: {(4, 3)} mem: {}
    movq %rcx, %r11
    # Terminating block main.block_59
main.block_32:
    .loc 0 19 19                       # p3
    .loc 0 94 15                       # p4 - p3
    movq %rdi, %rcx
    subq %r11, %rcx
    .loc 0 95 10                       # t[13] < 0
    # Terminating block main.block_32
    cmpq $0, %rcx
    jge main.block_60
main.block_33:     # if-then block at line 95
    # Phi reg: {(3, 3), (5, 4)} mem: {}
    movq %rdi, %rcx
    # Terminating block main.block_33
    jmp main.block_34
main.block_60:
    # Phi reg: {(5, 3), (3, 4)} mem: {}
    movq %r11, %rcx
    movq %rdi, %r11
    # Terminating block main.block_60
main.block_34:
    .loc 0 19 23                       # p4
    .loc 0 19 19                       # p3
    .loc 0 99 15                       # p8 - p5
    movq %r15, %rdi
    subq %rsi, %rdi
    .loc 0 100 10                      # t[14] < 0
    # Terminating block main.block_34
    cmpq $0, %rdi
    jge main.block_61
main.block_35:     # if-then block at line 100
    # Phi reg: {(6, 5), (10, 6)} mem: {}
    movq %rsi, %rdi
    movq %r15, %rsi
    # Terminating block main.block_35
    jmp main.block_36
main.block_61:
    # Phi reg: {(6, 6), (10, 5)} mem: {}
    movq %r15, %rdi
    # Terminating block main.block_61
main.block_36:
    .loc 0 19 39                       # p8
    .loc 0 19 27                       # p5
    .loc 0 104 15                      # p5 - p3
    movq %rsi, %r12
    subq %rcx, %r12
    .loc 0 105 10                      # t[15] < 0
    # Terminating block main.block_36
    cmpq $0, %r12
    jge main.block_62
    # Phi reg: {(4, 4)} mem: {}
    # Terminating block main.block_37
    jmp main.block_38
main.block_62:
    # Phi reg: {(6, 4)} mem: {}
    movq %rsi, %rcx
    # Terminating block main.block_62
main.block_38:
    .loc 0 19 27                       # p5
    .loc 0 109 15                      # p8 - p4
    movq %rdi, %rsi
    subq %r11, %rsi
    .loc 0 110 10                      # t[16] < 0
    # Terminating block main.block_38
    cmpq $0, %rsi
    jge main.block_63
main.block_39:     # if-then block at line 110
    # Phi reg: {(5, 3)} mem: {}
    movq %rdi, %r11
    # Terminating block main.block_39
main.block_63:
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_63
main.block_40:
    .loc 0 19 23                       # p4
    .loc 0 114 15                      # p9 - p5
    movq %rbx, %rdi
    subq %rcx, %rdi
    .loc 0 115 10                      # t[17] < 0
    # Terminating block main.block_40
    cmpq $0, %rdi
    jge main.block_64
main.block_41:     # if-then block at line 115
    # Phi reg: {(4, 4), (11, 5)} mem: {}
    movq %rbx, %rdi
    # Terminating block main.block_41
    jmp main.block_42
main.block_64:
    # Phi reg: {(11, 4), (4, 5)} mem: {}
    movq %rcx, %rdi
    movq %rbx, %rcx
    # Terminating block main.block_64
main.block_42:
    .loc 0 19 43                       # p9
    .loc 0 19 27                       # p5
    .loc 0 119 15                      # p9 - p4
    movq %rcx, %rsi
    subq %r11, %rsi
    .loc 0 120 10                      # t[18] < 0
    # Terminating block main.block_42
    cmpq $0, %rsi
    jge main.block_65
main.block_43:     # if-then block at line 120
    # Phi reg: {(4, 3)} mem: {}
    movq %rcx, %r11
    # Terminating block main.block_43
main.block_65:
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_65
main.block_44:
    .loc 0 19 23                       # p4
    .loc 0 124 15                      # p5 - p4
    movq %rdi, %rcx
    subq %r11, %rcx
    .loc 0 125 10                      # t[19] < 0
    # Terminating block main.block_44
    cmpq $0, %rcx
    jge main.block_66
    # Phi reg: {(3, 3)} mem: {}
    # Terminating block main.block_45
    jmp main.block_46
main.block_66:
    # Phi reg: {(5, 3)} mem: {}
    movq %rdi, %r11
    # Terminating block main.block_66
main.block_46:
    .loc 0 19 27                       # p5
    # No annotation available for inst store_array global:imageOut[%15] %111
    leaq 303(%r8), %rax
    cmpq $129999, %rax
    ja main.bound_check_fail.r8.303.130000.20
    .set imageOut.303, imageOut + 2424
    movq %r11, imageOut.303(, %r8, 8)
    # No annotation available for inst add %38, %1
    leaq 1(%r10), %r8
    .loc 0 17 12                       # reload 1
    movq $1, %r10
    # Phi reg: {(2, 0), (0, 2)} mem: {}
    xchg %r8, %r10
    # Terminating block main.block_46
    jmp main.block_5
main.block_6:
    # No annotation available for inst load stack_1
    movq 56(%rsp), %r9
    movq 64(%rsp), %r10
    # Phi reg: {(2, 1), (0, 0), (1, 2)} mem: {}
    xchg %r9, %r10
    # Terminating block main.block_6
    jmp main.block_2
main.block_3:
    # Terminating block main.block_3
    .loc 0 132 1
    xorq %rax, %rax
    popq %rbx
    popq %rbp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    addq $24, %rsp
    ret
main.bound_check_fail.r8._1.130000.20:
    movq %r8, %rcx
    addq $-1, %rcx
    movq $20, %rsi
    movq $130000, %rdx
    jmp bounds_check.fail
main.bound_check_fail.r8.303.130000.20:
    movq %r8, %rcx
    addq $303, %rcx
    movq $20, %rsi
    movq $130000, %rdx
bounds_check.fail:
    leaq index_out_of_bounds_msg(%rip), %rdi
    call printf
    movq $-1, %rdi
    call exit