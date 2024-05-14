my_div:
    subq $8, %rsp
my_div.block_0:     # entry
    movq $12345, %r8
    movq %rdi, %rax
    cqto
    idivq %r8
    movq %rax, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
my_mod:
    subq $8, %rsp
my_mod.block_0:     # entry
    movq $12345, %r8
    movq %rdi, %rax
    cqto
    idivq %r8
    movq %rdx, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
my_div_p2:
    subq $8, %rsp
my_div_p2.block_0:     # entry
    movq $1024, %r8
    movq %rdi, %rax
    cqto
    idivq %r8
    movq %rax, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
my_mod_p2:
    subq $8, %rsp
my_mod_p2.block_0:     # entry
    movq $1024, %r8
    movq %rdi, %rax
    cqto
    idivq %r8
    movq %rdx, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret