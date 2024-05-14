my_div:
    subq $8, %rsp
my_div.block_0:     # entry
    movabsq $-6205696892516465602, %rax
    imulq %rdi
    addq %rdi, %rdx
    sarq $13, %rdx
    movq %rdi, %r8
    shrq $63, %r8
    addq %rdx, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
my_mod:
    subq $8, %rsp
my_mod.block_0:     # entry
    movabsq $-6205696892516465602, %rax
    imulq %rdi
    addq %rdi, %rdx
    sarq $13, %rdx
    movq %rdi, %r8
    shrq $63, %r8
    addq %rdx, %r8
    imulq $12345, %r8, %rdx
    movq %rdi, %r8
    subq %rdx, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
my_div_p2:
    subq $8, %rsp
my_div_p2.block_0:     # entry
    movq %rdi, %r8
    sarq $10, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
my_mod_p2:
    subq $8, %rsp
my_mod_p2.block_0:     # entry
    movq %rdi, %r8
    andq $1023, %r8
    movq %r8, %rax
    addq $8, %rsp
    ret
