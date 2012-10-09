	.text
	.align 4,0x90
.globl _asm_exec
.globl asm_exec
_asm_exec:
asm_exec:

	/* push regs onto stack */

	pushq	%rbp
	movq	%rsp, %rbp
	pushq	%rax
	pushq	%rbx
	pushq	%rcx
	pushq	%rdx
	pushq	%rsi
	pushq	%rdi
	pushq	%r8
	pushq	%r9
	pushq	%r10
	pushq	%r11
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15

        /* now %rdi holds pointer to exp_stack */

        /* store %rsp in %rbp */

        movq    %rsp, %rbp

        /* set %rsi to the number of repetitions to be done */

        movq    16(%rdi), %rsi

        /* set %r8 to 0 and %r9 to 2 */

        movq    $0, %r8
        movq    $2, %r9

STARTAGAIN:

        /* reset %rsp from %rbp */

        movq    %rbp, %rsp

        /* set %rax to 0 and set %r15 to hold pointer to heap */

        xorq    %rax,%rax
        movq    0(%rdi), %r15

        /* do stuff to the stack and add stuff to the heap */

	.include "generated_asm.s"

        /* check whether this needs to be repeated */

        subq    $1, %rsi
        jne STARTAGAIN

        /* store %rax onto stack */

        pushq   %rax

        /* calculate number of elements added to heap */

        movq    %r15, %rbx
        movq    0(%rdi), %rax
        subq    %rax, %rbx
        shrq    $3,%rbx
        movq    %rbx, 0(%rdi)   /* exp_stack[0] */

        /* calculate number of elements pushed onto stack */

        movq    %rsp, %rax
        movq    %rbp, %rbx
        subq    %rax, %rbx
        shrq    $3,%rbx
        subq    $1,%rbx
        movq    %rbx, 8(%rdi)   /* exp_stack[1] */

        /* copy those elements into exp_stack[2..] */

        leaq    16(%rdi),%rcx
L1:     cmpq    $0,%rbx
        je L2
        popq    %rdx
        movq    %rdx,0(%rcx)
        addq    $8,%rcx
        subq    $1,%rbx
        jmp L1
L2:

        /* restore %rsp from %rbp */

        movq    %rbp, %rsp

        /* pop regs off stack */

	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%r11
	popq	%r10
	popq	%r9
	popq	%r8
	popq	%rdi
	popq	%rsi
	popq	%rdx
	popq	%rcx
	popq	%rbx
	popq	%rax
	popq	%rbp
	retq
