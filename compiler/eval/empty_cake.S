#### Preprocessor to get around Mac OS and Linux differences in naming

#if defined(__APPLE__)
# define cdecl(s) _##s
#else
# define cdecl(s) s
#endif

        .file	"cake.S"

#### Data section -- modify the numbers to change stack/heap size

	.bss
	.align	16
cake_heap:
	.space	80 * 1024 * 1024   # heap size in bytes
	.align	16
cake_stack:
	.space	20 * 1024 * 1024   # stack size in bytes
	.align	16
cake_end:

#### Start up code

        .text
	.globl	cdecl(main)
cdecl(main):
	pushq	%rbp        # push base pointer
	movq	%rsp, %rbp  # save stack pointer
	leaq	cake_main(%rip), %rdi   # arg1: entry address
	leaq	cake_heap(%rip), %rsi   # arg2: first address of heap
	leaq	cake_stack(%rip), %rdx  # arg3: first address of stack
	leaq	cake_end(%rip), %rcx    # arg4: first address past the stack
	jmp 	cake_main

#### CakeML FFI interface (each block is 8 bytes long)

        .align	8, 0x90

cake_ffiisEof:
	pushq	%r15
	jmp	cdecl(ffiisEof)
	.align	8, 0x90

cake_fficlose:
	pushq	%r15
	jmp	cdecl(fficlose)
	.align	8, 0x90

cake_ffifgetc:
	pushq	%r15
	jmp	cdecl(ffifgetc)
	.align	8, 0x90        

cake_ffiiopen:
	pushq	%r15
	jmp	cdecl(ffiopen)
	.align	8, 0x90

cake_ffiwrite:
	pushq	%r15
	jmp	cdecl(ffiwrite)
	.align	8, 0x90

cake_clear:
	callq	cdecl(exit)
	.align	8, 0x90

cake_exit:
	callq	cdecl(exit)
	.align	8, 0x90

cake_main:

#### Verified code follows
