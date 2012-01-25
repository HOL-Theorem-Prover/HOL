	.text
	.align 4,0x90
.globl _jit_exec
.globl jit_exec
_jit_exec:
jit_exec:

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

	/* store pointer to error function in exp_stack, do this by call-then-popq */

	call skip_error
	movq 	%rbp,%rsp
	popq 	%rbp
#ifdef __linux__
        jmp	report_error
#else
        jmp	_report_error
#endif
skip_error:
	popq	%rax
	movq 	%rax,56(%rdi)

	/* store pointer to print function in exp_stack, do this by call-then-popq */

	call 	skip_print
	pushq 	%rax
	pushq 	%rbx
	pushq 	%rcx
	pushq 	%rdx
	pushq 	%rsi
	pushq 	%rdi
	pushq 	%rbp
	pushq 	%r8
	pushq 	%r9
	pushq 	%r10
	pushq 	%r11
	pushq 	%r12
	pushq 	%r13
	pushq 	%r14
	pushq 	%r15
	movq	%rax,%rdi /* arg1 */
	movq	%r14,%rsi /* arg2 */
	movq	%r15,%rdx /* arg3 */
	movq	%rbx,%rcx /* arg4 */
#ifdef __linux__
        call	print_str
#else
        call	_print_str
#endif
	popq 	%r15
	popq 	%r14
	popq 	%r13
	popq 	%r12
	popq 	%r11
	popq 	%r10
	popq 	%r9
	popq 	%r8
	popq 	%rbp
	popq 	%rdi
	popq 	%rsi
	popq 	%rdx
	popq 	%rcx
	popq 	%rbx
	popq 	%rax
        retq
skip_print:
	popq	%rax
	movq 	%rax,64(%rdi)

	/* store pointer to read_line function in exp_stack, do this by call-then-popq */

	call 	skip_read_line
	pushq 	%rax
	pushq 	%rbx
	pushq 	%rcx
	pushq 	%rdx
	pushq 	%rsi
	pushq 	%rdi
	pushq 	%rbp
	pushq 	%r8
	pushq 	%r9
	pushq 	%r10
	pushq 	%r11
	pushq 	%r12
	pushq 	%r13
	pushq 	%r14
	pushq 	%r15
	movq	%rax,%rdi
#ifdef __linux__
        call	read_line
#else
        call	_read_line
#endif
	movq	%rax,%rcx
	popq 	%r15
	popq 	%r14
	popq 	%r13
	popq 	%r12
	popq 	%r11
	popq 	%r10
	popq 	%r9
	popq 	%r8
	popq 	%rbp
	popq 	%rdi
	popq 	%rsi
	popq 	%rdx
	popq 	%rbx  /* not a mistake, rcx is not written since the result is stored there. */
	popq 	%rbx
	popq 	%rax
        retq
skip_read_line:
	popq	%rax
	movq 	%rax,72(%rdi)

	/* store pointer to stats function in exp_stack, do this by call-then-popq */

	call 	skip_stats
	pushq 	%rax
	pushq 	%rbx
	pushq 	%rcx
	pushq 	%rdx
	pushq 	%rsi
	pushq 	%rdi
	pushq 	%rbp
	pushq 	%r8
	pushq 	%r9
	pushq 	%r10
	pushq 	%r11
	pushq 	%r12
	pushq 	%r13
	pushq 	%r14
	pushq 	%r15
#ifdef __linux__
        call	print_stats
#else
        call	_print_stats
#endif
	popq 	%r15
	popq 	%r14
	popq 	%r13
	popq 	%r12
	popq 	%r11
	popq 	%r10
	popq 	%r9
	popq 	%r8
	popq 	%rbp
	popq 	%rdi
	popq 	%rsi
	popq 	%rdx
	popq 	%rcx
	popq 	%rbx
	popq 	%rax
        retq
skip_stats:
	popq	%rax
	movq 	%rax,80(%rdi)

	/* execute verified code */

	.include "verified_code.s"

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
