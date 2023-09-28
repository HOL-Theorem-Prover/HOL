open HolKernel Parse boolLib bossLib
open x64_decompLib

val _ = new_theory "x64_decomp_demo";

val (decomp_cert,decomp_def) = x64_decompLib.x64_decompile "decomp" `
  (* 0: *)  55              (* push   %rbp *)
  (* 1: *)  4889E5          (* mov    %rsp,%rbp *)
  (* 4: *)  48897DE8        (* mov    %rdi,-0x18(%rbp) *)
  (* 8: *)  8975E4          (* mov    %esi,-0x1c(%rbp) *)
  (* b: *)  C745F800000000  (* movl   $0x0,-0x8(%rbp) *)
  (* 12: *) EB3B            (* jmp    4f <to_upper+0x4f> *)
  (* 14: *) 8B45F8          (* mov    -0x8(%rbp),%eax *)
  (* 17: *) 4863D0          (* movslq %eax,%rdx *)
  (* 1a: *) 488B45E8        (* mov    -0x18(%rbp),%rax *)
  (* 1e: *) 4801D0          (* add    %rdx,%rax *)
  (* 21: *) 0FB600          (* movzbl (%rax),%eax *)
  (* 24: *) 0FBEC0          (* movsbl %al,%eax *)
  (* 27: *) 8945FC          (* mov    %eax,-0x4(%rbp) *)
  (* 2a: *) 837DFC60        (* cmpl   $0x60,-0x4(%rbp) *)
  (* 2e: *) 7E1B            (* jle    4b <to_upper+0x4b> *)
  (* 30: *) 837DFC7A        (* cmpl   $0x7a,-0x4(%rbp) *)
  (* 34: *) 7F15            (* jg     4b <to_upper+0x4b> *)
  (* 36: *) 8B45F8          (* mov    -0x8(%rbp),%eax *)
  (* 39: *) 4863D0          (* movslq %eax,%rdx *)
  (* 3c: *) 488B45E8        (* mov    -0x18(%rbp),%rax *)
  (* 40: *) 4801C2          (* add    %rax,%rdx *)
  (* 43: *) 8B45FC          (* mov    -0x4(%rbp),%eax *)
  (* 46: *) 83E820          (* sub    $0x20,%eax *)
  (* 49: *) 8802            (* mov    %al,(%rdx) *)
  (* 4b: *) 8345F801        (* addl   $0x1,-0x8(%rbp) *)
  (* 4f: *) 8B45F8          (* mov    -0x8(%rbp),%eax *)
  (* 52: *) 3B45E4          (* cmp    -0x1c(%rbp),%eax *)
  (* 55: *) 7CBD            (* jl     14 <to_upper+0x14> *)
  (* 57: *) 5D              (* pop    %rbp *) `

val _ = save_thm("decomp_cert",decomp_cert);

val () = Feedback.set_trace "x64 spec" 2

val (decomp1_cert,decomp1_def) =
  Feedback.trace ("Theory.allow_rebinds", 1)
     (x64_decompLib.x64_decompile "decomp1")
  ‘
  (*  0: *) 55              (* push   %rbp *)
  (*  1: *) 4889e5          (* mov    %rsp,%rbp *)
  (*  4: *) 4883ec20        (* sub    $0x20,%rsp *)
  (*  8: *) 48897de8        (* mov    %rdi,-0x18(%rbp) *)
  (*  c: *) 488b45e8        (* mov    -0x18(%rbp),%rax *)
  (* 10: *) 488945f8        (* mov    %rax,-0x8(%rbp) *)
  (* 14: *) eb1e            (* jmp    34 <transform+0x34> *)
  (* 16: *) 488b45f8        (* mov    -0x8(%rbp),%rax *)
  (* 1a: *) 0fb600          (* movzbl (%rax),%eax *)
  (* 1d: *) 0fbec0          (* movsbl %al,%eax *)
  (* 20: *) 89c7            (* mov    %eax,%edi *)
            488bc0          (* mov    %rax,%rax *)
            eb00            (* jmp    27 <transform+0x27> *)
  (* 22:    e800000000         callq  27 <transform+0x27> *)
  (* 27: *) 89c2            (* mov    %eax,%edx *)
  (* 29: *) 488b45f8        (* mov    -0x8(%rbp),%rax *)
  (* 2d: *) 8810            (* mov    %dl,(%rax) *)
  (* 2f: *) 488345f801      (* addq   $0x1,-0x8(%rbp) *)
  (* 34: *) 488b45f8        (* mov    -0x8(%rbp),%rax *)
  (* 38: *) 0fb600          (* movzbl (%rax),%eax *)
  (* 3b: *) 84c0            (* test   %al,%al *)
  (* 3d: *) 75d7            (* jne    16 <transform+0x16> *)
  (* 3f: *) 488b45e8        (* mov    -0x18(%rbp),%rax *)
  (* 43: *) c9              (* leaveq  *) ’

val _ = save_thm("decomp1_cert",decomp1_cert);

val _ = export_theory()
