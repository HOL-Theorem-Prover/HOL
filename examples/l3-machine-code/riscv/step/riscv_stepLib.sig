signature riscv_stepLib =
sig
   val hex_to_padded_opcode: string -> Term.term
   val riscv_decode: Term.term -> Thm.thm
   val riscv_decode_hex: string -> Thm.thm
   val riscv_step: Term.term -> Thm.thm
   val riscv_step_hex: string -> Thm.thm
   val riscv_dict: (string * Term.term) list
end
