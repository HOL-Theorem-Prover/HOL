signature cheri_stepLib =
sig
   val hex_to_padded_opcode: string -> Term.term

   val cheri_decode: Term.term -> Thm.thm
   val cheri_decode_hex: string -> Thm.thm
   val cheri_dict: (string, Term.term) Redblackmap.dict
   val cheri_step: Term.term -> Thm.thm list
   val cheri_step_hex: string -> Thm.thm list

   val cheri_find_opc: Term.term -> (string * Term.term) list
end
