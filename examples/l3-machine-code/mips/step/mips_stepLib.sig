signature mips_stepLib =
sig
   val hex_to_padded_opcode: string -> Term.term

   val mips_decode: Term.term -> Thm.thm
   val mips_decode_hex: string -> Thm.thm
   val mips_dict: (string, Term.term) Redblackmap.dict
   val mips_eval: bool -> Term.term -> Thm.thm list
   val mips_eval_hex: bool -> string -> Thm.thm list
   val mips_step_code: bool -> string -> Thm.thm list

   val mips_find_opc: Term.term -> (string * Term.term) list
end
