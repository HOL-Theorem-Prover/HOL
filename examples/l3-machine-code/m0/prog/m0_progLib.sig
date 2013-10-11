signature m0_progLib =
sig
   val addInstructionClass: string -> bool
   val get_code: Thm.thm -> Term.term
   val mk_thumb2_pair: bool -> Term.term -> Term.term

   val m0_config: bool * bool -> unit
   val m0_spec: string -> Thm.thm list
   val m0_spec_hex: string -> Thm.thm list

   val set_newline: string -> unit
end
