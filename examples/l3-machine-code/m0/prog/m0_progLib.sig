signature m0_progLib =
sig
   val REG_CONV: Conv.conv
   val addInstructionClass: string -> bool
   val get_code: Thm.thm -> Term.term
   val m0_config: bool -> string -> unit
   val m0_introduction: Drule.rule
   val m0_spec: string -> Thm.thm list
   val m0_spec_code: string quotation -> Thm.thm list list
   val m0_spec_hex: string -> Thm.thm list
   val memory_introduction: Drule.rule
   val mk_thumb2_pair: bool -> Term.term -> Term.term
   val register_introduction: Drule.rule
   val set_newline: string -> unit
end
