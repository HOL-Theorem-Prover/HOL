signature arm8_stepLib =
sig
   val arm8_decode: Term.term -> Thm.thm
   val arm8_decode_hex: string -> Thm.thm
   val arm8_decode_instruction: string -> Thm.thm
   val arm8_instruction: Term.term -> string option
   val arm8_names: string list
   val arm8_pattern: string -> Term.term option
   val arm8_step: Term.term -> Thm.thm list
   val arm8_step_code: string quotation -> Thm.thm list list
   val arm8_step_hex: string -> Thm.thm list

   val ARM8_CONV: Conv.conv
   val DATATYPE_CONV: Conv.conv
   val REG_31_RULE: Drule.rule
end
