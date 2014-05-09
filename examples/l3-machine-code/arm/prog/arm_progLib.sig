signature arm_progLib =
sig
   val addInstructionClass: string -> unit

   val arm_config: string -> string -> unit
   val arm_spec: string -> Thm.thm list
   val arm_spec_code: string quotation -> Thm.thm list list
   val arm_spec_hex: string -> Thm.thm list

   val change_config_rule: Drule.rule

   val set_newline: string -> unit
end
