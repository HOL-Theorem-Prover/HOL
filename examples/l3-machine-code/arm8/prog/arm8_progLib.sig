signature arm8_progLib =
sig
   val arm8_config: string -> unit
   val arm8_spec: string -> Thm.thm list
   val arm8_spec_code: string quotation -> Thm.thm list list
   val arm8_spec_hex: string -> Thm.thm list
end
