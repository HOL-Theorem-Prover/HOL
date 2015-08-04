signature x64_stepLib =
sig
   val x64_CONV: Conv.conv
   val x64_step: Term.term list -> Thm.thm
   val x64_step_hex: string -> Thm.thm
   val x64_step_code: string quotation -> Thm.thm list
   val x64_decode: Term.term list -> Thm.thm
   val x64_decode_hex: string -> Thm.thm
   val x64_decode_code: string quotation -> Thm.thm list
end
