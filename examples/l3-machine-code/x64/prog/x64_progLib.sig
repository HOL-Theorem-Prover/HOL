signature x64_progLib =
sig
   val x64_spec: string -> Thm.thm
   val x64_spec_code: string quotation -> Thm.thm list
   val x64_spec_trace: (string -> unit) option ref
end
