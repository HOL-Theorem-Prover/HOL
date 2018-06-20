signature x64AssemblerLib =
sig
   val x64_code: string quotation -> string list
   val x64_code_no_spaces: string quotation -> string list
   val x64_disassemble1: string -> string
   val x64_disassemble_string: string -> (string * string) list
   val x64_disassemble_term: Term.term -> (string * string) list
   val print_x64_code: string quotation -> unit
   val print_x64_disassemble: string quotation -> unit
end
