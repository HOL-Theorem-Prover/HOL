signature x64_decompLib =
sig
   val x64_decompile: string -> Term.term quotation -> Thm.thm * Thm.thm
   val x64_decompile_code: string -> string quotation -> Thm.thm * Thm.thm
end
