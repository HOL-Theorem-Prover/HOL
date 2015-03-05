signature x64_decompLib =
sig
   val x64_decompile: string -> string quotation -> Thm.thm * Thm.thm
   val x64_decompile_code: string -> string quotation -> Thm.thm * Thm.thm
end
