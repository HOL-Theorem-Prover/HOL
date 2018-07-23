structure syntaxLib :> syntaxLib =
struct

open HolKernel boolLib bossLib Parse;
open GraphLangTheory

val dest1 = #3 o HolKernel.syntax_fns1 "GraphLang"
val dest3 = #3 o HolKernel.syntax_fns3 "GraphLang"

val dest_IMPL_INST = dest3 "IMPL_INST"
val dest_Inst = dest3 "Inst"
val dest_IF = dest3 "IF"
val dest_ASM = dest3 "ASM"
val dest_Jump = dest1 "Jump"

end
