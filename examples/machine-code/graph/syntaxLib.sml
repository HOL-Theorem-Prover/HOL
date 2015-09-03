structure syntaxLib =
struct

open HolKernel boolLib bossLib Parse;
open listTheory wordsTheory pred_setTheory arithmeticTheory wordsLib pairTheory;
open set_sepTheory progTheory helperLib addressTheory combinTheory;

(* generic functions *)

fun dest1 name pat = fn tm =>
  if can (match_term pat) tm then
    rand tm
  else failwith (name ^ " expects " ^ term_to_string pat)

fun dest2 name pat = fn tm =>
  if can (match_term pat) tm then
    (rand (rator tm), rand tm)
  else failwith (name ^ " expects " ^ term_to_string pat)

fun dest3 name pat = fn tm =>
  if can (match_term pat) tm then
    (rand (rator (rator tm)), rand (rator tm), rand tm)
  else failwith (name ^ " expects " ^ term_to_string pat)

(* specific functions *)

val dest_IMPL_INST = dest3 "dest_IMPL_INST" ``IMPL_INST code locs next``
val dest_Inst = dest3 "dest_Inst" ``Inst loc assert next``
val dest_IF = dest3 "dest_IF" ``IF g next1 next2``
val dest_ASM = dest3 "dest_ASM" ``ASM side update jump``
val dest_Jump = dest1 "dest_Jump" ``Jump w``

end
