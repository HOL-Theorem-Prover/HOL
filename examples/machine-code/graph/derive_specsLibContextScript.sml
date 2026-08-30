Theory derive_specsLibContext[bare]
Ancestors
  words
Libs
  HolKernel Parse boolLib bossLib wordsLib

(* ------------------------------------------------------------------------- *)
(* Lemmas derive_specsLib.sml formerly proved as it loaded.  A library is     *)
(* loaded before its client's new_theory, so there was no current theory to   *)
(* prove against; proving them in a theory of their own removes that.  The    *)
(* library keeps the instantiation it applies afterwards.                     *)
(* ------------------------------------------------------------------------- *)

Theorem fix_sub_word64:
  (n2w n + w = if n < dimword (:'a) DIV 2 then n2w n + (w:'a word)
               else w - n2w (dimword (:'a) - n MOD dimword (:'a))) /\
  (w + n2w n = if n < dimword (:'a) DIV 2 then w + n2w n
               else w - n2w (dimword (:'a) - n MOD dimword (:'a)))
Proof
  simp [Once WORD_ADD_COMM] \\ rw []
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM WORD_NEG_NEG]))
  \\ rewrite_tac [WORD_EQ_NEG, word_2comp_n2w]
QED
