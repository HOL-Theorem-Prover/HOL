(* HolRefute by case study: a context-free grammar, adapted from Isabelle's
   Manual_Nits.thy section 3.1. *)

Theory refuteGrammar
Ancestors
  list
Libs
  Refute

Datatype:
  letter = La | Lb
End

Inductive S1:
  S1 [] /\
  (!w. A1 w ==> S1 (Lb :: w)) /\
  (!w. B1 w ==> S1 (La :: w)) /\
  (!w. S1 w ==> A1 (La :: w)) /\
  (!w. S1 w ==> S1 (Lb :: w)) /\
  (!v w. B1 v /\ B1 v ==> B1 (La :: v ++ w))
End

(* The diagnostic tactic is followed by cheat in deliberately false
   conjectures so that the counterexample remains visible in the build. *)

Theorem every_word_of_the_first_grammar_is_balanced:
  S1 w ==>
  LENGTH (FILTER (\x. x = La) w) =
  LENGTH (FILTER (\x. x = Lb) w)
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Inductive S2:
  S2 [] /\
  (!w. A2 w ==> S2 (Lb :: w)) /\
  (!w. B2 w ==> S2 (La :: w)) /\
  (!w. S2 w ==> A2 (La :: w)) /\
  (!w. S2 w ==> B2 (Lb :: w)) /\
  (!v w. B2 v /\ B2 v ==> B2 (La :: v ++ w))
End

Theorem every_word_of_the_second_grammar_is_balanced:
  S2 w ==>
  LENGTH (FILTER (\x. x = La) w) =
  LENGTH (FILTER (\x. x = Lb) w)
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Inductive S3:
  S3 [] /\
  (!w. A3 w ==> S3 (Lb :: w)) /\
  (!w. B3 w ==> S3 (La :: w)) /\
  (!w. S3 w ==> A3 (La :: w)) /\
  (!w. S3 w ==> B3 (Lb :: w)) /\
  (!v w. B3 v /\ B3 w ==> B3 (La :: v ++ w))
End

Theorem every_balanced_word_is_in_the_third_grammar:
  LENGTH (FILTER (\x. x = La) w) =
  LENGTH (FILTER (\x. x = Lb) w) ==>
  S3 w
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Inductive S4:
  S4 [] /\
  (!w. A4 w ==> S4 (Lb :: w)) /\
  (!w. B4 w ==> S4 (La :: w)) /\
  (!w. S4 w ==> A4 (La :: w)) /\
  (!v w. A4 v /\ A4 w ==> A4 (Lb :: v ++ w)) /\
  (!w. S4 w ==> B4 (Lb :: w)) /\
  (!v w. B4 v /\ B4 w ==> B4 (La :: v ++ w))
End

(* The corrected grammar yields no counterexample.  The diagnostic leaves
   the goal unchanged, and mutual rule induction then proves soundness. *)

Theorem the_fourth_grammar_is_sound:
  (!w. S4 w ==>
       LENGTH (FILTER (\x. x = La) w) =
       LENGTH (FILTER (\x. x = Lb) w)) /\
  (!w. A4 w ==>
       LENGTH (FILTER (\x. x = La) w) =
       LENGTH (FILTER (\x. x = Lb) w) + 1) /\
  (!w. B4 w ==>
       LENGTH (FILTER (\x. x = Lb) w) =
       LENGTH (FILTER (\x. x = La) w) + 1)
Proof
  MODEL_REFUTE_TAC >>
  ho_match_mp_tac S4_ind >>
  rw [FILTER_APPEND_DISTRIB, LENGTH_APPEND]
QED
