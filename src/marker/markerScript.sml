open HolKernel Parse boolLib

infix THEN ORELSE

val _ = new_theory "marker";

(* stmarker stands for "short term marker"; use this constant to mark
   sub-terms for a short period (within a conversion, say) and be sure
   to remove the marker soon after use. *)
val stmarker_def = new_definition("stmarker_def", ``stmarker (x:'a) = x``);

(* the following move_<dir>_<op> theorems will loop if more than one term
   is marked at the same level *)
val move_left_conj = store_thm(
  "move_left_conj",
  ``!p q m. (p /\ stmarker m = stmarker m /\ p) /\
            ((stmarker m /\ p) /\ q = stmarker m /\ (p /\ q)) /\
            (p /\ (stmarker m /\ q) = stmarker m /\ (p /\ q))``,
  REWRITE_TAC [stmarker_def, CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC CONJ_COMM);

val move_right_conj = store_thm(
  "move_right_conj",
  ``!p q m. (stmarker m /\ p = p /\ stmarker m) /\
            (p /\ (q /\ stmarker m) = (p /\ q) /\ stmarker m) /\
            ((p /\ stmarker m) /\ q = (p /\ q) /\ stmarker m)``,
  REWRITE_TAC [stmarker_def, GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC CONJ_COMM);

val move_left_disj = store_thm(
  "move_left_disj",
  ``!p q m. (p \/ stmarker m = stmarker m \/ p) /\
            ((stmarker m \/ p) \/ q = stmarker m \/ (p \/ q)) /\
            (p \/ (stmarker m \/ q) = stmarker m \/ (p \/ q))``,
  REWRITE_TAC [stmarker_def, DISJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC DISJ_COMM);

val move_right_disj = store_thm(
  "move_right_disj",
  ``!p q m. (stmarker m \/ p = p \/ stmarker m) /\
            (p \/ (q \/ stmarker m) = (p \/ q) \/ stmarker m) /\
            ((p \/ stmarker m) \/ q = (p \/ q) \/ stmarker m)``,
  REWRITE_TAC [stmarker_def, GSYM DISJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  MATCH_ACCEPT_TAC DISJ_COMM);

(* Note, if you want to move a pair of things to the edge of a term,
   you can move one of them, and then the second in two successive
   passes.  Something like
     find_and_move_left THENC RAND_CONV find_and_move_left
   will result in a term
     t1 /\ (t2 /\ ...)
   rewriting with CONJ_ASSOC will even give you
     (t1 /\ t2) /\ ...
*)

val _ = export_theory();

