(* ===================================================================== *)
(* FILE: mk_res_quan.ml	    DATE: 1 Aug 92	BY: Wai Wong		*)
(* Create the theory res_quan containing all theorems about		*)
(* restricted quantifiers.   	    					*)
(* ===================================================================== *)
structure res_quanScript =
struct


open HolKernel Parse basicHol90Lib;

val _ = new_theory"res_quan";

type thm = Thm.thm
infix THEN THENL;

val RESQ_FORALL = restr_binderTheory.RES_FORALL;
val RESQ_EXISTS = restr_binderTheory.RES_EXISTS;
val RESQ_SELECT = restr_binderTheory.RES_SELECT;
val RESQ_ABSTRACT = restr_binderTheory.RES_ABSTRACT;

val _ = associate_restriction ("\\", "RES_ABSTRACT");
val _ = associate_restriction ("!",  "RES_FORALL");
val _ = associate_restriction ("?",  "RES_EXISTS");
val _ = associate_restriction ("@",  "RES_SELECT");

(* ===================================================================== *)
(* Properties of restricted quantification.                              *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* RESQ_FORALL	    	    	    					*)
(* --------------------------------------------------------------------- *)



val RESQ_FORALL_CONJ_DIST = store_thm("RESQ_FORALL_CONJ_DIST",
    (--`!P Q R.
     (!(i:'a) :: P. (Q i /\ R i)) = (!i :: P. Q i) /\ (!i :: P. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL]
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

val RESQ_FORALL_DISJ_DIST = store_thm("RESQ_FORALL_DISJ_DIST",
    (--`!P Q R.
     (!(i:'a) :: \i. P i \/ Q i. R i) = (!i :: P. R i) /\ (!i :: Q. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

val RESQ_FORALL_UNIQUE = store_thm("RESQ_FORALL_UNIQUE",
    (--`!P j. (!(i:'a) :: ($= j). P i) = P j`--),
    REWRITE_TAC [RESQ_FORALL] THEN BETA_TAC THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
       [DISCH_THEN (fn th =>
             ACCEPT_TAC(MP (SPEC (--`j:'a`--) th) (REFL (--`j:'a`--)) )),
        DISCH_TAC THEN GEN_TAC THEN DISCH_THEN (fn th => SUBST1_TAC (SYM th))
        THEN FIRST_ASSUM ACCEPT_TAC]);

val RESQ_FORALL_FORALL = store_thm("RESQ_FORALL_FORALL",
    (--`!(P:'a->bool) (R:'a->'b->bool) (x:'b).
        (!x. !i :: P. R i x) = (!i :: P. !x. R i x)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL]
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val RESQ_FORALL_REORDER = store_thm("RESQ_FORALL_REORDER",
    (--`!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (!i :: P. !j :: Q. R i j) = (!j :: Q. !i :: P. R i j)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

(* --------------------------------------------------------------------- *)
(* RESQ_EXISTS	    	    	    					*)
(* --------------------------------------------------------------------- *)

val RESQ_EXISTS_DISJ_DIST = store_thm("RESQ_EXISTS_DISJ_DIST",
    (--`!P Q R.
     (?(i:'a) :: P. (Q i \/ R i)) = (?i :: P. Q i) \/ (?i :: P. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_EXISTS]
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[CONJ_SYM]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);

val RESQ_DISJ_EXISTS_DIST = store_thm("RESQ_DISJ_EXISTS_DIST",
    (--`!P Q R.
     (?(i:'a) :: \i. P i \/ Q i. R i) = (?i :: P. R i) \/ (?i :: Q. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_EXISTS]
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);

val RESQ_EXISTS_UNIQUE = store_thm("RESQ_EXISTS_UNIQUE",
    (--`!P j. (?(i:'a) :: ($= j). P i) = P j`--),
    REWRITE_TAC [RESQ_EXISTS] THEN BETA_TAC THEN REPEAT GEN_TAC
    THEN EQ_TAC THENL[
      DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[],
      DISCH_TAC THEN EXISTS_TAC (--`j:'a`--) THEN  ASM_REWRITE_TAC[]]);

val RESQ_EXISTS_REORDER = store_thm("RESQ_EXISTS_REORDER",
    (--`!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (?i :: P. ?j :: Q. R i j) = (?j :: Q. ?i :: P. R i j)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_EXISTS] THEN BETA_TAC
    THEN EQ_TAC THEN DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THENL[
      EXISTS_TAC (--`x':'b`--) THEN CONJ_TAC THENL[
    	ALL_TAC, EXISTS_TAC(--`x:'a`--) THEN CONJ_TAC],
      EXISTS_TAC (--`x':'a`--) THEN CONJ_TAC THENL[
    	ALL_TAC, EXISTS_TAC(--`x:'b`--) THEN CONJ_TAC]]
    THEN FIRST_ASSUM ACCEPT_TAC);


val _ = export_theory();

val _ = let
  val ^^ = Path.concat
  infix ^^
in
  export_theory_as_docfiles (Path.parentArc ^^ "help" ^^ "thms")
end

end;
