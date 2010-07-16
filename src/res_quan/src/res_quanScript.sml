(* =====================================================================
    FILE: mk_res_quan.ml	    DATE: 1 Aug 92
    BY: Wai Wong
    CHANGED BY: Joe Hurd, June 2001 (to use predicate sets)
    CHANGED BY: Joe Hurd, June 2001 (to remove the ARB from RES_ABSTRACT)
    CHANGED BY: Joe Hurd, October 2001 (moved definitions to boolTheory)

    Create the theory res_quan containing all theorems about
    restricted quantifiers.
 ===================================================================== *)

(* interactive use
app load ["combinTheory", "pred_setTheory", "BasicProvers"];
*)

(* non-interactive use
*)
structure res_quanScript =
struct

open HolKernel Parse boolLib combinTheory pred_setTheory BasicProvers;

val _ = new_theory "res_quan";

type thm = Thm.thm
infix THEN THENL;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* --------------------------------------------------------------------- *)
(* Definitions to support restricted abstractions and quantifications    *)
(* --------------------------------------------------------------------- *)

(* JEH: Defns moved to boolTheory: the following versions remove lambdas *)

val RES_FORALL = save_thm("RES_FORALL", RES_FORALL_THM)
val RES_EXISTS = save_thm("RES_EXISTS", RES_EXISTS_THM)
val RES_EXISTS_UNIQUE = save_thm("RES_EXISTS_UNIQUE", RES_EXISTS_UNIQUE_THM)
val RES_SELECT = save_thm("RES_SELECT", RES_SELECT_THM)

val RES_ABSTRACT = save_thm ("RES_ABSTRACT", RES_ABSTRACT_DEF);

(* ===================================================================== *)
(* Properties of restricted quantification.                              *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* RES_FORALL	    	    	    					*)
(* --------------------------------------------------------------------- *)

val RES_FORALL_CONJ_DIST = store_thm("RES_FORALL_CONJ_DIST",
    (--`!P Q R.
     (!(i:'a) :: P. (Q i /\ R i)) = (!i :: P. Q i) /\ (!i :: P. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL]
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

val RES_FORALL_DISJ_DIST = store_thm("RES_FORALL_DISJ_DIST",
    (--`!P Q R.
     (!(i:'a) :: \j. P j \/ Q j. R i) = (!i :: P. R i) /\ (!i :: Q. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL, SPECIFICATION] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

val RES_FORALL_UNIQUE = store_thm("RES_FORALL_UNIQUE",
    (--`!P j. (!(i:'a) :: ($= j). P i) = P j`--),
    REWRITE_TAC [RES_FORALL, SPECIFICATION] THEN BETA_TAC THEN
    PROVE_TAC []);

val RES_FORALL_FORALL = store_thm("RES_FORALL_FORALL",
    (--`!(P:'a->bool) (R:'a->'b->bool) (x:'b).
        (!x. !i :: P. R i x) = (!i :: P. !x. R i x)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL, SPECIFICATION]
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val RES_FORALL_REORDER = store_thm("RES_FORALL_REORDER",
    (--`!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (!i :: P. !j :: Q. R i j) = (!j :: Q. !i :: P. R i j)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_FORALL, SPECIFICATION] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

val RES_FORALL_EMPTY = store_thm
  ("RES_FORALL_EMPTY",
   ``!(p : 'a -> bool). RES_FORALL {} p``,
   RW_TAC bool_ss [RES_FORALL, NOT_IN_EMPTY]);

val RES_FORALL_UNIV = store_thm
  ("RES_FORALL_UNIV",
   ``!(p : 'a -> bool). RES_FORALL UNIV p = $! p``,
   RW_TAC bool_ss [RES_FORALL, IN_UNIV, ETA_AX]);

val RES_FORALL_NULL = store_thm
  ("RES_FORALL_NULL",
   ``!(p : 'a -> bool) m. RES_FORALL p (\x. m) = ((p = {}) \/ m)``,
   RW_TAC bool_ss [RES_FORALL, EXTENSION, NOT_IN_EMPTY]
   THEN Cases_on `m`
   THEN PROVE_TAC []);

(* --------------------------------------------------------------------- *)
(* RES_EXISTS	    	    	    					*)
(* --------------------------------------------------------------------- *)

val RES_EXISTS_DISJ_DIST = store_thm("RES_EXISTS_DISJ_DIST",
    (--`!P Q R.
     (?(i:'a) :: P. (Q i \/ R i)) = (?i :: P. Q i) \/ (?i :: P. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_EXISTS, SPECIFICATION]
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[CONJ_SYM]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);

val RES_DISJ_EXISTS_DIST = store_thm("RES_DISJ_EXISTS_DIST",
    (--`!P Q R.
     (?(i:'a) :: \i. P i \/ Q i. R i) = (?i :: P. R i) \/ (?i :: Q. R i)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_EXISTS, SPECIFICATION]
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);

val RES_EXISTS_EQUAL = store_thm("RES_EXISTS_EQUAL",
    (--`!P j. (?(i:'a) :: ($= j). P i) = P j`--),
    REWRITE_TAC [RES_EXISTS, SPECIFICATION] THEN BETA_TAC THEN REPEAT GEN_TAC
    THEN EQ_TAC THENL[
      DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[],
      DISCH_TAC THEN EXISTS_TAC (--`j:'a`--) THEN  ASM_REWRITE_TAC[]]);

val RES_EXISTS_REORDER = store_thm("RES_EXISTS_REORDER",
    (--`!(P:'a->bool) (Q:'b->bool) (R:'a->'b->bool).
        (?i :: P. ?j :: Q. R i j) = (?j :: Q. ?i :: P. R i j)`--),
    REPEAT STRIP_TAC THEN REWRITE_TAC [RES_EXISTS, SPECIFICATION] THEN BETA_TAC
    THEN EQ_TAC THEN DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THENL[
      EXISTS_TAC (--`x':'b`--) THEN CONJ_TAC THENL[
    	ALL_TAC, EXISTS_TAC(--`x:'a`--) THEN CONJ_TAC],
      EXISTS_TAC (--`x':'a`--) THEN CONJ_TAC THENL[
    	ALL_TAC, EXISTS_TAC(--`x:'b`--) THEN CONJ_TAC]]
    THEN FIRST_ASSUM ACCEPT_TAC);

val RES_EXISTS_EMPTY = store_thm
  ("RES_EXISTS_EMPTY",
   ``!(p : 'a -> bool). ~RES_EXISTS {} p``,
   RW_TAC bool_ss [RES_EXISTS, NOT_IN_EMPTY]);

val RES_EXISTS_UNIV = store_thm
  ("RES_EXISTS_UNIV",
   ``!(p : 'a -> bool). RES_EXISTS UNIV p = $? p``,
   RW_TAC bool_ss [RES_EXISTS, IN_UNIV, ETA_AX]);

val RES_EXISTS_NULL = store_thm
  ("RES_EXISTS_NULL",
   ``!(p : 'a -> bool) m. RES_EXISTS p (\x. m) = (~(p = {}) /\ m)``,
   RW_TAC bool_ss [RES_EXISTS, EXTENSION, NOT_IN_EMPTY]
   THEN Cases_on `m`
   THEN PROVE_TAC []);

val RES_EXISTS_ALT = store_thm
  ("RES_EXISTS_ALT",
   ``!(p : 'a -> bool) m.
       RES_EXISTS p m = (RES_SELECT p m) IN p /\ m (RES_SELECT p m)``,
   RW_TAC bool_ss [RES_EXISTS, EXISTS_DEF, RES_SELECT, SPECIFICATION]);

(* --------------------------------------------------------------------- *)
(* RES_EXISTS_UNIQUE                                                     *)
(* --------------------------------------------------------------------- *)

val RES_EXISTS_UNIQUE_EMPTY = store_thm
  ("RES_EXISTS_UNIQUE_EMPTY",
   ``!(p : 'a -> bool). ~RES_EXISTS_UNIQUE {} p``,
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_EMPTY, NOT_IN_EMPTY]);

val RES_EXISTS_UNIQUE_UNIV = store_thm
  ("RES_EXISTS_UNIQUE_UNIV",
   ``!(p : 'a -> bool). RES_EXISTS_UNIQUE UNIV p = $?! p``,
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_UNIV, IN_UNIV,
                   RES_FORALL_UNIV, EXISTS_UNIQUE_DEF]
   ++ KNOW_TAC ``$? (p:'a->bool) = ?x. p x`` >> RW_TAC bool_ss [ETA_AX]
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   ++ PROVE_TAC []);

val RES_EXISTS_UNIQUE_NULL = store_thm
  ("RES_EXISTS_UNIQUE_NULL",
   ``!(p : 'a -> bool) m. RES_EXISTS_UNIQUE p (\x. m) = ((?x. p = {x}) /\ m)``,
   RW_TAC bool_ss [RES_EXISTS_UNIQUE, RES_EXISTS_NULL, NOT_IN_EMPTY,
                   RES_FORALL_NULL, EXISTS_UNIQUE_DEF, EXTENSION, IN_SING]
   ++ RW_TAC bool_ss [RES_EXISTS, RES_FORALL]
   ++ Cases_on `m`
   ++ PROVE_TAC []);

val RES_EXISTS_UNIQUE_ALT = store_thm
  ("RES_EXISTS_UNIQUE_ALT",
   ``!(p : 'a -> bool) m.
       RES_EXISTS_UNIQUE p m = (?x :: p. m x /\ !y :: p. m y ==> (y = x))``,
   RW_TAC bool_ss [SPECIFICATION, RES_EXISTS_UNIQUE, RES_EXISTS, RES_FORALL]
   THEN PROVE_TAC []);

(* --------------------------------------------------------------------- *)
(* RES_SELECT                                                            *)
(* --------------------------------------------------------------------- *)

val RES_SELECT_EMPTY = store_thm
  ("RES_SELECT_EMPTY",
   ``!(p : 'a -> bool). RES_SELECT {} p = @x. F``,
   RW_TAC bool_ss [RES_SELECT, NOT_IN_EMPTY, ETA_AX]);

val RES_SELECT_UNIV = store_thm
  ("RES_SELECT_UNIV",
   ``!(p : 'a -> bool). RES_SELECT UNIV p = $@ p``,
   RW_TAC bool_ss [RES_SELECT, IN_UNIV, ETA_AX]);

(* --------------------------------------------------------------------- *)
(* RES_ABSTRACT                                                          *)
(* --------------------------------------------------------------------- *)

val RES_ABSTRACT =
  save_thm ("RES_ABSTRACT", CONJUNCT1 RES_ABSTRACT_DEF);

val RES_ABSTRACT_EQUAL =
  save_thm ("RES_ABSTRACT_EQUAL", CONJUNCT2 RES_ABSTRACT_DEF);

val RES_ABSTRACT_IDEMPOT = store_thm
  ("RES_ABSTRACT_IDEMPOT",
   ``!p m. RES_ABSTRACT p (RES_ABSTRACT p m) = RES_ABSTRACT p m``,
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC RES_ABSTRACT_EQUAL
   THEN RW_TAC bool_ss [RES_ABSTRACT]);

(* Sanity check for RES_ABSTRACT definition suggested by Lockwood Morris *)
val RES_ABSTRACT_EQUAL_EQ = store_thm
  ("RES_ABSTRACT_EQUAL_EQ",
   ``!p m1 m2.
       (RES_ABSTRACT p m1 = RES_ABSTRACT p m2) =
       (!x. x IN p ==> (m1 x = m2 x))``,
   REPEAT STRIP_TAC
   THEN EQ_TAC THENL
   [PROVE_TAC [RES_ABSTRACT],
    PROVE_TAC [RES_ABSTRACT_EQUAL]]);

val _ = export_theory();

val _ = let
  val ^^ = Path.concat
  infix ^^
in
  export_theory_as_docfiles (Path.parentArc ^^ "help" ^^ "thms")
end

end;
