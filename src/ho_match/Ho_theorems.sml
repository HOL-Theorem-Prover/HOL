(* =====================================================================
 * FILE : $Id$
 *
 * ===================================================================== *)


structure Ho_theorems :> Ho_theorems =
struct

open HolKernel Parse basicHol90Lib liteLib Ho_rewrite Ho_resolve;

infix 5 |->
infix THEN ORELSE THENL;

type thm = Thm.thm

val ETA_AX            = boolTheory.ETA_AX;
val EXISTS_DEF        = boolTheory.EXISTS_DEF;
val EXISTS_UNIQUE_DEF = boolTheory.EXISTS_UNIQUE_DEF;

val BETA_THM          = boolTheory.BETA_THM
val ABS_SIMP          = boolTheory.ABS_SIMP;


(* ------------------------------------------------------------------------- *)
(* Start building up the basic rewrites; we add a few more later.            *)
(* ------------------------------------------------------------------------- *)

val _ = add_implicit_rewrites
  [REFL_CLAUSE,
   EQ_CLAUSES,
   NOT_CLAUSES,
   AND_CLAUSES,
   OR_CLAUSES,
   IMP_CLAUSES,
   FORALL_SIMP,
   EXISTS_SIMP,
   ABS_SIMP];;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for unique existence.                                        *)
(* ------------------------------------------------------------------------- *)
val EXISTS_UNIQUE_THM = prove
 ((--`!P. (?!x:'a. P x) = (?x. P x) /\ (!x x'. P x /\ P x' ==> (x = x'))`--),
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_DEF, BETA_THM]);;

(* ------------------------------------------------------------------------- *)
(* Trivial instances of existence.                                           *)
(* ------------------------------------------------------------------------- *)

val EXISTS_REFL = prove
 ((--`!a:'a. ?x. x = a`--),
  GEN_TAC THEN EXISTS_TAC (--`a:'a`--) THEN REFL_TAC);;

val EXISTS_UNIQUE_REFL = prove
 ((--`!a:'a. ?!x. x = a`--),
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REPEAT(EQ_TAC ORELSE STRIP_TAC) THENL
   [EXISTS_TAC (--`a:'a`--), ASM_REWRITE_TAC[]] THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Alternative version of unique existence.                                  *)
(* ------------------------------------------------------------------------- *)

val EXISTS_UNIQUE_ALT = prove
 ((--`!P:'a->bool. (?!x. P x) = (?x. !y. P y = (x = y))`--),
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC (--`x:'a`--)) ASSUME_TAC) THEN
    EXISTS_TAC (--`x:'a`--) THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_ACCEPT_TAC],
    DISCH_THEN(X_CHOOSE_TAC (--`x:'a`--)) THEN
    ASM_REWRITE_TAC[GSYM EXISTS_REFL] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)

val UNWIND_THM1 = prove
 ((--`!P (a:'a). (?x. (a = x) /\ P x) = P a`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)),
    DISCH_TAC THEN EXISTS_TAC (--`a:'a`--) THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
    REFL_TAC]);;

val UNWIND_THM2 = prove
 ((--`!P (a:'a). (?x. (x = a) /\ P x) = P a`--),
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC UNWIND_THM1);;

val UNWIND_FORALL_THM1 =
prove((--`!f (v:'a). (!x. (v = x) ==> f x) = f v`--),
 REPEAT STRIP_TAC THEN EQ_TAC THENL
 [DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [],
  DISCH_TAC THEN GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]
 );

val UNWIND_FORALL_THM2 =
prove((--`!f (v:'a). (!x. (x = v) ==> f x) = f v`--),
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
    THENL [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [], ASM_REWRITE_TAC []]
);

(* ------------------------------------------------------------------------- *)
(* Permuting quantifiers.                                                    *)
(* ------------------------------------------------------------------------- *)

val SWAP_FORALL_THM = prove
 ((--`!P:'a->'b->bool. (!x y. P x y) = (!y x. P x y)`--),
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

val SWAP_EXISTS_THM = prove
 ((--`!P:'a->'b->bool. (?x y. P x y) = (?y x. P x y)`--),
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [MAP_EVERY EXISTS_TAC [(--`y:'b`--), (--`x:'a`--)],
    MAP_EVERY EXISTS_TAC [(--`x:'a`--), (--`y:'b`--)]] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;


(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)

val FORALL_AND_THM       = boolTheory.FORALL_AND_THM;
val AND_FORALL_THM       = GSYM FORALL_AND_THM;
val LEFT_AND_FORALL_THM  = boolTheory.LEFT_AND_FORALL_THM;
val RIGHT_AND_FORALL_THM = boolTheory.RIGHT_AND_FORALL_THM


(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)

val EXISTS_OR_THM = boolTheory.EXISTS_OR_THM;
val OR_EXISTS_THM = GSYM EXISTS_OR_THM;

val LEFT_OR_EXISTS_THM  = boolTheory.LEFT_OR_EXISTS_THM
val RIGHT_OR_EXISTS_THM = boolTheory.RIGHT_OR_EXISTS_THM

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_AND_THM  = boolTheory.LEFT_EXISTS_AND_THM;
val RIGHT_EXISTS_AND_THM = boolTheory.RIGHT_EXISTS_AND_THM;
val TRIV_EXISTS_AND_THM  = boolTheory.BOTH_EXISTS_AND_THM;

val LEFT_AND_EXISTS_THM  = GSYM LEFT_EXISTS_AND_THM;
val RIGHT_AND_EXISTS_THM = GSYM RIGHT_EXISTS_AND_THM;
val TRIV_AND_EXISTS_THM  = GSYM TRIV_EXISTS_AND_THM

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)

val TRIV_FORALL_OR_THM = boolTheory.BOTH_FORALL_OR_THM;
val TRIV_OR_FORALL_THM = GSYM TRIV_FORALL_OR_THM;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

val RIGHT_IMP_FORALL_THM = GSYM boolTheory.RIGHT_FORALL_IMP_THM;
val RIGHT_FORALL_IMP_THM = boolTheory.RIGHT_FORALL_IMP_THM;
val LEFT_IMP_EXISTS_THM  = boolTheory.LEFT_EXISTS_IMP_THM;
val LEFT_FORALL_IMP_THM  = boolTheory.LEFT_FORALL_IMP_THM;
val TRIV_FORALL_IMP_THM  = boolTheory.BOTH_FORALL_IMP_THM;
val TRIV_EXISTS_IMP_THM  = boolTheory.BOTH_EXISTS_IMP_THM;



(* ------------------------------------------------------------------------- *)
(* Monotonicity.                                                             *)
(* ------------------------------------------------------------------------- *)

val MONO_AND = TAUT (--`(x ==> y) /\ (z ==> w) ==> (x /\ z ==> y /\ w)`--);;

val MONO_OR = TAUT (--`(x ==> y) /\ (z ==> w) ==> (x \/ z ==> y \/ w)`--);;

val MONO_IMP = TAUT (--`(y ==> x) /\ (z ==> w) ==> ((x ==> z) ==> (y ==> w))`--);;

val MONO_NOT = TAUT (--`(y ==> x) ==> (~x ==> ~y)`--);;

val MONO_ALL = prove
 ((--`(!x:'a. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))`--),
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

val MONO_EXISTS = prove
 ((--`(!x:'a. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))`--),
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`x:'a`--)) THEN
  EXISTS_TAC (--`x:'a`--) THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Classical.                                                                *)
(* ------------------------------------------------------------------------- *)

val SELECT_REFL   = boolTheory.SELECT_REFL;
val SELECT_UNIQUE = boolTheory.SELECT_UNIQUE;

val SELECT_REFL_2 = prove
 ((--`!x:'a. (@y. x = y) = x`--),
  GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
  THEN CONV_TAC SELECT_CONV
  THEN EXISTS_TAC (--`x:'a`--) THEN REFL_TAC);

val SELECT_THM = prove
 ((--`!P. P (@x. P x) = (?(x:'a). P x)`--),
 REWRITE_TAC [BETA_THM,EXISTS_DEF]);

val _ = add_implicit_rewrites [SELECT_REFL, SELECT_REFL_2];
val _ = add_implicit_rewrites [NOT_CLAUSES];

(* ------------------------------------------------------------------------- *)
(* Infinite de Morgan laws.                                                  *)
(* ------------------------------------------------------------------------- *)

val NOT_EXISTS_THM = boolTheory.NOT_EXISTS_THM
val NOT_FORALL_THM = boolTheory.NOT_FORALL_THM;

val EXISTS_NOT_THM = GSYM NOT_FORALL_THM;
val FORALL_NOT_THM = GSYM NOT_EXISTS_THM;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and disjunction                                      *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_OR_THM  = boolTheory.LEFT_FORALL_OR_THM;
val RIGHT_FORALL_OR_THM = boolTheory.RIGHT_FORALL_OR_THM;
val LEFT_OR_FORALL_THM  = GSYM LEFT_FORALL_OR_THM;
val RIGHT_OR_FORALL_THM = GSYM RIGHT_FORALL_OR_THM;


(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_IMP_THM = boolTheory.LEFT_EXISTS_IMP_THM;
val LEFT_IMP_FORALL_THM = GSYM LEFT_EXISTS_IMP_THM;
val RIGHT_EXISTS_IMP_THM = boolTheory.RIGHT_EXISTS_IMP_THM;
val RIGHT_IMP_EXISTS_THM = GSYM RIGHT_EXISTS_IMP_THM;

val _ = add_implicit_rewrites [COND_CLAUSES];

val COND_BOOL_CLAUSES =
    TAUT (--`(!b e. (if b then T else e) = (b \/ e)) /\
	     (!b t. (if b then t else T) = (b ==> t)) /\
             (!b e. (if b then F else e) = (~b /\ e)) /\
             (!b t. (if b then t else F) = (b /\ t))`--);

val _ = add_implicit_rewrites [COND_BOOL_CLAUSES];


(* ------------------------------------------------------------------------- *)
(* Throw monotonicity in.                                                    *)
(* ------------------------------------------------------------------------- *)

val MONO_COND = prove
 ((--`(x ==> y) /\ (z ==> w) ==> (if b then x else z) ==>
      (if b then y else w)`--),
  STRIP_TAC THEN BOOL_CASES_TAC (--`b:bool`--) THEN
  ASM_REWRITE_TAC[]);

val FUN_EQ_THM = prove
 ((--`!(f:'a->'b) g.  (f = g) = (!x. f x = g x)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC,
    MATCH_ACCEPT_TAC EQ_EXT]);


(* -------------------------------------------------------------------------
 * Congruence Rules
 * ------------------------------------------------------------------------- *)

val IMP_CONG =
    TAUT (--`(P = P') ==> (P' ==> (Q = Q')) ==> ((P ==> Q) = (P' ==> Q'))`--);

val AND_CONG =
    TAUT(--`(Q ==> (P = P')) ==> (P' ==> (Q = Q')) ==>
            ((P /\ Q) = (P' /\ Q'))`--);

val OR_CONG =
    TAUT (--`(~Q ==> (P = P')) ==> (~P' ==> (Q = Q')) ==>
	     ((P \/ Q) = (P' \/ Q'))`--);

val COND_CONG =
    TAUT (--`(g = g') ==>
  	  (g' ==> (t:'a = t')) ==>
	      (~g' ==> (e = e')) ==>
		  ((if g then t else e) = (if g' then t' else e'))`--);

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(* ------------------------------------------------------------------------- *)

val SKOLEM_THM = prove
 ((--`!P. (!x:'a. ?y:'b. P x y) = (?f. !x. P x (f x))`--),
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [EXISTS_TAC (--`\x:'a. @y:'b. P x y`--) THEN GEN_TAC THEN
    BETA_TAC THEN CONV_TAC SELECT_CONV,
    EXISTS_TAC (--`(f:'a->'b) x`--)] THEN
  POP_ASSUM MATCH_ACCEPT_TAC);

(* ------------------------------------------------------------------------- *)
(* NB: this one is true intuitionistically and intensionally.                *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_ALT = prove
 ((--`!P:'a->'b->bool. (!x. ?!y. P x y) = ?f. !x y. P x y = (f x = y)`--),
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT, SKOLEM_THM]);


(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_THM = prove
 ((--`!P. (!x:'a. ?!y:'b. P x y) = (?!f. !x. P x (f x))`--),
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM, SKOLEM_THM, FORALL_AND_THM] THEN
  EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC (--`x:'a`--) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
    MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y1:'b`--), (--`y2:'b`--)]
    THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC (--`f:'a->'b`--)) THEN
    SUBGOAL_THEN (--`(\z. if (z = x) then y1 else (f:'a->'b) z) =
                  (\z. if (z = x) then y2 else (f:'a->'b) z)`--) MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o C AP_THM (--`x:'a`--)) THEN REWRITE_TAC[BETA_THM]]]);


end (* struct *)
