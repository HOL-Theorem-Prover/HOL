(* ===================================================================== *)
(* FILE          : boolLib.sml                                           *)
(* DESCRIPTION   : boolTheory and related support, most of which is      *)
(*                 inherited from hol88.                                 *)
(* ===================================================================== *)

structure boolLib =
struct

 open boolTheory boolSyntax 
      Drule Tactical Tactic Thm_cont Conv Rewrite Prim_rec Abbrev;

 local open DefnBase TypeBase Ho_Net Ho_Rewrite Psyntax Rsyntax in end

val Term = Parse.Term
val Type = Parse.Type
val --   = Parse.--   

(*---------------------------------------------------------------------------
      Stock the rewriter in Ho_Rewrite with some rules not proved
      in boolTheory.
 ---------------------------------------------------------------------------*)

infix THEN THENL ORELSE

val COND_BOOL_CLAUSES = 
  prove(Term`(!b e. (if b then T else e) = (b \/ e)) /\
             (!b t. (if b then t else T) = (b ==> t)) /\
             (!b e. (if b then F else e) = (~b /\ e)) /\
             (!b t. (if b then t else F) = (b /\ t))`,
let open HolKernel
in
REPEAT (STRIP_TAC ORELSE COND_CASES_TAC ORELSE EQ_TAC)
 THEN TRY (ACCEPT_TAC TRUTH ORELSE FIRST_ASSUM ACCEPT_TAC) THENL 
 [DISJ1_TAC THEN ACCEPT_TAC TRUTH,
  DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC,
  FIRST_ASSUM MATCH_MP_TAC THEN ACCEPT_TAC TRUTH,
  POP_ASSUM (K ALL_TAC) THEN 
  POP_ASSUM (MP_TAC o EQ_MP (el 2 (CONJUNCTS (SPEC_ALL NOT_CLAUSES)))) THEN 
  ACCEPT_TAC (EQT_ELIM (el 4 (CONJUNCTS (SPEC F IMP_CLAUSES))))]
end);

val _ = 
  let open boolTheory 
  in Ho_Rewrite.add_implicit_rewrites [COND_BOOL_CLAUSES]
  end;

(* ------------------------------------------------------------------------- *)
(* Alternative version of unique existence, slated for boolTheory.           *)
(* ------------------------------------------------------------------------- *)

local open HolKernel Ho_Rewrite
in
val EXISTS_UNIQUE_ALT = prove(
(* store_thm( "EXISTS_UNIQUE_ALT", *)
 Term`!P:'a->bool. (?!x. P x) = ?x. !y. P y = (x = y)`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC (--`x:'a`--)) ASSUME_TAC) THEN
    EXISTS_TAC (--`x:'a`--) THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_ACCEPT_TAC],
    DISCH_THEN(X_CHOOSE_TAC (--`x:'a`--)) THEN
    ASM_REWRITE_TAC[GSYM EXISTS_REFL] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REFL_TAC]);;


(* ------------------------------------------------------------------------- *)
(* NB: this one is true intuitionistically and intensionally.                *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_ALT = prove
(*  "UNIQUE_SKOLEM_ALT", *)
 (Term`!P:'a->'b->bool. (!x. ?!y. P x y) = ?f. !x y. P x y = (f x = y)`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT, SKOLEM_THM]);


(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_THM = prove
(* store_thm("UNIQUE_SKOLEM_THM", *)
(Term`!P. (!x:'a. ?!y:'b. P x y) = ?!f. !x. P x (f x)`,
 GEN_TAC 
  THEN Ho_Rewrite.REWRITE_TAC[EXISTS_UNIQUE_THM, SKOLEM_THM, FORALL_AND_THM]
  THEN EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) 
  THEN ASM_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC (--`x:'a`--) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
    MAP_EVERY X_GEN_TAC [(--`x:'a`--), (--`y1:'b`--), (--`y2:'b`--)]
    THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC (--`f:'a->'b`--)) THEN
    SUBGOAL_THEN (--`(\z. if z=x then y1 else (f:'a->'b) z)
                   = (\z. if z=x then y2 else (f:'a->'b) z)`--) MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o C AP_THM (--`x:'a`--)) THEN REWRITE_TAC[BETA_THM]]]);


(*---------------------------------------------------------------------------
   From Joe Hurd : case analysis on the (4) functions in the type
   :bool -> bool. Also slated for boolTheory.
 ---------------------------------------------------------------------------*)

val BOOL_FUN_CASES_THM = prove(
 (* store_thm ("BOOL_FUN_CASES_THM", *)
  Term `!f. (f = \b. F) \/ (f = \b. T) \/ (f = \b. b) \/ (f = \b. ~b)`,
  GEN_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
    THEN ASM_CASES_TAC (Term`f T:bool`) 
    THEN ASM_CASES_TAC (Term`f F:bool`)
    THENL [DISJ2_TAC THEN DISJ1_TAC,
           DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC,
           DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC,
           DISJ1_TAC]
    THEN GEN_TAC 
    THEN BOOL_CASES_TAC (Term`b:bool`) 
    THEN ASM_REWRITE_TAC []);

val BOOL_FUN_INDUCT = prove(
 (* store_thm ("BOOL_FUN_INDUCT", *)
   Term`!P. P (\b. F) /\ P (\b. T) /\ P (\b. b) /\ P (\b. ~b) ==> !f. P f`,
   REPEAT STRIP_TAC
     THEN MP_TAC (SPEC (Term`f:bool->bool`) BOOL_FUN_CASES_THM)
     THEN STRIP_TAC 
     THEN ASM_REWRITE_TAC[])
end;

end
