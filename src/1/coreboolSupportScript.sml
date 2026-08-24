(* ===================================================================== *)
(* FILE          : coreboolSupportScript.sml                             *)
(* DESCRIPTION   : Theorems that Prim_rec and boolLib used to prove at    *)
(*                 load time.  Landed here so those libraries can just    *)
(*                 open coreboolSupportTheory instead of firing           *)
(*                 Tactical.prove during their own load.                  *)
(* ===================================================================== *)

Theory coreboolSupport[bare]
Ancestors
  bool
Libs
  HolKernel Parse
  Drule Tactical Tactic Thm_cont Conv Rewrite Ho_Rewrite

(* The Theorem syntax expands to Q.store_thm_at; the real Q sits in
   src/q, downstream of us.  Provide a minimal shim that satisfies the
   expansion using only Parse.typedTerm, Tactical.prove and
   Theory.gen_save_thm --- machinery already available at src/1. *)
structure Q = struct
  fun store_thm_at loc (name, q, tac) =
    let val tm = Parse.typedTerm q Type.bool
        val th = Tactical.prove (tm, tac)
    in Theory.gen_save_thm {name = name, loc = loc, private = false, thm = th}
    end
  fun store_thm x = store_thm_at DB_dtype.Unknown x
end

(*---------------------------------------------------------------------------
    Rewrites over conditionals.  The first three conjuncts of
    COND_BOOL_CLAUSES are useful when rewriting assumptions; the
    second-conjunct pattern is the one Ho_Rewrite consumes when
    boolLib forwards it via add_implicit_rewrites.
 ---------------------------------------------------------------------------*)

Theorem COND_BOOL_CLAUSES:
  (!b e. (if b then T else e) = (b \/ e)) /\
  (!b t. (if b then t else T) = (b ==> t)) /\
  (!b e. (if b then F else e) = (~b /\ e)) /\
  (!b t. (if b then t else F) = (b /\ t))
Proof
  REPEAT (STRIP_TAC ORELSE COND_CASES_TAC ORELSE EQ_TAC)
  THEN RULE_ASSUM_TAC (REWRITE_RULE [F_DEF])
  THEN (ACCEPT_TAC TRUTH ORELSE TRY (FIRST_ASSUM MATCH_ACCEPT_TAC))
  THEN ASM_REWRITE_TAC []
QED

Theorem IF_THEN_T_IMP:
  !b e. (if b then T else e) = (~b ==> e)
Proof
  REPEAT (STRIP_TAC ORELSE COND_CASES_TAC ORELSE EQ_TAC)
  THEN RULE_ASSUM_TAC (REWRITE_RULE [F_DEF])
  THEN (ACCEPT_TAC TRUTH ORELSE TRY (FIRST_ASSUM MATCH_ACCEPT_TAC))
  THEN ASM_REWRITE_TAC []
QED

(*---------------------------------------------------------------------------
    Alternative form of unique existence.
 ---------------------------------------------------------------------------*)

Theorem EXISTS_UNIQUE_ALT:
  !P:'a->bool. (?!x. P x) = ?x. !y. P y = (x = y)
Proof
  GEN_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN EQ_TAC THENL
  [DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ``x:'a``) ASSUME_TAC) THEN
   EXISTS_TAC ``x:'a`` THEN GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
    DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_ACCEPT_TAC],
   DISCH_THEN (X_CHOOSE_TAC ``x:'a``) THEN
   ASM_REWRITE_TAC [GSYM EXISTS_REFL] THEN REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REFL_TAC]
QED

(* Intuitionistic + intensional form of Skolem for unique existence. *)
Theorem UNIQUE_SKOLEM_ALT:
  !P:'a->'b->bool. (!x. ?!y. P x y) = ?f. !x y. P x y = (f x = y)
Proof
  GEN_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_ALT, SKOLEM_THM]
QED

(* Intuitionistic + extensional form of Skolem for unique existence. *)
Theorem UNIQUE_SKOLEM_THM:
  !P. (!x:'a. ?!y:'b. P x y) = ?!f. !x. P x (f x)
Proof
  GEN_TAC
  THEN REWRITE_TAC [EXISTS_UNIQUE_THM, SKOLEM_THM, FORALL_AND_THM]
  THEN EQ_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
  THEN ASM_REWRITE_TAC [] THENL
  [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC ``x:'a`` THEN FIRST_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC ``x:'a`` THEN ASM_REWRITE_TAC [],
   MAP_EVERY X_GEN_TAC [``x:'a``, ``y1:'b``, ``y2:'b``]
   THEN STRIP_TAC THEN
   FIRST_ASSUM (X_CHOOSE_TAC ``f:'a->'b``) THEN
   SUBGOAL_THEN ``(\z. if z=x then y1 else (f:'a->'b) z)
                = (\z. if z=x then y2 else (f:'a->'b) z)`` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [],
    DISCH_THEN (MP_TAC o C AP_THM ``x:'a``) THEN REWRITE_TAC [BETA_THM]]]
QED

(*---------------------------------------------------------------------------
    Trivial rewrites over T / ~T / ~~T conjunctions.  Used by
    Prim_rec.simp_conjs to normalise a chain of these to a single atom.
 ---------------------------------------------------------------------------*)

Theorem notT_and:
  !b. (~T /\ b) = ~T
Proof
  REWRITE_TAC []
QED

Theorem notnotT_and:
  !b. (~~T /\ b) = b
Proof
  REWRITE_TAC []
QED

Theorem T_and:
  !b. (T /\ b) = b
Proof
  REWRITE_TAC []
QED

Theorem T_eqF:
  (T = ~T) = F
Proof
  REWRITE_TAC []
QED

Theorem notnotT:
  ~~T = T
Proof
  REWRITE_TAC []
QED

Theorem notT:
  ~T = F
Proof
  REWRITE_TAC []
QED
