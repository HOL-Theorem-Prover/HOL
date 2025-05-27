(*===========================================================================*)
(* Propositional Logic, up to soundness and completeness. The development is *)
(* a mixture of that in Peter Johnstone's book, Notes on Logic and Set Theory*)
(* and Peter Andrew's book, An Introduction to Mathematical Logic and Type   *)
(* Theory : to Truth Through Proof. Further discussion with John Harrison    *)
(* revealed that the completeness proof is due originally to Kalmar,         *)
(* according to an attribution in Mendelson's book.                          *)
(*===========================================================================*)

open HolKernel boolLib Parse bossLib pred_setTheory;

local open stringLib string_numTheory in end;

val _ = new_theory "PropLogic"

(*---------------------------------------------------------------------------*)
(* Simplification set for arithmetic and sets                                *)
(*---------------------------------------------------------------------------*)

val prop_ss = arith_ss ++ pred_setLib.PRED_SET_ss;

(*---------------------------------------------------------------------------*)
(* Useful lemmas about sets.                                                 *)
(*---------------------------------------------------------------------------*)

Theorem SUBSET_INSERT_MONO[local]:
  !A B x. A SUBSET B ==> (x INSERT A) SUBSET (x INSERT B)
Proof RW_TAC prop_ss [SUBSET_DEF]
QED

Theorem IN_MONO[local]: !x s. x IN s ==> !h. x IN (h INSERT s)
Proof RW_TAC prop_ss []
QED

Theorem IMAGE_CONG[local]:
  !f1 f2 s. (!x. x IN s ==> (f1 x = f2 x)) ==> (IMAGE f1 s = IMAGE f2 s)
Proof
 RW_TAC prop_ss [IN_IMAGE, EXTENSION] THEN METIS_TAC[]
QED

Theorem DIFF_UNION[local]:
  !x y. y SUBSET x ==> ((x DIFF y) UNION y = x)
Proof RW_TAC prop_ss [EXTENSION,SUBSET_DEF] THEN METIS_TAC[]
QED

Theorem DIFF_INTER[local]: !x y. (x DIFF y) INTER y = {}
Proof
 RW_TAC prop_ss [EXTENSION] THEN METIS_TAC[]
QED

Theorem lem1[local]:
  !e s1 s2. (e INSERT s1) UNION s2 = s1 UNION (e INSERT s2)
Proof RW_TAC prop_ss [EXTENSION] THEN METIS_TAC []
QED

Theorem lem2[local]:
  !e s1 s2. ~(e IN s1) /\ ~(e IN s2) ==>
            ((e INSERT s1) INTER s2 = s1 INTER (e INSERT s2))
Proof RW_TAC prop_ss [EXTENSION] THEN METIS_TAC[]
QED


(*---------------------------------------------------------------------------*)
(* Declare HOL datatype of propositions.                                     *)
(*---------------------------------------------------------------------------*)

Datatype: prop = Var string | False | Imp prop prop
End

(*---------------------------------------------------------------------------*)
(* Make --> into an infix representing Imp(lication).                        *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "-->" (Infixr 490);
Overload "-->" = ``Imp``


(*---------------------------------------------------------------------------*)
(* Variables of a proposition.                                               *)
(*---------------------------------------------------------------------------*)

Definition Vars_def[simp]:
  (Vars (Var s) = {Var s}) /\
  (Vars False = {}) /\
  (Vars (p --> q) = (Vars p) UNION (Vars q))
End

Theorem IN_Vars[local]:
  !x p. x IN Vars(p) ==> ?d. x = Var d
Proof
  Induct_on ‘p’ THEN simp[DISJ_IMP_THM]
QED

Theorem FINITE_Vars[simp]: !p. FINITE (Vars p)
Proof Induct THEN simp[]
QED

(*---------------------------------------------------------------------------*)
(* Value of a proposition in an environment. Environments represented by     *)
(* functions of type string->bool.                                           *)
(*---------------------------------------------------------------------------*)

Definition Value_def[simp]:
  (Value env (Var s) = env s) /\
  (Value env False = F) /\
  (Value env (p --> q) = ((Value env p) ==> (Value env q)))
End

(*---------------------------------------------------------------------------*)
(* Extra variables mapped by environments do not change the result of Value. *)
(*---------------------------------------------------------------------------*)

Theorem Value_only_on_Vars[local]:
  !p env d b.
    Var d NOTIN Vars p ==>
    Value env(| d |-> b |) p = Value env p
Proof
 Induct THEN simp[combinTheory.APPLY_UPDATE_THM]
QED


(*---------------------------------------------------------------------------*)
(* A tautology evaluates to T in every environment.                          *)
(*---------------------------------------------------------------------------*)

Definition Tautology_def: Tautology p = !env. Value env p = T
End

(*---------------------------------------------------------------------------*)
(* Define the inference system. First the axioms. Note S and K similarity.   *)
(*---------------------------------------------------------------------------*)

Definition Ax1_def: Ax1 p q = p --> q --> p
End

Definition Ax2_def: Ax2 p q r = (p --> q --> r) --> (p --> q) --> (p --> r)
End

Definition Ax3_def: Ax3 p = ((p --> False) --> False) --> p
End

(*---------------------------------------------------------------------------*)
(* Syntactic entailment via an inductive definition.                         *)
(*---------------------------------------------------------------------------*)

Inductive is_thm:
[~Ax1:]
  (!p q (H:prop set). is_thm H (Ax1 p q))
[~Ax2:]
  (!p q r H. is_thm H (Ax2 p q r))
[~Ax3:]
  (!p H. is_thm H (Ax3 p))
[~inH:]
  (!p H. p IN H ==> is_thm H p)
[~MP:]
  (!H p q. is_thm H (p --> q) /\ is_thm H p ==> is_thm H q)
End

(*---------------------------------------------------------------------------*)
(* Make ||- into an infix representing syntactic entailment.                 *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "||-" (Infix(NONASSOC, 450));
Overload "||-" = “is_thm”

(*---------------------------------------------------------------------------*)
(* An example object-logic theorem and its proof.                            *)
(*---------------------------------------------------------------------------*)

Theorem p_Imp_p:
  !H p. H ||- (p --> p)
Proof
  REPEAT GEN_TAC THEN
  `H ||- (Ax1 p (p --> p))`   by METIS_TAC [is_thm_rules] THEN
  `H ||- (Ax2 p (p --> p) p)` by METIS_TAC [is_thm_rules] THEN
  `H ||- ((p --> p --> p) --> (p --> p))`
    by METIS_TAC [is_thm_rules,Ax1_def,Ax2_def] THEN
  `H ||- Ax1 p p` by METIS_TAC [is_thm_rules] THEN
  METIS_TAC [Ax1_def,is_thm_rules]
QED


(*---------------------------------------------------------------------------*)
(* Weakening and the Deduction theorem are used in the completeness proof    *)
(* and help in many object-logic deductions.                                 *)
(*---------------------------------------------------------------------------*)

Theorem WEAKENING:
  !G H p. G ||- p ∧ G SUBSET H ==> H ||- p
Proof
  Induct_on ‘is_thm’ >> simp[is_thm_rules] >>
  METIS_TAC [is_thm_rules,SUBSET_DEF]
QED

Theorem Ded1[local]:
  !H p q. H ||- (p --> q) ==> (p INSERT H) ||- q
Proof
 REPEAT STRIP_TAC THEN
 `(p INSERT H) ||- (p --> q)` by METIS_TAC[WEAKENING,SUBSET_DEF,IN_INSERT] THEN
 `(p INSERT H) ||- p` by METIS_TAC[is_thm_rules,IN_INSERT] THEN
 `(p INSERT H) ||- q` by METIS_TAC[is_thm_rules]
QED

Theorem Ded2[local]:
  !H p q. (p INSERT H) ||- q ==> H ||- (p --> q)
Proof
  Induct_on ‘is_thm’ >> rw[] >~
  [‘q ∈ p INSERT H’]
  >- (gvs[] >> metis_tac[p_Imp_p, is_thm_rules, Ax1_def]) >~
  [‘p INSERT H ||- a --> b’, ‘p INSERT H ||- a’]
  >- (‘H ||- p --> a --> b ∧ H ||- p --> a’ by metis_tac[] >>
      ‘H ||- Ax2 p a b’ by simp[is_thm_rules] >>
      irule is_thm_MP >>
      qexists‘p --> a’ >> simp[] >>
      irule is_thm_MP >> metis_tac[Ax2_def]) >>
  metis_tac[Ax1_def, is_thm_rules]
QED

Theorem DEDUCTION:
  !H p q. is_thm (p INSERT H) q <=> H ||- (p --> q)
Proof METIS_TAC [Ded1, Ded2]
QED

(*---------------------------------------------------------------------------*)
(* Applications of Deduction Thm: false implies any prop, plus some others   *)
(*---------------------------------------------------------------------------*)

Theorem P_Imp_P:
  !H p. (p INSERT H) ||- p
Proof
  METIS_TAC [p_Imp_p,DEDUCTION]
QED

Theorem False_Imp_P:
  !H p. H ||- (False --> p)
Proof
  REPEAT GEN_TAC THEN
  `H ||- (Ax1 False (p --> False))`
    by METIS_TAC [is_thm_rules,WEAKENING,SUBSET_EMPTY] THEN
  FULL_SIMP_TAC prop_ss [Ax1_def] THEN
  `(False INSERT H) ||- ((p --> False) --> False)`
    by METIS_TAC [DEDUCTION] THEN
  `(False INSERT H) ||- (((p --> False) --> False) --> p)`
    by METIS_TAC [is_thm_Ax3,Ax3_def,
                  WEAKENING,SUBSET_INSERT_RIGHT,SUBSET_REFL] THEN
  `(False INSERT H) ||- p` by METIS_TAC [is_thm_MP ] THEN
  METIS_TAC [DEDUCTION]
QED

(*---------------------------------------------------------------------------*)
(* Contrapositive: (p --> q) --> (~q --> ~p)                                 *)
(*---------------------------------------------------------------------------*)

Theorem Contrapos:
  !H p q. H ||- ((p --> q) --> ((q --> False) --> (p --> False)))
Proof
 REPEAT GEN_TAC THEN
 `(p INSERT (q --> False) INSERT (p --> q) INSERT H) ||- (p --> q)`
    by METIS_TAC [DEDUCTION, p_Imp_p,WEAKENING,EMPTY_SUBSET,
                  SUBSET_INSERT_MONO, INSERT_COMM]  THEN
 `(p INSERT (q --> False) INSERT (p --> q) INSERT H) ||- p`
    by METIS_TAC [DEDUCTION, p_Imp_p,WEAKENING,EMPTY_SUBSET,
                  SUBSET_INSERT_MONO, INSERT_COMM]  THEN
 `(p INSERT (q --> False) INSERT (p --> q) INSERT H) ||- q`
    by METIS_TAC [is_thm_MP] THEN
 `(p INSERT (q --> False) INSERT (p --> q) INSERT H) ||- (q --> False)`
    by (MATCH_MP_TAC WEAKENING THEN Q.EXISTS_TAC `{q --> False}` THEN
        RW_TAC prop_ss [P_Imp_P]) THEN
 `(p INSERT (q --> False) INSERT (p --> q) INSERT H) ||- False`
    by METIS_TAC [is_thm_MP] THEN
 METIS_TAC [DEDUCTION]
QED

(*---------------------------------------------------------------------------*)
(* The following statement can also be read (more comfortably) as            *)
(*                                                                           *)
(*   (p --> r) --> (q --> r) --> (p \/ q) --> r                              *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Theorem Disj_Elim:
  !H p q r.
    H ||- ((p --> r) --> (q --> r) --> ((p --> False) --> q) --> r)
Proof
 REPEAT GEN_TAC THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- (r --> False)`
    by METIS_TAC [DEDUCTION, p_Imp_p,WEAKENING,EMPTY_SUBSET,SUBSET_INSERT_MONO]
    THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H)  ||- (q --> r)`
    by (MATCH_MP_TAC WEAKENING THEN Q.EXISTS_TAC `{q --> r}`
        THEN RW_TAC prop_ss [P_Imp_P]) THEN
 `((r --> False) INSERT((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- ((r --> False) --> (q --> False))`
    by METIS_TAC [is_thm_MP,Contrapos] THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- (q --> False)`
    by METIS_TAC [is_thm_MP] THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- ((p --> False) --> q)`
    by (MATCH_MP_TAC WEAKENING THEN Q.EXISTS_TAC `{(p --> False) --> q}`
        THEN RW_TAC prop_ss [P_Imp_P]) THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- ((p --> False) --> False)`
    by METIS_TAC [is_thm_MP,Contrapos] THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- p`
    by METIS_TAC [is_thm_MP,is_thm_Ax3,Ax3_def] THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- (p --> r)`
    by (MATCH_MP_TAC WEAKENING THEN Q.EXISTS_TAC `{p --> r}`
        THEN RW_TAC prop_ss [P_Imp_P]) THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- r`
    by METIS_TAC [is_thm_MP] THEN
 `((r --> False) INSERT ((p --> False) --> q) INSERT
  (q --> r) INSERT (p --> r) INSERT H) ||- False`
    by METIS_TAC [is_thm_MP] THEN
 `(((p --> False) --> q) INSERT (q --> r) INSERT
  (p --> r) INSERT H) ||- ((r --> False) --> False)`
    by METIS_TAC [DEDUCTION] THEN
 `(((p --> False) --> q) INSERT (q --> r) INSERT (p --> r) INSERT H) ||- r`
    by METIS_TAC [is_thm_Ax3, Ax3_def, is_thm_MP] THEN
 METIS_TAC [DEDUCTION]
QED


(*---------------------------------------------------------------------------*)
(*     (p --> q) --> (~p --> q) --> q                                        *)
(*---------------------------------------------------------------------------*)

Theorem Case_Split:
  !H p q. H ||- ((p --> q) --> ((p --> False) --> q) --> q)
Proof
 let val lem = Q.SPECL [`H`,`p`,`p --> False`, `q`] Disj_Elim
 in
  REPEAT GEN_TAC THEN ASSUME_TAC lem THEN
  `(((p --> False) --> q) INSERT (p --> q) INSERT H)
   ||- (((p --> False) --> p --> False) --> q)`
    by METIS_TAC [DEDUCTION] THEN
  `(((p --> False) --> q) INSERT (p --> q) INSERT H)
   ||- ((p --> False) --> p --> False)`
    by METIS_TAC [P_Imp_P,DEDUCTION] THEN
  `(((p --> False) --> q) INSERT (p --> q) INSERT H) ||- q`
    by METIS_TAC [is_thm_MP]
  THEN METIS_TAC [DEDUCTION]
 end
QED

(*===========================================================================*)
(* Soundness: every theorem is a tautology. Note that we have to modify      *)
(* the statement in order for it to be in the right shape for induction      *)
(* (on the construction of a proof) to apply.                                *)
(*===========================================================================*)

(*
g `!H p. H ||- p ==> (H={}) ==> Tautology p`;
e (HO_MATCH_MP_TAC is_thm_ind);
e (RW_TAC prop_ss [Tautology_def]);
(*1*)
e (RW_TAC prop_ss [Ax1_def, Value_def]);
(*2*)
e (RW_TAC prop_ss [Ax2_def, Value_def]);
(*3*)
e (RW_TAC prop_ss [Ax3_def, Value_def]);
(*4*)
e (FULL_SIMP_TAC prop_ss []);
(*5*)
e (FULL_SIMP_TAC prop_ss [Value_def]);
*)

(*---------------------------------------------------------------------------*)
(* Previous proof revised into a single tactic invocation.                   *)
(*---------------------------------------------------------------------------*)

Theorem Soundness: !p. ({} ||- p) ==> Tautology p
Proof
  Induct_on ‘is_thm’ >>
  simp[Tautology_def, Value_def, Ax1_def, Ax2_def, Ax3_def]
QED

(*===========================================================================*)
(* Completeness: every tautology is a theorem.                               *)
(*                                                                           *)
(* First define IValue, which changes the syntax of p, if need be, so that   *)
(* p will evaluate to T in the given env.                                    *)
(*===========================================================================*)

Definition IValue_def:
  IValue env p = if Value env p = T then p else (p --> False)
End

(*---------------------------------------------------------------------------*)
(* Sanity check, not used later.                                             *)
(*---------------------------------------------------------------------------*)

Theorem Value_IValue: !p env. Value env (IValue env p) = T
Proof
  RW_TAC prop_ss [IValue_def,Value_def]
QED

(*---------------------------------------------------------------------------*)
(* Variables disjoint from those of p are not moved by IValue.               *)
(*---------------------------------------------------------------------------*)

Theorem IValue_only_on_Vars:
  !p env d b. Var d NOTIN Vars p ==>
              IValue env(| d |-> b |) p = IValue env p
Proof
  rw[IValue_def] THEN METIS_TAC[Value_only_on_Vars]
QED

Theorem IMAGE_IValue_only_on_Vars:
  !s env d b. Var d NOTIN s /\ (!x. x IN s ==> ?e. x = Var e) ==>
              IMAGE (IValue env(| d |-> b |)) s =
              IMAGE (IValue env) s
Proof
 REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_CONG THEN
 REPEAT STRIP_TAC THEN MATCH_MP_TAC IValue_only_on_Vars THEN
 METIS_TAC [Vars_def,IN_INSERT,NOT_IN_EMPTY,IMAGE_CONG,IValue_only_on_Vars]
QED

(*---------------------------------------------------------------------------*)
(* Important lemma (from Peter Andrews' book "To Truth Through Proof").      *)
(*---------------------------------------------------------------------------*)

Theorem Andrews_Lemma:
 !p env H.
   (Vars p) SUBSET H ==> (IMAGE (IValue env) H) ||- (IValue env p)
Proof
 Induct THENL
 [MAP_EVERY Q.X_GEN_TAC [`s`, `env`, `H`] THEN RW_TAC prop_ss [] THEN
  FULL_SIMP_TAC prop_ss [Vars_def] THEN
   `H ||- (Var s)` by METIS_TAC [is_thm_inH] THEN
   `IValue env (Var s) IN (IMAGE (IValue env) H)` by METIS_TAC[IMAGE_IN]
   THEN METIS_TAC[is_thm_inH],
  RW_TAC prop_ss [IValue_def,Value_def] THEN
    METIS_TAC [p_Imp_p, EMPTY_SUBSET,WEAKENING],
  RW_TAC prop_ss [] THEN
  `(IMAGE (IValue env) H) ||- (IValue env p) /\  (* use IH *)
   (IMAGE (IValue env) H) ||- (IValue env p')`
      by METIS_TAC [Vars_def,UNION_SUBSET] THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN REPEAT (WEAKEN_TAC (K true)) THEN
  SIMP_TAC prop_ss [IValue_def,Value_def] THEN
  RW_TAC prop_ss [] THEN FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THENL
  [(*3.1*)
   `(p INSERT (IMAGE (IValue env) H)) ||- p'`
      by METIS_TAC [WEAKENING,SUBSET_INSERT_RIGHT,SUBSET_REFL]
    THEN METIS_TAC[DEDUCTION],
   (*3.2*)
   `((p --> p') INSERT (IMAGE (IValue env) H)) ||- (p --> p')`
      by METIS_TAC [IN_INSERT, is_thm_inH] THEN
   `((p --> p') INSERT (IMAGE (IValue env) H)) ||- p /\
    ((p --> p') INSERT (IMAGE (IValue env) H)) ||- (p' --> False)`
       by METIS_TAC [WEAKENING,SUBSET_INSERT_RIGHT,SUBSET_REFL] THEN
    `((p --> p') INSERT (IMAGE (IValue env) H)) ||- p'`
      by METIS_TAC [is_thm_MP] THEN
   `((p --> p') INSERT (IMAGE (IValue env) H)) ||- False`
      by METIS_TAC [is_thm_MP] THEN
   METIS_TAC[DEDUCTION],
   (*3.3*)
   `(p INSERT (IMAGE (IValue env) H)) ||- False` by METIS_TAC [DEDUCTION] THEN
   `(p INSERT (IMAGE (IValue env) H)) ||- p'`
       by METIS_TAC [False_Imp_P,is_thm_MP]
   THEN METIS_TAC[DEDUCTION],
   (*3.4*)
   `(p INSERT (IMAGE (IValue env) H)) ||- False` by METIS_TAC [DEDUCTION] THEN
   `(p INSERT (IMAGE (IValue env) H)) ||- p'`
       by METIS_TAC [False_Imp_P,is_thm_MP]
   THEN METIS_TAC[DEDUCTION]]]
QED

(*---------------------------------------------------------------------------*)
(* Proof by induction on the number of variables removed from Vars(p) to get *)
(* V. If no variables dropped (base case), then V = Vars(p) and can use      *)
(* Andrews' Lemma. Otherwise, we have removed n variables and can still      *)
(* prove the prop; if one more is removed, need to show the prop is still    *)
(* provable.                                                                 *)
(*---------------------------------------------------------------------------*)

Theorem Completeness_Lemma:
  !p V. Tautology p /\ (V SUBSET (Vars p))
        ==>
        !env. (IMAGE (IValue env) V) ||- p
Proof
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 `?U. (U UNION V = Vars(p)) /\ (U INTER V = {}) /\ FINITE U`
   by (Q.EXISTS_TAC `Vars(p) DIFF V` THEN
       METIS_TAC [DIFF_UNION,DIFF_INTER,FINITE_UNION,FINITE_Vars]) THEN
 POP_ASSUM (fn th =>
    NTAC 3 (POP_ASSUM MP_TAC) THEN Q.ID_SPEC_TAC `V` THEN MP_TAC th) THEN
 Q.ID_SPEC_TAC `U` THEN
 HO_MATCH_MP_TAC FINITE_INDUCT THEN RW_TAC prop_ss [] THEN1
  METIS_TAC [Andrews_Lemma,IValue_def,Tautology_def] THEN
 `U UNION (e INSERT V) = Vars p` by METIS_TAC [lem1] THEN
 `e IN Vars(p)` by METIS_TAC [IN_UNION, IN_INSERT] THEN
 `(e INSERT V) SUBSET Vars p` by METIS_TAC [INSERT_SUBSET] THEN
 `~(e IN V)`
   by (Q.PAT_ASSUM `x INTER y = {}` MP_TAC THEN
       RW_TAC prop_ss [EXTENSION] THEN METIS_TAC[]) THEN
 `U INTER (e INSERT V) = {}` by METIS_TAC [lem2] THEN
 (* finally, use IH *)
 `!env. is_thm (IMAGE (IValue env) (e INSERT V)) p`
   by METIS_TAC[] THEN
 REPEAT (WEAKEN_TAC is_eq) THEN POP_ASSUM MP_TAC THEN
 REPEAT (WEAKEN_TAC is_forall) THEN Q.PAT_X_ASSUM `FINITE s` (K ALL_TAC) THEN
 Q.PAT_X_ASSUM `(e INSERT V) SUBSET Vars p` (K ALL_TAC) THEN STRIP_TAC THEN
 `?d. e = Var(d)` by METIS_TAC [IN_Vars] THEN RW_TAC std_ss [] THEN
 `(IMAGE (IValue env(| d |-> T|)) (Var(d) INSERT V)) ||- p`
        by METIS_TAC[] THEN
 `(IMAGE (IValue env(| d |-> F|)) (Var(d) INSERT V)) ||- p`
        by METIS_TAC[] THEN
 Q.PAT_X_ASSUM `!env. (f env) ||- p` (K ALL_TAC) THEN
 FULL_SIMP_TAC std_ss [IMAGE_INSERT,IValue_def,Value_def,
                       combinTheory.UPDATE_APPLY] THEN
 NTAC 2 (POP_ASSUM MP_TAC) THEN
 `!x. x IN V ==> ?e. x = Var(e)` by METIS_TAC [SUBSET_DEF,IN_Vars] THEN
 `!b. IMAGE (IValue env(| d |-> b |)) V =
      IMAGE (IValue env) V` by METIS_TAC [IMAGE_IValue_only_on_Vars] THEN
 RW_TAC prop_ss [] THEN
 (* Now just do a little object logic proof. *)
 `(IMAGE (IValue env) V) ||- (Var d --> p)` by METIS_TAC [DEDUCTION] THEN
 `(IMAGE (IValue env) V) ||- ((Var d --> False) --> p)`
                    by METIS_TAC [DEDUCTION] THEN
 `(IMAGE(IValue env) V) ||- ((Var d --> p) --> ((Var d --> False) --> p) --> p)`
     by METIS_TAC [Case_Split] THEN
 METIS_TAC [is_thm_MP]
QED

(*---------------------------------------------------------------------------*)
(* Completeness is then an easy consequence.                                 *)
(*---------------------------------------------------------------------------*)

Theorem Completeness: !p. Tautology p ==> {} ||- p
Proof METIS_TAC [EMPTY_SUBSET,IMAGE_EMPTY,Completeness_Lemma]
QED

(* ----------------------------------------------------------------------
    Johnstone's approach, from "Notes on Logic and Set Theory"; showing
    that every consistent set has a maximal (complete), consistent
    extension.
   ---------------------------------------------------------------------- *)

Definition entails_def:
  entails A p ⇔
    ∀env. (∀a. a ∈ A ⇒ Value env a) ⇒ Value env p
End

Theorem entails_EMPTY:
  entails {} p ⇔ Tautology p
Proof
  simp[entails_def, Tautology_def]
QED

Theorem entails_False[simp]:
  entails Γ False ⇒ ∀env. ∃a. a ∈ Γ ∧ ¬Value env a
Proof
  simp[entails_def]
QED

Definition consistent_def:
  consistent Γ ⇔ ¬(Γ ||- False)
End

Overload Not = “λp. p --> False”

Theorem adequacy_implies_completeness:
  (∀Γ. entails Γ False ⇒ ¬consistent Γ) ⇒
  ∀Γ t. entails Γ t ⇒ Γ ||- t
Proof
  rpt strip_tac >>
  ‘entails (Not t INSERT Γ) False’
    by (gs[entails_def, SF DNF_ss] >> metis_tac[]) >>
  ‘¬consistent (Not t INSERT Γ)’ by simp[] >>
  WEAKEN_TAC is_forall >>
  gs[consistent_def, DEDUCTION] >>
  metis_tac[Ax3_def, is_thm_MP, is_thm_Ax3]
QED

(* need to be able to enumerate the props *)
Definition prop2num_def[simp]:
  prop2num False = 0 ∧
  prop2num (Var s) = 2 * s2n s + 1 ∧
  prop2num (Imp p1 p2) = 2 * (prop2num p1 *, prop2num p2) + 2
End

Definition num2prop_def:
  num2prop n = if n = 0 then False
               else if ODD n then Var (n2s ((n - 1) DIV 2))
               else Imp (num2prop (nfst ((n - 2) DIV 2)))
                        (num2prop (nsnd ((n - 2) DIV 2)))
Termination
  WF_REL_TAC ‘$<’ >> rw[]
  >- (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
      irule_at Any numpairTheory.nfst_le >> simp[arithmeticTheory.DIV_LT_X]) >>
  irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
  irule_at Any numpairTheory.nsnd_le >> simp[arithmeticTheory.DIV_LT_X]
End

Theorem prop2num_num2prop[simp]:
  ∀n. prop2num (num2prop n) = n
Proof
  recInduct num2prop_ind >> rpt strip_tac >>
  ONCE_REWRITE_TAC [num2prop_def] >> rw[]
  >- gs[arithmeticTheory.ODD_EXISTS, arithmeticTheory.ADD1] >>
  gs[arithmeticTheory.EVEN_EXISTS, GSYM arithmeticTheory.EVEN_ODD] >>
  rename [‘2 * m - 2’] >> Cases_on ‘m’ >>
  gvs[arithmeticTheory.ADD1, arithmeticTheory.LEFT_ADD_DISTRIB]
QED

Theorem num2prop_prop2num[simp]:
  ∀p. num2prop (prop2num p) = p
Proof
  Induct >> simp[] >> ONCE_REWRITE_TAC[num2prop_def] >>
  rw[arithmeticTheory.ODD_ADD, arithmeticTheory.ODD_MULT]
QED

Theorem num2prop_11[simp]:
  num2prop n1 = num2prop n2 ⇔ n1 = n2
Proof
  metis_tac[prop2num_num2prop]
QED

Theorem prop2num_11[simp]:
  prop2num p1 = prop2num p2 ⇔ p1 = p2
Proof
  metis_tac[num2prop_prop2num]
QED

Definition limitbuild_def[simp]:
  limitbuild A 0 = A ∧
  limitbuild A0 (SUC n) =
  let A = limitbuild A0 n;
      p = num2prop n
  in
    if consistent (p INSERT A) then p INSERT A
    else Not p INSERT A
End

Theorem limitbuild_mono:
  ∀m n. m ≤ n ⇒ limitbuild A m ⊆ limitbuild A n
Proof
  simp[PULL_EXISTS, arithmeticTheory.LESS_EQ_EXISTS] >>
  CONV_TAC SWAP_FORALL_CONV >> Induct >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  rw[] >> gs[SUBSET_DEF]
QED

Theorem consistent_INSERT:
  consistent A ∧ ¬consistent (a INSERT A) ⇒
  consistent (Not a INSERT A)
Proof
  simp[consistent_def] >> rpt strip_tac >>
  gs[DEDUCTION] >> metis_tac[is_thm_MP]
QED

Theorem limitbuild_preserves_consistency:
  consistent A ⇒ ∀n. consistent (limitbuild A n)
Proof
  strip_tac >> Induct >> simp[] >> rw[consistent_INSERT]
QED

Theorem is_thm_FINITE_hyps:
  ∀A a. A ||- a ⇒ ∃A0. FINITE A0 ∧ A0 ⊆ A ∧ A0 ||- a
Proof
  Induct_on ‘is_thm’ >> rw[] >~
  [‘a ∈ A’] >- (qexists ‘{a}’ >> simp[is_thm_inH]) >~
  [‘A1 ⊆ A’, ‘A1 ||- p --> q’, ‘A2 ⊆ A’, ‘A2 ||- p’]
  >- (qexists ‘A1 ∪ A2’ >> simp[] >> irule is_thm_MP >>
      qexists ‘p’ >> conj_tac >> irule WEAKENING >>
      first_assum $ irule_at Any >> simp[]) >>
  metis_tac[FINITE_EMPTY, is_thm_rules, EMPTY_SUBSET]
QED

Overload limit = “λA. BIGUNION (IMAGE (limitbuild A) UNIV)”

Theorem limit_FINITE_SUBSET:
  ∀A B. B ⊆ limit A ∧ FINITE B ⇒ ∃n. B ⊆ limitbuild A n
Proof
  Induct_on ‘FINITE’ >> simp[PULL_EXISTS] >> rw[] >>
  first_x_assum $ drule_then strip_assume_tac >>
  rename [‘B ⊆ limitbuild A n1’, ‘e ∈ limitbuild A n2’] >>
  qexists ‘MAX n1 n2’ >> conj_tac >~
  [‘B ⊆ limitbuild A (MAX n1 n2)’]
  >- (irule SUBSET_TRANS >> irule_at Any limitbuild_mono >>
      first_assum $ irule_at Any >> simp[]) >>
  irule (iffLR SUBSET_DEF) >> first_assum $ irule_at Any >>
  irule limitbuild_mono >> simp[]
QED

Theorem limit_consistency:
  consistent A ⇒ consistent (limit A)
Proof
  simp[consistent_def] >> rpt strip_tac >>
  ‘∃B. FINITE B ∧ B ⊆ limit A ∧ B ||- False’ by metis_tac[is_thm_FINITE_hyps] >>
  ‘¬(B ⊆ A)’ by metis_tac[WEAKENING] >>
  drule_all_then (qx_choose_then ‘N’ strip_assume_tac) limit_FINITE_SUBSET >>
  ‘¬(limitbuild A N ||- False)’
    by metis_tac[limitbuild_preserves_consistency, consistent_def] >>
  metis_tac[WEAKENING]
QED

Theorem limits_complete:
  ∀p. p ∈ limit A ∨ Not p ∈ limit A
Proof
  simp[PULL_EXISTS] >> CCONTR_TAC >> gs[] >>
  rpt $ first_x_assum $ qspec_then ‘SUC $ prop2num p’ mp_tac >>
  simp[limitbuild_def] >> rw[]
QED

Theorem limits_extend:
  A ⊆ limit A
Proof
  simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >> qexists ‘0’ >> simp[]
QED

Theorem consistent_no_False:
  consistent A ⇒ False ∉ A
Proof
  simp[consistent_def] >> rpt strip_tac >> metis_tac[is_thm_inH]
QED

Theorem limit_entailed:
  consistent (limit A) ⇒
  ∀a. Value (λv. Var v ∈ limit A) a ⇔ a ∈ limit A
Proof
  strip_tac >> Induct >> qabbrev_tac ‘L = limit A’ >> simp[PULL_EXISTS]
  >- simp[consistent_no_False] >>
  rename [‘a --> b’] >>
  map_every Cases_on [‘a ∈ L’, ‘b ∈ L’] >> gs[] >> CCONTR_TAC >> gs[] >~
  [‘a ∈ L’, ‘b ∈ L’, ‘a --> b ∉ L’]
  >- (‘Not (a --> b) ∈ L’ by metis_tac [limits_complete] >>
      ‘L ||- b’ by metis_tac[is_thm_inH] >>
      ‘L ||- b --> a --> b’ by metis_tac[is_thm_Ax1, Ax1_def] >>
      ‘L ||- a --> b’ by metis_tac[is_thm_MP] >>
      metis_tac [consistent_def, is_thm_rules]) >~
  [‘a ∈ L’, ‘b ∉ L’, ‘a --> b ∈ L’]
  >- (‘L ||- b’ by metis_tac[is_thm_rules] >>
      metis_tac[consistent_def, is_thm_rules, limits_complete]) >~
  [‘a ∉ L’, ‘b ∈ L’, ‘a --> b ∉ L’]
  >- (‘L ||- b’ by metis_tac[is_thm_rules] >>
      ‘L ||- a --> b’ by metis_tac[is_thm_rules, Ax1_def] >>
      metis_tac[consistent_def, limits_complete, is_thm_rules]) >~
  [‘a ∉ L’, ‘b ∉ L’, ‘a --> b ∉ L’]
  >- (‘L ||- a --> b’ suffices_by
        metis_tac[limits_complete, consistent_def, is_thm_rules] >>
      simp[GSYM DEDUCTION] >> irule is_thm_MP >>
      qexists ‘False’ >> simp[False_Imp_P] >> irule is_thm_MP >>
      qexists ‘a’ >> metis_tac[IN_INSERT, is_thm_rules, limits_complete])
QED

Theorem adequacy:
  ∀Γ. entails Γ False ⇒ ¬consistent Γ
Proof
  rpt strip_tac >> drule_then assume_tac limit_consistency >>
  drule entails_False >> simp[] >> qexists ‘(λv. Var v ∈ limit Γ)’ >>
  qx_gen_tac ‘a’ >> Cases_on ‘a ∈ Γ’ >> simp[Excl "IN_BIGUNION"] >>
  metis_tac[limit_entailed, SUBSET_DEF, limits_extend]
QED

Theorem completeness_again:
  entails Γ ϕ ⇒ Γ ||- ϕ
Proof
  metis_tac[adequacy_implies_completeness, adequacy]
QED

Theorem soundness_again:
  Γ ||- ϕ ⇒ entails Γ ϕ
Proof
  Induct_on ‘is_thm’ >> simp[Ax1_def, Ax2_def, Ax3_def, entails_def]
QED

Theorem compactness:
  entails Γ ϕ ⇒ ∃Γ₀. FINITE Γ₀ ∧ Γ₀ ⊆ Γ ∧ entails Γ₀ ϕ
Proof
  metis_tac[is_thm_FINITE_hyps, completeness_again, soundness_again]
QED

val _ = export_theory()
