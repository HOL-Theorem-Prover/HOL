(*===========================================================================*)
(* Propositional Logic, up to soundness and completeness. The development is *)
(* a mixture of that in Peter Johnstone's book, Notes on Logic and Set Theory*)
(* and Peter Andrew's book, An Introduction to Mathematical Logic and Type   *)
(* Theory : to Truth Through Proof. Further discussion with John Harrison    *)
(* revealed that the completeness proof is due originally to Kalmar,         *)
(* according to an attribution in Mendelson's book.                          *)
(*===========================================================================*)

open HolKernel boolLib Parse bossLib pred_setTheory;

local open stringLib in end;

val _ = new_theory "PropLogic"

(*---------------------------------------------------------------------------*)
(* Simplification set for arithmetic and sets                                *)
(*---------------------------------------------------------------------------*)

val prop_ss = arith_ss ++ pred_setLib.PRED_SET_ss;

(*---------------------------------------------------------------------------*)
(* Useful lemmas about sets.                                                 *)
(*---------------------------------------------------------------------------*)

val SUBSET_INSERT_MONO = Q.prove
(`!A B x. A SUBSET B ==> (x INSERT A) SUBSET (x INSERT B)`,
 RW_TAC prop_ss [SUBSET_DEF]);

val IN_MONO = Q.prove
(`!x s. x IN s ==> !h. x IN (h INSERT s)`,
 RW_TAC prop_ss []);

val IMAGE_CONG = Q.prove
(`!f1 f2 s. (!x. x IN s ==> (f1 x = f2 x)) ==> (IMAGE f1 s = IMAGE f2 s)`,
 RW_TAC prop_ss [IN_IMAGE, EXTENSION] THEN METIS_TAC[]);

val DIFF_UNION = Q.prove
(`!x y. y SUBSET x ==> ((x DIFF y) UNION y = x)`,
 RW_TAC prop_ss [EXTENSION,SUBSET_DEF] THEN METIS_TAC[]);

val DIFF_INTER = Q.prove
(`!x y. (x DIFF y) INTER y = {}`,
 RW_TAC prop_ss [EXTENSION] THEN METIS_TAC[]);

val lem1 = Q.prove
(`!e s1 s2. (e INSERT s1) UNION s2 = s1 UNION (e INSERT s2)`,
 RW_TAC prop_ss [EXTENSION] THEN METIS_TAC []);

val lem2 = Q.prove
(`!e s1 s2. ~(e IN s1) /\ ~(e IN s2) ==>
  ((e INSERT s1) INTER s2 = s1 INTER (e INSERT s2))`,
 RW_TAC prop_ss [EXTENSION] THEN METIS_TAC[]);


(*---------------------------------------------------------------------------*)
(* Declare HOL datatype of propositions.                                     *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `prop = Var of string
                           | False
                           | Imp of prop => prop`;

(*---------------------------------------------------------------------------*)
(* Make --> into an infix representing Imp(lication).                        *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "-->" (Infixr 490);
val _ = overload_on ("-->", ``Imp``);


(*---------------------------------------------------------------------------*)
(* Variables of a proposition.                                               *)
(*---------------------------------------------------------------------------*)

val Vars_def =
 Define
   `(Vars (Var s) = {Var s}) /\
    (Vars False = {}) /\
    (Vars (p --> q) = (Vars p) UNION (Vars q))`;

val IN_Vars = Q.prove
(`!x p. x IN Vars(p) ==> ?d. x = Var d`,
 GEN_TAC THEN Induct THEN RW_TAC prop_ss [Vars_def] THEN METIS_TAC[]);

val IN_Vars = Q.prove
(`!x p. x IN Vars(p) ==> ?d. x = Var d`,
 Induct_on `p` THEN RW_TAC prop_ss [Vars_def] THEN METIS_TAC[]);

val FINITE_Vars = Q.prove
(`!p. FINITE (Vars p)`,
 Induct THEN RW_TAC prop_ss [Vars_def]);


(*---------------------------------------------------------------------------*)
(* Value of a proposition in an environment. Environments represented by     *)
(* functions of type string->bool.                                           *)
(*---------------------------------------------------------------------------*)

val Value_def =
 Define
  `(Value env (Var s) = env s) /\
   (Value env False = F) /\
   (Value env (p --> q) = ((Value env p) ==> (Value env q)))`;

(*---------------------------------------------------------------------------*)
(* Extra variables mapped by environments do not change the result of Value. *)
(*---------------------------------------------------------------------------*)

val Value_only_on_Vars = Q.prove
(`!p env d b.
    ~(Var d IN Vars p) ==>
    (Value (\x. if x=d then b else env(x)) p = Value env p)`,
 Induct THEN RW_TAC prop_ss [Value_def,Vars_def]);


(*---------------------------------------------------------------------------*)
(* A tautology evaluates to T in every environment.                          *)
(*---------------------------------------------------------------------------*)

val Tautology_def =
 Define
   `Tautology p = !env. Value env p = T`;


(*---------------------------------------------------------------------------*)
(* Define the inference system. First the axioms. Note S and K similarity.   *)
(*---------------------------------------------------------------------------*)

val Ax1_def =
 Define
  `Ax1 p q = p --> q --> p`;

val Ax2_def =
 Define
  `Ax2 p q r = (p --> q --> r) --> (p --> q) --> (p --> r)`;

val Ax3_def =
 Define
  `Ax3 p = ((p --> False) --> False) --> p`;


(*---------------------------------------------------------------------------*)
(* Syntactic entailment via an inductive definition.                         *)
(*---------------------------------------------------------------------------*)

val (is_thm_rules, is_thm_ind, is_thm_cases) =
 Hol_reln
  `(!p q (H:prop set). is_thm H (Ax1 p q)) /\
   (!p q r H. is_thm H (Ax2 p q r)) /\
   (!p H. is_thm H (Ax3 p)) /\
   (!p H. p IN H ==> is_thm H p) /\
   (!H p q. is_thm H (p --> q) /\ is_thm H p ==> is_thm H q)`;

val [is_thm_Ax1, is_thm_Ax2,
     is_thm_Ax3, is_thm_inH, is_thm_MP] = CONJUNCTS is_thm_rules;

(*---------------------------------------------------------------------------*)
(* Make ||- into an infix representing syntactic entailment.                 *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "||-" (Infix(NONASSOC, 450));
val _ = overload_on ("||-", ``is_thm``);

(*---------------------------------------------------------------------------*)
(* Make a "strong" version of induction on the structure of a proof.         *)
(* Not actually used in rest of the development.                             *)
(*---------------------------------------------------------------------------*)

val is_thm_strong_ind =
 IndDefLib.derive_strong_induction (is_thm_rules, is_thm_ind);


(*---------------------------------------------------------------------------*)
(* An example object-logic theorem and its proof.                            *)
(*---------------------------------------------------------------------------*)

val p_Imp_p = Q.prove
(`!H p. H ||- (p --> p)`,
  REPEAT GEN_TAC THEN
 `H ||- (Ax1 p (p --> p))`   by METIS_TAC [is_thm_rules] THEN
 `H ||- (Ax2 p (p --> p) p)` by METIS_TAC [is_thm_rules] THEN
 `H ||- ((p --> p --> p) --> (p --> p))`
                             by METIS_TAC [is_thm_rules,Ax1_def,Ax2_def] THEN
 `H ||- Ax1 p p` by METIS_TAC [is_thm_rules] THEN
 METIS_TAC [Ax1_def,is_thm_rules]);


(*---------------------------------------------------------------------------*)
(* Weakening and the Deduction theorem are used in the completeness proof    *)
(* and help in many object-logic deductions.                                 *)
(*---------------------------------------------------------------------------*)

val weakening_lemma = Q.prove
(`!G p. G ||- p ==> !H. (G SUBSET H) ==> H ||- p`,
 HO_MATCH_MP_TAC is_thm_ind
   THEN REPEAT CONJ_TAC THENL
   [METIS_TAC [is_thm_rules],
    METIS_TAC [is_thm_rules],
    METIS_TAC [is_thm_rules],
    METIS_TAC [is_thm_rules,SUBSET_DEF],
    METIS_TAC [is_thm_rules]]);

val WEAKENING = Q.prove
(`!G H p. G ||- p /\ (G SUBSET H) ==> H ||- p`,
 METIS_TAC [weakening_lemma]);

val Ded1 = Q.prove
(`!H p q. H ||- (p --> q) ==> (p INSERT H) ||- q`,
 REPEAT STRIP_TAC THEN
 `(p INSERT H) ||- (p --> q)` by METIS_TAC[WEAKENING,SUBSET_DEF,IN_INSERT] THEN
 `(p INSERT H) ||- p` by METIS_TAC[is_thm_rules,IN_INSERT] THEN
 `(p INSERT H) ||- q` by METIS_TAC[is_thm_rules]);

val Ded2_lemma = Q.prove
(`!H1 q. H1 ||- q ==> !p H. (H1 = p INSERT H) ==> H ||- (p --> q)`,
 HO_MATCH_MP_TAC is_thm_ind THEN RW_TAC prop_ss [] THENL
 [METIS_TAC [is_thm_rules, Ax1_def],
  METIS_TAC [is_thm_rules, Ax1_def],
  METIS_TAC [is_thm_rules, Ax1_def],
  Cases_on `q=p` THENL
  [(* nts: (p --> p) *)
   FULL_SIMP_TAC prop_ss [] THEN RW_TAC prop_ss [p_Imp_p],
   (* (same as cases 1-3)*)
   METIS_TAC [is_thm_rules, Ax1_def,IN_INSERT]],
  `H ||- (p --> q)` by METIS_TAC [] THEN
  `H ||- (p --> q --> q')` by METIS_TAC[] THEN REPEAT(WEAKEN_TAC is_forall) THEN
  `H ||- ((p --> q --> q') --> (p --> q) --> (p --> q'))`
      by METIS_TAC [is_thm_rules, Ax2_def] THEN
  METIS_TAC [is_thm_rules]]);

val Ded2 = Q.prove
(`!H p q. (p INSERT H) ||- q ==> H ||- (p --> q)`,
 METIS_TAC [Ded2_lemma]);

val DEDUCTION = Q.prove
(`!H p q. is_thm (p INSERT H) q <=> H ||- (p --> q)`,
 METIS_TAC [Ded1, Ded2]);

(*---------------------------------------------------------------------------*)
(* Applications of Deduction Thm: false implies any prop, plus some others   *)
(*---------------------------------------------------------------------------*)

val P_Imp_P = Q.prove
(`!H p. (p INSERT H) ||- p`,
  METIS_TAC [p_Imp_p,DEDUCTION]);

val False_Imp_P = Q.prove
(`!H p. H ||- (False --> p)`,
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
 METIS_TAC [DEDUCTION]);

(*---------------------------------------------------------------------------*)
(* Contrapositive: (p --> q) --> (~q --> ~p)                                 *)
(*---------------------------------------------------------------------------*)

val Contrapos = Q.prove
(`!H p q. H ||- ((p --> q) --> ((q --> False) --> (p --> False)))`,
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
 METIS_TAC [DEDUCTION]);

(*---------------------------------------------------------------------------*)
(* The following statement can also be read (more comfortably) as            *)
(*                                                                           *)
(*   (p --> r) --> (q --> r) --> (p \/ q) --> r                              *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val Disj_Elim = Q.prove
(`!H p q r.
   H ||- ((p --> r) --> (q --> r) --> ((p --> False) --> q) --> r)`,
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
 METIS_TAC [DEDUCTION]);


(*---------------------------------------------------------------------------*)
(*     (p --> q) --> (~p --> q) --> q                                        *)
(*---------------------------------------------------------------------------*)

val Case_Split = Q.prove
(`!H p q. H ||- ((p --> q) --> ((p --> False) --> q) --> q)`,
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
 end);

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

val Sound_lemma = Q.prove
(`!H p. H ||- p ==> (H = {}) ==> Tautology p`,
 HO_MATCH_MP_TAC is_thm_ind
   THEN RW_TAC prop_ss [Tautology_def, Value_def, Ax1_def, Ax2_def, Ax3_def]
   THEN FULL_SIMP_TAC prop_ss []);

val Soundness = Q.store_thm(
  "Soundness",
  `!p. ({} ||- p) ==> Tautology p`,
  METIS_TAC [Sound_lemma]);


(*===========================================================================*)
(* Completeness: every tautology is a theorem.                               *)
(*                                                                           *)
(* First define IValue, which changes the syntax of p, if need be, so that   *)
(* p will evaluate to T in the given env.                                    *)
(*===========================================================================*)

val IValue_def =
 Define
   `IValue env p = if Value env p = T then p else (p --> False)`;

(*---------------------------------------------------------------------------*)
(* Sanity check, not used later.                                             *)
(*---------------------------------------------------------------------------*)

val Value_IValue = Q.prove
(`!p env. Value env (IValue env p) = T`,
 RW_TAC prop_ss [IValue_def,Value_def]);

(*---------------------------------------------------------------------------*)
(* Variables disjoint from those of p are not moved by IValue.               *)
(*---------------------------------------------------------------------------*)

val IValue_only_on_Vars = Q.prove
(`!p env d b. ~(Var d IN Vars p) ==>
               (IValue (\x. if x=d then b else env(x)) p = IValue env p)`,
 RW_TAC prop_ss [IValue_def] THEN METIS_TAC[Value_only_on_Vars]);

val IMAGE_IValue_only_on_Vars = Q.prove
(`!s env d b. ~(Var d IN s) /\ (!x. x IN s ==> ?e. x = Var e) ==>
               (IMAGE (IValue (\x. if x=d then b else env(x))) s =
                IMAGE (IValue env) s)`,
 REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_CONG THEN
 REPEAT STRIP_TAC THEN MATCH_MP_TAC IValue_only_on_Vars THEN
 METIS_TAC [Vars_def,IN_INSERT,NOT_IN_EMPTY,IMAGE_CONG,IValue_only_on_Vars]);


(*---------------------------------------------------------------------------*)
(* Important lemma (from Peter Andrews' book "To Truth Through Proof").      *)
(*---------------------------------------------------------------------------*)

val Andrews_Lemma = Q.store_thm(
 "Andrews_Lemma",
 `!p env H.
    (Vars p) SUBSET H ==> (IMAGE (IValue env) H) ||- (IValue env p)`,
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
   THEN METIS_TAC[DEDUCTION]]]);

(*---------------------------------------------------------------------------*)
(* Proof by induction on the number of variables removed from Vars(p) to get *)
(* V. If no variables dropped (base case), then V = Vars(p) and can use      *)
(* Andrews' Lemma. Otherwise, we have removed n variables and can still      *)
(* prove the prop; if one more is removed, need to show the prop is still    *)
(* provable.                                                                 *)
(*---------------------------------------------------------------------------*)

val Completeness_Lemma = Q.prove
(`!p V. Tautology p /\ (V SUBSET (Vars p))
        ==>
         !env. (IMAGE (IValue env) V) ||- p`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 `?U. (U UNION V = Vars(p)) /\ (U INTER V = {}) /\ FINITE U`
   by (Q.EXISTS_TAC `Vars(p) DIFF V` THEN
       METIS_TAC [DIFF_UNION,DIFF_INTER,FINITE_UNION,FINITE_Vars]) THEN
 POP_ASSUM (fn th =>
    NTAC 3 (POP_ASSUM MP_TAC) THEN Q.ID_SPEC_TAC `V` THEN MP_TAC th) THEN
 Q.ID_SPEC_TAC `U` THEN
 HO_MATCH_MP_TAC FINITE_INDUCT THEN RW_TAC prop_ss [] THENL
 [METIS_TAC [Andrews_Lemma,IValue_def,Tautology_def],
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
  REPEAT (WEAKEN_TAC is_forall) THEN Q.PAT_ASSUM `FINITE s` (K ALL_TAC) THEN
  Q.PAT_ASSUM `(e INSERT V) SUBSET Vars p` (K ALL_TAC) THEN STRIP_TAC THEN
 `?d. e = Var(d)` by METIS_TAC [IN_Vars] THEN RW_TAC std_ss [] THEN
 `(IMAGE (IValue (\x. if x=d then T else env(x))) (Var(d) INSERT V)) ||- p`
        by METIS_TAC[] THEN
 `(IMAGE (IValue (\x. if x=d then F else env(x))) (Var(d) INSERT V)) ||- p`
        by METIS_TAC[] THEN
 Q.PAT_ASSUM `!env. (f env) ||- p` (K ALL_TAC) THEN
 FULL_SIMP_TAC std_ss [IMAGE_INSERT,IValue_def,Value_def] THEN
 `(Var d INSERT IMAGE (IValue(\x. if x=d then T else env x)) V) ||- p /\
  ((Var d --> False) INSERT
   IMAGE (IValue(\x. if x=d then F else env x)) V) ||- p`
    by METIS_TAC [] THEN
 NTAC 2 (POP_ASSUM MP_TAC) THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
 `!x. x IN V ==> ?e. x = Var(e)` by METIS_TAC [SUBSET_DEF,IN_Vars] THEN
 `!b. IMAGE (IValue (\x. (if x = d then b else env x))) V =
      IMAGE (IValue env) V` by METIS_TAC [IMAGE_IValue_only_on_Vars] THEN
 RW_TAC prop_ss [] THEN
 (* Now just do a little object logic proof. *)
 `(IMAGE (IValue env) V) ||- (Var d --> p)` by METIS_TAC [DEDUCTION] THEN
 `(IMAGE (IValue env) V) ||- ((Var d --> False) --> p)`
                    by METIS_TAC [DEDUCTION] THEN
 `(IMAGE(IValue env) V) ||- ((Var d --> p) --> ((Var d --> False) --> p) --> p)`
     by METIS_TAC [Case_Split] THEN
 METIS_TAC [is_thm_MP]]);


(*---------------------------------------------------------------------------*)
(* Completeness is then an easy consequence.                                 *)
(*---------------------------------------------------------------------------*)

val Completeness = Q.store_thm(
 "Completeness",
 `!p. Tautology p ==> {} ||- p`,
 METIS_TAC [EMPTY_SUBSET,IMAGE_EMPTY,Completeness_Lemma]);

val _ = export_theory()
