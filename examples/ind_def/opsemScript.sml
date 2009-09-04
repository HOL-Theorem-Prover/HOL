(*===========================================================================*)
(* Operational semantics and program logic for a very simple imperative      *)
(* programming language. Adapted from an example of Tom Melham and Juanito   *)
(* Camilleri.                                                                *)
(*===========================================================================*)

structure opsemScript =
struct

(* Interactive use:
  app load ["stringLib", "finite_mapTheory"];
*)

open HolKernel Parse boolLib bossLib
     stringLib IndDefLib IndDefRules finite_mapTheory;

val _ = new_theory "opsem";

(*---------------------------------------------------------------------------*)
(* Syntax of the programming language.					     *)
(*                                                                           *)
(* Program variables are represented by strings, and states are modelled by  *)
(* finite maps from program variables to natural numbers.	             *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("state", ``:string |-> num``);

(*---------------------------------------------------------------------------*)
(* Natural number expressions and boolean expressions are defined by         *)
(* datatypes with simple evaluation semantics. In the following proofs,      *)
(* neval and beval don't end up playing a role.                              *)
(*---------------------------------------------------------------------------*)

val _ =
 Hol_datatype
      `nexp = Var of string
            | Const of num
            | Plus of nexp => nexp
            | Times of nexp => nexp
            | Sub of nexp => nexp`;

val _ =
 Hol_datatype
      `bexp = Equal of nexp => nexp
            | Less of nexp => nexp
            | Not of bexp`;

val neval_def =
 Define
  `(neval (Var s) sigma = (sigma ' s)) /\
   (neval (Const c) sigma = c) /\
   (neval (Plus e1 e2) sigma = neval e1 sigma + neval e2 sigma) /\
   (neval (Times e1 e2) sigma = neval e1 sigma * neval e2 sigma) /\
   (neval (Sub e1 e2) sigma = neval e1 sigma - neval e2 sigma)`;

val beval_def =
 Define
  `(beval (Equal e1 e2) sigma = (neval e1 sigma = neval e2 sigma)) /\
   (beval (Less e1 e2) sigma = (neval e1 sigma < neval e2 sigma)) /\
   (beval (Not e) sigma = ~(beval e sigma))`;


(*---------------------------------------------------------------------------*)
(* Datatype of programs                                                      *)
(*---------------------------------------------------------------------------*)

val _ =
 Hol_datatype
  `program = Skip
           | Assign of string => nexp
           | Seq    of program => program
           | Cond   of bexp => program => program
           | While  of bexp => program`;


(*---------------------------------------------------------------------------*)
(* Operational semantics. The semantics of commands will be given by a       *)
(* relation                                                                  *)
(*                                                                           *)
(*   EVAL : program -> state -> state -> bool                                *)
(*                                                                           *)
(* defined inductively such that                                             *)
(*                                                                           *)
(*   EVAL c s1 s2                                                            *)
(*                                                                           *)
(* holds exactly when executing the command c in the initial state s1        *)
(* terminates in the final state s2. The evaluation relation is defined      *)
(* inductively by the set of rules shown below.                              *)
(*---------------------------------------------------------------------------*)

val (rules,induction,ecases) = Hol_reln
   `(!s. EVAL Skip s s)
 /\ (!s v e. EVAL (Assign v e) s (s |+ (v,neval e s)))
 /\ (!c1 c2 s1 s2 s3. EVAL c1 s1 s2 /\ EVAL c2 s2 s3 ==> EVAL (Seq c1 c2) s1 s3)
 /\ (!c1 c2 s1 s2 b.  EVAL c1 s1 s2 /\ beval b s1 ==> EVAL (Cond b c1 c2) s1 s2)
 /\ (!c1 c2 s1 s2 b. EVAL c2 s1 s2 /\ ~beval b s1 ==> EVAL (Cond b c1 c2) s1 s2)
 /\ (!c s b. ~beval b s ==> EVAL (While b c) s s)
 /\ (!c s1 s2 s3 b.
         EVAL c s1 s2 /\
         EVAL (While b c) s2 s3 /\ beval b s1 ==> EVAL (While b c) s1 s3)`;

val rulel = CONJUNCTS rules;

(* --------------------------------------------------------------------- *)
(* Stronger form of rule induction.					 *)
(* --------------------------------------------------------------------- *)

val sinduction = derive_strong_induction(rules,induction);

(* =====================================================================*)
(* Derivation of backwards case analysis theorems for each rule.        *)
(*									*)
(* These theorems are consequences of the general case analysis theorem *)
(* proved above.  They are used to justify formal reasoning in which the*)
(* rules are driven "backwards', inferring premisses from conclusions.  *)
(* =====================================================================*)

val SKIP_THM = store_thm
("SKIP_THM",
 ``!s1 s2. EVAL Skip s1 s2 = (s1 = s2)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val ASSIGN_THM = store_thm
("ASSIGN_THM",
 ``!s1 s2 v e. EVAL (Assign v e) s1 s2 = (s2 = s1 |+ (v,neval e s1))``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val SEQ_THM = store_thm
("SEQ_THM",
 ``!s1 s3 c1 c2. EVAL (Seq c1 c2) s1 s3 = ?s2. EVAL c1 s1 s2 /\ EVAL c2 s2 s3``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val IF_T_THM = store_thm
("IF_T_THM",
 ``!s1 s2 b c1 c2.
     beval b s1 ==> (EVAL (Cond b c1 c2) s1 s2 = EVAL c1 s1 s2)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val IF_F_THM = store_thm
("IF_F_THM",
 ``!s1 s2 b c1 c2.
     ~beval b s1 ==> (EVAL (Cond b c1 c2) s1 s2 = EVAL c2 s1 s2)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val WHILE_T_THM = store_thm
("WHILE_T_THM",
 ``!s1 s3 b c.
    beval b s1 ==>
      (EVAL (While b c) s1 s3 = ?s2. EVAL c s1 s2 /\
                                     EVAL (While b c) s2 s3)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val WHILE_F_THM = store_thm
("WHILE_F_THM",
 ``!s1 s2 b c. ~beval b s1 ==> (EVAL (While b c) s1 s2 = (s1 = s2))``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

(*---------------------------------------------------------------------------*)
(* THEOREM: the operational semantics is deterministic.                      *)
(*                                                                           *)
(* Given the suite of theorems proved above, this proof is relatively        *)
(* straightforward.  The standard proof is by structural induction on c, but *)
(* the proof by rule induction given below gives rise to a slightly easier   *)
(* analysis in each case of the induction.  There are, however, more         *)
(* cases---one per rule, rather than one per constructor.                    *)
(*---------------------------------------------------------------------------*)

val EVAL_DETERMINISTIC = store_thm
("EVAL_DETERMINISTIC",
 ``!c st1 st2. EVAL c st1 st2 ==> !st3. EVAL c st1 st3 ==> (st2 = st3)``,
 HO_MATCH_MP_TAC induction THEN
 RW_TAC std_ss [SKIP_THM,ASSIGN_THM,SEQ_THM,
                IF_T_THM,IF_F_THM,WHILE_T_THM, WHILE_F_THM] THEN
 METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* Definition of Floyd-Hoare logic judgements for partial correctness and    *)
(* derivation of proof rules.                                                *)
(*---------------------------------------------------------------------------*)

val SPEC_def =
 Define
   `SPEC P c Q = !s1 s2. P s1 /\ EVAL c s1 s2 ==> Q s2`;


(*---------------------------------------------------------------------------*)
(* Skip rule                                                                 *)
(*---------------------------------------------------------------------------*)

val SKIP_RULE = store_thm
("SKIP_RULE",
 ``!P. SPEC P Skip P``,
 RW_TAC std_ss [SPEC_def,SKIP_THM]);

(*---------------------------------------------------------------------------*)
(* Assignment rule                                                           *)
(*---------------------------------------------------------------------------*)

val ASSIGN_RULE = store_thm
("ASSIGN_RULE",
 ``!P v e.
      SPEC (\s. P (s |+ (v,neval e s))) (Assign v e) P``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC [ASSIGN_THM]);

(*---------------------------------------------------------------------------*)
(* Sequencing rule                                                           *)
(*---------------------------------------------------------------------------*)

val SEQ_RULE = store_thm
("SEQ_RULE",
 ``!P c1 c2 Q R.
       SPEC P c1 Q /\ SPEC Q c2 R ==> SPEC P (Seq c1 c2) R``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC [SEQ_THM]);

(*---------------------------------------------------------------------------*)
(* Conditional rule                                                          *)
(*---------------------------------------------------------------------------*)

val COND_RULE = store_thm
("COND_RULE",
 ``!P b c1 c2 Q.
      SPEC (\s. P(s) /\ beval b s) c1 Q /\
      SPEC (\s. P(s) /\ ~beval b s) c2 Q ==> SPEC P (Cond b c1 c2) Q``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC [IF_T_THM, IF_F_THM]);

(*---------------------------------------------------------------------------*)
(* While rule                                                                *)
(*---------------------------------------------------------------------------*)

val lemma1 = Q.prove
(`!c s1 s2. EVAL c s1 s2 ==> !b' c'. (c = While b' c') ==> ~beval b' s2`,
 HO_MATCH_MP_TAC induction THEN RW_TAC std_ss []);

val lemma2 = Q.prove
(`!c s1 s2.
   EVAL c s1 s2 ==>
     !b' c'. (c = While b' c') ==>
             (!s1 s2. P s1 /\ beval b' s1 /\ EVAL c' s1 s2 ==> P s2) ==>
             (P s1 ==> P s2)`,
 HO_MATCH_MP_TAC sinduction THEN RW_TAC std_ss [] THEN METIS_TAC[]);

val WHILE_RULE = store_thm
("WHILE_RULE",
 ``!P b c. SPEC (\s. P(s) /\ beval b s) c P ==>
           SPEC P (While b c) (\s. P s /\ ~beval b s)``,
 RW_TAC std_ss [SPEC_def] THENL [METIS_TAC[lemma2],METIS_TAC[lemma1]]);


(*---------------------------------------------------------------------------*)
(* Precondition strengthening                                                *)
(*---------------------------------------------------------------------------*)

val PRE_STRENGTHEN = store_thm
("PRE_STRENGTHEN",
 ``!P c Q P'. (!s. P' s ==> P s) /\  SPEC P c Q ==> SPEC P' c Q``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* postcondition weakening                                                   *)
(*---------------------------------------------------------------------------*)

val POST_WEAKEN = store_thm
("POST_WEAKEN",
 ``!P c Q Q'. (!s. Q s ==> Q' s) /\  SPEC P c Q ==> SPEC P c Q'``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* Boolean combinations of pre-and-post-conditions.                          *)
(*---------------------------------------------------------------------------*)

val CONJ_TRIPLE = store_thm
("CONJ_TRIPLE",
 ``!P1 P2 c Q1 Q2. SPEC P1 c Q1 /\ SPEC P2 c Q2
                   ==> SPEC (\s. P1 s /\ P2 s) c (\s. Q1 s /\ Q2 s)``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC[]);

val DISJ_TRIPLE = store_thm
("DISJ_TRIPLE",
 ``!P1 P2 c Q1 Q2. SPEC P1 c Q1 /\ SPEC P2 c Q2
                   ==> SPEC (\s. P1 s \/ P2 s) c (\s. Q1 s \/ Q2 s)``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC[]);

val _ = export_theory();

end
