
(* ============================ newOpsemScript.sml ============================

This file is an extension of the Melham-Camilleri opsem example
distributed with HOL4 in HOL/examples/ind_def/opsemScript.sml.

 Tom Melham:        http://web.comlab.ox.ac.uk/Tom.Melham/
 Juanito Camilleri: http://www.um.edu.mt/about/uom/administration

See see newOpsemDoc.txt for some documentation.

=============================================================================*)


(*===========================================================================*)
(* Start of text adapted from examples/ind_def/opsemScript.sml               *)
(*===========================================================================*)

(*===========================================================================*)
(* Operational semantics and program logic for a very simple imperative      *)
(* programming language. Adapted from an example of Tom Melham and Juanito   *)
(* Camilleri.                                                                *)
(*===========================================================================*)

(* Stuff needed when running interactively
quietdec := true; (* turn off printing *)
app load ["stringLib", "finite_mapTheory", "intLib", "pred_setTheory"];
open HolKernel Parse boolLib bossLib 
     stringLib IndDefLib IndDefRules finite_mapTheory relationTheory
     pred_setTheory;
intLib.deprecate_int();
clear_overloads_on "TC"; (* Stop TC R printing as TC^+ *)
quietdec := false; (* turn printing back on *)
*)

open HolKernel Parse boolLib bossLib 
     stringLib IndDefLib IndDefRules finite_mapTheory relationTheory
     pred_setTheory;

val _ = intLib.deprecate_int();
val _ = clear_overloads_on "TC"; (* Stop TC R printing as TC^+ *)

val _ = new_theory "newOpsem";

val _ = computeLib.add_persistent_funs
         [("finite_mapTheory.FUPDATE_LIST_THM",FUPDATE_LIST_THM),
          ("finite_mapTheory.DOMSUB_FUPDATE_THM",DOMSUB_FUPDATE_THM),
          ("finite_mapTheory.DOMSUB_FEMPTY",DOMSUB_FEMPTY),
          ("finite_mapTheory.FDOM_FUPDATE",FDOM_FUPDATE),
          ("finite_mapTheory.FAPPLY_FUPDATE_THM",FAPPLY_FUPDATE_THM),
          ("finite_mapTheory.FDOM_FEMPTY",FDOM_FEMPTY),
          ("pred_setTheory.IN_INSERT",pred_setTheory.IN_INSERT),
          ("pred_setTheory.IN_UNION",pred_setTheory.IN_UNION),
          ("pred_setTheory.NOT_IN_EMPTY",pred_setTheory.NOT_IN_EMPTY),
          ("integerTheory.NUM_OF_INT", integerTheory.NUM_OF_INT)
         ];

(* make infix ``$/`` equal to ``$DIV`` *)

val DIV_AUX_def = xDefine "DIV_AUX" `m / n = m DIV n`;

(*---------------------------------------------------------------------------*)
(* A value is a scalar (number) or one-dimensional array                     *)
(*---------------------------------------------------------------------------*)

val _ =
 Hol_datatype
  `value = Scalar of int | Array  of (num |-> int)`;

(*---------------------------------------------------------------------------*)
(* Program variables are represented by strings, and states are modelled by  *)
(* finite maps from program variables to values                              *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("state", ``:string |-> value``);

val isScalar_def =
 Define
  `(isScalar(Scalar n) = T) /\ (isScalar(Array a) = F)`;

val ScalarOf_def =
 Define
  `ScalarOf(Scalar n) = n`;

val isArray_def =
 Define
  `(isArray(Array a) = T) /\ (isArray(Scalar n) = F)`;

val ArrayOf_def =
 Define
  `ArrayOf(Array a) = a`;

(*---------------------------------------------------------------------------*)
(* Syntax of the programming language.					     *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Natural number (nexp), boolean (bexp) and array expressions (aexp)        *)
(* are defined by datatypes with simple evaluation semantics.                *)
(*---------------------------------------------------------------------------*)

val _ = 
 Hol_datatype 
  `nexp = Var of string 
        | Arr of string => nexp
        | Const of int
        | Plus of nexp => nexp
        | Sub of nexp => nexp
        | Times of nexp => nexp
        | Div of nexp => nexp
        | Min of nexp => nexp`;

val _ = 
 Hol_datatype 
  `bexp = Equal of nexp => nexp
        | Less of nexp => nexp
        | LessEq of nexp => nexp
        | Greater of nexp => nexp
        | GreaterEq of nexp => nexp
        | And of bexp => bexp
        | Or of bexp => bexp
        | Not of bexp`;

val _ =
 Hol_datatype
  `aexp = ArrConst  of (num |-> int)           (* array constant *)
        | ArrVar    of string                  (* array variable *)
        | ArrUpdate of aexp => nexp => nexp`;  (* array update   *)

val neval_def =  
 Define
  `(neval (Var v) s = ScalarOf(s ' v)) /\
   (neval (Arr a e) s = (ArrayOf(s ' a) ' (Num(neval e s)))) /\
   (neval (Const c) s = c) /\
   (neval (Plus e1 e2) s = integer$int_add (neval e1 s) (neval e2 s)) /\
   (neval (Sub e1 e2) s = integer$int_sub (neval e1 s) (neval e2 s)) /\
   (neval (Times e1 e2) s = integer$int_mul (neval e1 s) (neval e2 s)) /\
   (neval (Div e1 e2) s = integer$int_quot (neval e1 s) (neval e2 s)) /\
   (neval (Min e1 e2) s = integer$int_min (neval e1 s) (neval e2 s))`;

val beval_def =  
 Define
  `(beval (Equal e1 e2) s = (neval e1 s = neval e2 s)) /\
   (beval (Less e1 e2) s = integer$int_lt (neval e1 s) (neval e2 s)) /\
   (beval (LessEq e1 e2) s = integer$int_le (neval e1 s) (neval e2 s)) /\
   (beval (And b1 b2) s = (beval b1 s /\ beval b2 s)) /\
   (beval (Or b1 b2) s = (beval b1 s \/ beval b2 s)) /\
   (beval (Not e) s = ~(beval e s))`;

val aeval_def =
 Define
  `(aeval (ArrConst f) s = f)
   /\
   (aeval (ArrVar v) s = ArrayOf(s ' v))
   /\
   (aeval (ArrUpdate a e1 e2) s = aeval a s |+ (Num(neval e1 s), neval e2 s))`;

val Update_def =
 Define
  `(Update v (INL e) s = s |+ (v, Scalar(neval e s)))
   /\
   (Update v (INR a) s = s |+ (v, Array(aeval a s)))`;

(* Convert a value or array to a constant expression *)
val Exp_def =
 Define
  `(Exp(Scalar n) = INL(Const n))
   /\
   (Exp(Array f)  = INR(ArrConst f))`;

val Update_Exp =
 store_thm
  ("Update_Exp",
   ``!v val s. Update v (Exp val) s = s |+ (v, val)``,
   Cases_on `val`
    THEN RW_TAC std_ss [Update_def,Exp_def,aeval_def,neval_def]);

(*===========================================================================*)
(* Type of outputs of executing programs (e.g. Proc bodies)                  *)
(*===========================================================================*)

val _ =
 Hol_datatype 
  `outcome = RESULT of state | ERROR of state | TIMEOUT of state`;

(* Some automatically proves theorems relating RESULT, TIMEOUT and ERROR     *)

val outcome_11       = fetch "-" "outcome_11";
val outcome_distinct = fetch "-" "outcome_distinct";
val outcome_nchotomy = fetch "-" "outcome_nchotomy";

(*---------------------------------------------------------------------------*)
(* Datatype of programs                                                      *)
(*---------------------------------------------------------------------------*)

val _ = 
 Hol_datatype
  `program = Skip                                    (* null command         *)
           | GenAssign of string => (nexp + aexp)    (* variable assignment  *)
           | Dispose   of string                     (* deallocate variable  *)
           | Seq       of program => program         (* sequencing           *)
           | Cond      of bexp => program => program (* conditional          *)
           | While     of bexp => program            (* while loop           *)
           | Local     of string => program          (* local variable block *)
           | Proc      of (state -> outcome)`;       (* procedures           *)

(* Simple variable assignment *)
val Assign_def =
 Define
  `Assign v e = GenAssign v (INL e)`;

(* Array assignment *)
val ArrayAssign_def =
 Define
  `ArrayAssign v e1 e2 =  GenAssign v (INR(ArrUpdate (ArrVar v) e1 e2))`;

(* Multiple local variables *)
val Locals_def =
 Define
  `(Locals [] c = c) /\
   (Locals (v::vl) c = Local v (Locals vl c))`;

(* Some rather crude overloadings to improve the concrete syntax *)

val _ = overload_on ("V", ``Var``);
val _ = overload_on ("C", ``Const``);

val _ = overload_on ("+", ``Plus``);
val _ = overload_on ("-", ``Sub``);
val _ = overload_on ("*", ``Times``);
val _ = overload_on ("/", ``Div``);

val _ = overload_on ("=", ``Equal``);
val _ = overload_on ("<", ``Less``);
val _ = overload_on ("<=", ``LessEq``);
val _ = overload_on (">", ``Greater``);
val _ = overload_on (">=", ``GreaterEq``);

val _ = overload_on ("~", ``Not``);
val _ = overload_on ("/\\", ``And``);
val _ = overload_on ("\\/", ``Or``);

val _ = overload_on ("COND", ``Cond:bexp->program->program->program``);

val _ = overload_on ("::=", ``Assign``);
val _ = set_fixity "::=" (Infixr 280);

val _ = overload_on (";;", ``Seq``);
val _ = set_fixity ";;" (Infixr 180);

(*---------------------------------------------------------------------------*)
(* Big-step operational semantics specified by an inductive relation.        *)
(*                                                                           *)
(*   EVAL : program -> state -> state -> bool                                *)
(*                                                                           *)
(* is defined inductively such that                                          *)
(*                                                                           *)
(*   EVAL c s1 s2                                                            *)
(*                                                                           *)
(* holds exactly when executing the command c in the initial state s1        *)
(* terminates in the final state s2. The evaluation relation is defined      *)
(* inductively by the set of rules shown below.                              *)
(*---------------------------------------------------------------------------*)

val (rules,induction,ecases) = Hol_reln
   `(!s. 
      EVAL Skip s s)
 /\ (!s v e. 
      EVAL (GenAssign v e) s (Update v e s))
 /\ (!s v. EVAL (Dispose v) s (s \\ v))
 /\ (!c1 c2 s1 s2 s3. EVAL c1 s1 s2 /\ EVAL c2 s2 s3 
      ==> EVAL (Seq c1 c2) s1 s3)
 /\ (!c1 c2 s1 s2 b.  EVAL c1 s1 s2 /\ beval b s1 
      ==> EVAL (Cond b c1 c2) s1 s2)
 /\ (!c1 c2 s1 s2 b. EVAL c2 s1 s2 /\ ~beval b s1 
      ==> EVAL (Cond b c1 c2) s1 s2)
 /\ (!c s b. ~beval b s 
      ==> EVAL (While b c) s s)
 /\ (!c s1 s2 s3 b.
      EVAL c s1 s2 /\ EVAL (While b c) s2 s3 /\ beval b s1 
      ==> EVAL (While b c) s1 s3)
 /\ (!c s1 s2 v. 
      EVAL c s1 s2 
      ==> EVAL (Local v c) s1 (if v IN FDOM s1 
                                then s2|+(v, (s1 ' v)) 
                                else s2 \\ v))
 /\ (!s1 s2 f. (f s1 = RESULT s2) ==> EVAL (Proc f) s1 s2)`;

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
(* rules are driven 'backwards', inferring premisses from conclusions.  *)
(* =====================================================================*)

val SKIP_THM = store_thm
("SKIP_THM",
 ``!s1 s2. EVAL Skip s1 s2 = (s1 = s2)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val SKIP = store_thm
("SKIP",
 ``!s. EVAL Skip s s``,
 METIS_TAC rulel);

val GEN_ASSIGN_THM = store_thm 
("GEN_ASSIGN_THM",
 ``!s1 s2 v e. EVAL (GenAssign v e) s1 s2 = (s2 = Update v e s1)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val GEN_ASSIGN = store_thm 
("GEN_ASSIGN",
 ``!s v e. EVAL (GenAssign v e) s (Update v e s)``,
 METIS_TAC rulel);

val ASSIGN = store_thm 
("ASSIGN",
 ``!s v e. EVAL (Assign v e) s (Update v (INL e) s)``,
 RW_TAC std_ss [Assign_def] THEN METIS_TAC rulel);

val ARRAY_ASSIGN = store_thm 
("ARRAY_ASSIGN",
 ``!s v e1 e2. 
    EVAL (ArrayAssign v e1 e2) s (Update v (INR(ArrUpdate (ArrVar v) e1 e2)) s)``,
 RW_TAC std_ss [ArrayAssign_def] THEN METIS_TAC rulel);

val DISPOSE_THM = store_thm 
("DISPOSE_THM",
 ``!s1 s2 v. EVAL (Dispose v) s1 s2 = (s2 = s1 \\ v)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

val DISPOSE = store_thm 
("DISPOSE",
 ``!s v. EVAL (Dispose v) s (s \\ v)``,
 METIS_TAC rulel);

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

val IF_THM =
 store_thm
  ("IF_THM",
   ``!s1 s2 b s1 s2.
       EVAL (Cond b c1 c2) s1 s2 =
        if beval b s1 then EVAL c1 s1 s2 else EVAL c2 s1 s2``,
   METIS_TAC[IF_T_THM,IF_F_THM]);

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

val WHILE_THM = store_thm 
("WHILE_THM",
 ``!s1 s3 b c.
     EVAL (While b c) s1 s3 = 
      if beval b s1 
       then ?s2. EVAL c s1 s2 /\ EVAL (While b c) s2 s3
       else (s1 = s3)``,
 METIS_TAC[WHILE_T_THM,WHILE_F_THM]);

val LOCAL_THM = store_thm
 ("LOCAL_THM",
  ``!s1 s2 v c. 
     EVAL (Local v c) s1 s2 = 
      ?s3. EVAL c s1 s3 
           /\ 
           (s2 = if v IN FDOM s1 then s3 |+ (v, (s1 ' v)) else s3 \\ v)``,
 RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC(FUPDATE_EQ:: rulel));

val PROC_THM = store_thm
 ("PROC_THM",
  ``!f s1 s2 . EVAL (Proc f) s1 s2 = (f s1 = RESULT s2)``,
  RW_TAC std_ss [EQ_IMP_THM,Once ecases] THEN METIS_TAC rulel);

(* Semantic associativity of sequencing *)
val SEQ_ASSOC =
 store_thm
  ("SEQ_ASSOC",
   ``!c1 c2 c3 s1 s2. 
      EVAL (Seq (Seq c1 c2) c3) s1 s2 = EVAL (Seq c1 (Seq c2 c3)) s1 s2``,
   RW_TAC std_ss [SEQ_THM]
    THEN METIS_TAC[]); (* METIS does the whole proof, but is slower *)

(*---------------------------------------------------------------------------*)
(* Theorem: the big-step operational semantics is deterministic.             *)
(*                                                                           *)
(* Given the suite of theorems proved above, this proof is relatively        *)
(* straightforward.  The standard proof is by structural induction on c, but *)
(* the proof by rule induction given below gives rise to a slightly easier   *)
(* analysis in each case of the induction.  There are, however, more         *)
(* cases - one per rule - rather than one per constructor.                   *)
(*---------------------------------------------------------------------------*)

val EVAL_DETERMINISTIC = store_thm 
("EVAL_DETERMINISTIC",
 ``!c st1 st2. EVAL c st1 st2 ==> !st3. EVAL c st1 st3 ==> (st2 = st3)``,
 HO_MATCH_MP_TAC induction THEN 
 RW_TAC std_ss [SKIP_THM,GEN_ASSIGN_THM,DISPOSE_THM,SEQ_THM,
                IF_T_THM,IF_F_THM,WHILE_T_THM, 
                WHILE_F_THM,LOCAL_THM,PROC_THM] THEN 
 METIS_TAC[]);

(* Corollary used later *)
val IMP_EVAL_DETERMINISTIC =
 store_thm
  ("IMP_EVAL_DETERMINISTIC",
   ``!c st1 st2 p.
      (p st1 ==> EVAL c st1 st2) ==> !st3. EVAL c st1 st3 ==> p st1 ==> (st2 = st3)``,
   METIS_TAC[EVAL_DETERMINISTIC]);

(*---------------------------------------------------------------------------*)
(* Definition of Floyd-Hoare logic judgements for partial correctness and    *)
(* derivation of proof rules.                                                *)
(*---------------------------------------------------------------------------*)

val SPEC_def = 
 Define 
   `SPEC P c Q = !s1 s2. P s1 /\ EVAL c s1 s2 ==> Q s2`;

(*---------------------------------------------------------------------------*)
(* Definition of VDM-like Floyd-Hoare logic judgements for partial           *)
(* where the postcondition is a relation between initial and final starts    *)
(*---------------------------------------------------------------------------*)

val RSPEC_def = 
 Define 
   `RSPEC P c R = !s1 s2. P s1 /\ EVAL c s1 s2 ==> R s1 s2`;

(* Corollary used later *)
val EVAL_RSPEC =
 store_thm
  ("EVAL_RSPEC",
   ``!A c f.
      (!s. A s ==> EVAL c s (f s))
      ==>
      !P R.
       (!s. (P s ==> A s) /\ (A s ==> R s (f s))) ==> RSPEC P c R``,
   METIS_TAC[EVAL_DETERMINISTIC,RSPEC_def]);

(*---------------------------------------------------------------------------*)
(* Auxiliary definitions for composing correctness judgements                *)
(*---------------------------------------------------------------------------*)
val IMP_def =
 Define
  `IMP pre post = \prog. RSPEC pre prog post`;

val AND_def =
 Define
  `AND spec1 spec2 = \prog. spec1 prog /\ spec2 prog`;

(*---------------------------------------------------------------------------*)
(* Skip rule                                                                 *)
(*---------------------------------------------------------------------------*)

val SKIP_RULE = store_thm
("SKIP_RULE",
 ``!P. SPEC P Skip P``,
 RW_TAC std_ss [SPEC_def,SKIP_THM]);

(*---------------------------------------------------------------------------*)
(* Dispose rule                                                              *)
(*---------------------------------------------------------------------------*)

val DISPOSE_RULE = store_thm
("DISPOSE_RULE",
 ``!P v e.
      SPEC (\s. P (s \\ v)) (Dispose v) P``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC [DISPOSE_THM]);

(*---------------------------------------------------------------------------*)
(* Assignment rule                                                           *)
(*---------------------------------------------------------------------------*)

val GEN_ASSIGN_RULE = store_thm
("GEN_ASSIGN_RULE",
 ``!P v e.
      SPEC (P o Update v e) (GenAssign v e) P``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC [GEN_ASSIGN_THM]);

(*---------------------------------------------------------------------------*)
(* Dispose rule                                                              *)
(*---------------------------------------------------------------------------*)

val DISPOSE_RULE = store_thm
("DISPOSE_RULE",
 ``!P v.
      SPEC (\s. P (s \\ v)) (Dispose v) P``,
 RW_TAC std_ss [SPEC_def] THEN METIS_TAC [DISPOSE_THM]);

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

local

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

in

val WHILE_RULE = store_thm
("WHILE_RULE",
 ``!P b c. SPEC (\s. P(s) /\ beval b s) c P ==>
           SPEC P (While b c) (\s. P s /\ ~beval b s)``,
 RW_TAC std_ss [SPEC_def] THENL [METIS_TAC[lemma2],METIS_TAC[lemma1]])

end;

(*---------------------------------------------------------------------------*)
(* Local rule                                                                *)
(*---------------------------------------------------------------------------*)

val INDEPENDENT_def =
 Define
  `INDEPENDENT P v = !s. P s = P(s \\ v)`;

val LOCAL_RULE = store_thm
("LOCAL_RULE",
 ``!P Q c v. 
    SPEC P c Q /\ INDEPENDENT Q v
    ==> 
    SPEC P (Local v c) Q``,
 RW_TAC std_ss [SPEC_def]
  THEN FULL_SIMP_TAC std_ss [LOCAL_THM]
  THEN RW_TAC std_ss [FUPDATE_EQ]
  THEN METIS_TAC[DOMSUB_FUPDATE,INDEPENDENT_def]);

(*---------------------------------------------------------------------------*)
(* Proc rule                                                                 *)
(*---------------------------------------------------------------------------*)

val PROC_RULE = store_thm
("PROC_RULE",
 ``!P Q f. 
    (!s1. P s1 ==> ?s2. (f s1 = RESULT s2) /\ Q s2) ==> SPEC P (Proc f) Q``,
 RW_TAC std_ss [SPEC_def,PROC_THM] 
  THEN METIS_TAC [outcome_11]);


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

(*===========================================================================*)
(* End of HOL/examples/ind_def/opsemScript.sml                               *)
(*===========================================================================*)

(* ========================================================================= *)
(*  TOTAL-CORRECTNESS HOARE TRIPLES                                          *)
(* ========================================================================= *)

val TOTAL_SPEC_def = Define `
  TOTAL_SPEC p c q = SPEC p c q /\ !s1. p s1 ==> ?s2. EVAL c s1 s2`;

val TOTAL_SKIP_RULE = store_thm("TOTAL_SKIP_RULE",
  ``!P. TOTAL_SPEC P Skip P``,
  SIMP_TAC std_ss [TOTAL_SPEC_def,SKIP_RULE] THEN REPEAT STRIP_TAC 
  THEN Q.EXISTS_TAC `s1` THEN REWRITE_TAC [rules]);

val TOTAL_GEN_ASSIGN_RULE = store_thm("TOTAL_GEN_ASSIGN_RULE",
  ``!P v e. TOTAL_SPEC (P o Update v e) (GenAssign v e) P``,
  SIMP_TAC std_ss [TOTAL_SPEC_def,GEN_ASSIGN_RULE] THEN REPEAT STRIP_TAC 
  THEN Q.EXISTS_TAC `Update v e s1` THEN REWRITE_TAC [rules]);

val TOTAL_SEQ_RULE = store_thm("TOTAL_SEQ_RULE",
  ``!P c1 c2 Q R. TOTAL_SPEC P c1 Q /\ TOTAL_SPEC Q c2 R ==> 
                  TOTAL_SPEC P (Seq c1 c2) R``,
  REWRITE_TAC [TOTAL_SPEC_def] THEN REPEAT STRIP_TAC
  THEN1 (MATCH_MP_TAC SEQ_RULE THEN Q.EXISTS_TAC `Q` THEN ASM_REWRITE_TAC [])
  THEN FULL_SIMP_TAC bool_ss [SEQ_THM,SPEC_def]
  THEN RES_TAC THEN RES_TAC THEN METIS_TAC []);

val TOTAL_COND_RULE = store_thm("TOTAL_COND_RULE",
  ``!P b c1 c2 Q.
      TOTAL_SPEC (\s. P s /\ beval b s) c1 Q /\
      TOTAL_SPEC (\s. P s /\ ~beval b s) c2 Q ==>
      TOTAL_SPEC P (Cond b c1 c2) Q``,
  REWRITE_TAC [TOTAL_SPEC_def] THEN REPEAT STRIP_TAC
  THEN1 (MATCH_MP_TAC COND_RULE THEN ASM_REWRITE_TAC [])
  THEN FULL_SIMP_TAC std_ss []
  THEN Cases_on `beval b s1` THEN RES_TAC 
  THEN IMP_RES_TAC IF_T_THM THEN IMP_RES_TAC IF_F_THM
  THEN Q.EXISTS_TAC `s2` THEN ASM_REWRITE_TAC []);

val TOTAL_WHILE_F_THM = store_thm("TOTAL_WHILE_F_THM",
  ``!P b c. TOTAL_SPEC (\s. P s /\ ~beval b s) (While b c) P``,
  SIMP_TAC std_ss [TOTAL_SPEC_def,SPEC_def,GSYM AND_IMP_INTRO]
  THEN ONCE_REWRITE_TAC [WHILE_THM] THEN SIMP_TAC std_ss []);

val TOTAL_WHILE_T_THM = store_thm("TOTAL_WHILE_T_THM",
  ``!P b c M Q.
      TOTAL_SPEC (\s. P s /\ beval b s) c M /\ TOTAL_SPEC M (While b c) Q ==>
      TOTAL_SPEC (\s. P s /\ beval b s) (While b c) Q``,
  SIMP_TAC std_ss [TOTAL_SPEC_def,SPEC_def] THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [WHILE_THM] THEN ASM_REWRITE_TAC []
  THEN RES_TAC THEN RES_TAC THEN METIS_TAC [WHILE_THM]);

val TOTAL_GEN_ASSIGN_THM = store_thm("TOTAL_GEN_ASSIGN_THM",
  ``!P c v e Q. SPEC P (GenAssign v e) Q = TOTAL_SPEC P (GenAssign v e) Q``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [TOTAL_SPEC_def] 
  THEN REPEAT STRIP_TAC 
  THEN Q.EXISTS_TAC `Update v e s1` THEN REWRITE_TAC [rules]);


(*===========================================================================*)
(* Small-step semantics based on Collavizza et al. paper                     *)
(*===========================================================================*)

val (small_rules,small_induction,small_ecases) = Hol_reln
   `(!s l. 
      SMALL_EVAL (Skip :: l, s) (l, s))
 /\ (!s v e l. 
      SMALL_EVAL (GenAssign v e :: l, s) (l, Update v e s))
 /\ (!s v l. 
      SMALL_EVAL (Dispose v :: l, s) (l, s \\ v))
 /\ (!s l c1 c2. 
      SMALL_EVAL (Seq c1 c2 :: l, s) (c1 :: c2 :: l, s))
 /\ (!s l b c1 c2.  
      beval b s 
      ==> 
      SMALL_EVAL (Cond b c1 c2 :: l, s) (c1 :: l, s))
 /\ (!s l b c1 c2.  
      ~(beval b s)
      ==> 
      SMALL_EVAL (Cond b c1 c2 :: l, s) (c2 :: l, s))
 /\ (!s l b c.  
      beval b s 
      ==> 
      SMALL_EVAL (While b c :: l, s) (c :: While b c :: l, s))
 /\ (!s l b c.  
      ~(beval b s )
      ==> 
      SMALL_EVAL (While b c :: l, s) (l, s))
 /\ (!s l v c.
      v IN FDOM s
      ==>
      SMALL_EVAL 
       (Local v c :: l, s) 
       (c :: GenAssign v (Exp(s ' v)) :: l, s))
 /\ (!s l v c.
      ~(v IN FDOM s)
      ==>
      SMALL_EVAL (Local v c :: l, s) (c :: Dispose v :: l, s))
 /\ (!s1 s2 l f. 
      (f s1 = RESULT s2)
      ==> 
      SMALL_EVAL (Proc f :: l, s1) (l, s2))`;

val small_rulel = CONJUNCTS small_rules;

val SMALL_SKIP_THM = store_thm
("SMALL_SKIP_THM",
 ``!s1 s2 l1 l2. 
    SMALL_EVAL (Skip :: l1, s1) (l2, s2) = 
     (l2 = l1) /\ (s2 = s1)``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_GEN_ASSIGN_THM = store_thm 
("SMALL_GEN_ASSIGN_THM",
 ``!s1 s2 l1 l2 v e. 
    SMALL_EVAL (GenAssign v e :: l1, s1) (l2, s2) = 
     (l2 = l1) /\ (s2 = Update v e s1)``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_DISPOSE_THM = store_thm 
("SMALL_DISPOSE_THM",
 ``!s1 s2 l1 l2 v. 
    SMALL_EVAL (Dispose v :: l1, s1) (l2, s2) = 
     (l2 = l1) /\ (s2 = s1 \\ v)``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_SEQ_THM = store_thm
("SMALL_SEQ_THM",
 ``!s1 s3 l1 l3 c1 c2. 
    SMALL_EVAL (Seq c1 c2 :: l1, s1) (l2, s2) = 
     (l2 = c1 :: c2 :: l1) /\ (s2 = s1)``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_IF_T_THM = store_thm 
("SMALL_IF_T_THM",
 ``!s1 s2 l1 l2 b c1 c2. 
     beval b s1
     ==> 
     (SMALL_EVAL (Cond b c1 c2 :: l1, s1) (l2, s2) = 
      (l2 = c1 :: l1) /\ (s2 = s1))``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_IF_F_THM = store_thm 
("SMALL_IF_F_THM",
 ``!s1 s2 l1 l2 b c1 c2. 
     ~(beval b s1)
     ==> 
     (SMALL_EVAL (Cond b c1 c2 :: l1, s1) (l2, s2) = 
      (l2 = c2 :: l1) /\ (s2 = s1))``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_IF_THM = store_thm 
("SMALL_IF_THM",
 ``!s1 s2 l1 l2 b c1 c2. 
     SMALL_EVAL (Cond b c1 c2 :: l1, s1) (l2, s2) = 
      (l2 = (if beval b s1 then c1 else c2) :: l1) /\ (s2 = s1)``,
 METIS_TAC[SMALL_IF_T_THM,SMALL_IF_F_THM]);

val SMALL_WHILE_T_THM = store_thm 
("SMALL_WHILE_T_THM",
 ``!s1 s2 l1 l2 b c.
    beval b s1
    ==> 
    (SMALL_EVAL (While b c :: l1, s1) (l2, s2) = 
    (l2 = c :: While b c :: l1) /\ (s2 = s1))``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_WHILE_F_THM = store_thm 
("SMALL_WHILE_F_THM",
 ``!s1 s2 l1 l2 b c.
    ~(beval b s1)    ==> 
    (SMALL_EVAL (While b c :: l1, s1) (l2, s2) = 
    (l2 = l1) /\ (s2 = s1))``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC small_rulel);

val SMALL_WHILE_THM = store_thm 
("SMALL_WHILE_THM",
 ``!s1 s2 l1 l2 b c.
    SMALL_EVAL (While b c :: l1, s1) (l2, s2) = 
    (l2 = if beval b s1 then c :: While b c :: l1 else l1) /\ (s2 = s1)``,
 METIS_TAC[SMALL_WHILE_T_THM,SMALL_WHILE_F_THM]);

val SMALL_LOCAL_IN_THM = store_thm
 ("SMALL_LOCAL_IN_THM",
  ``!s1 s2 l1 l2 v c. 
     v IN FDOM s1
     ==>
     (SMALL_EVAL (Local v c :: l1, s1) (l2, s2) = 
       (l2 = c :: GenAssign v (Exp(s1 ' v)) :: l1)
       /\ 
       (s2 = s1))``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC(FUPDATE_EQ:: small_rulel));

val SMALL_LOCAL_NOT_IN_THM = store_thm
 ("SMALL_LOCAL_NOT_IN_THM",
  ``!s1 s2 l1 l2 v c. 
     ~(v IN FDOM s1)
     ==>
     (SMALL_EVAL (Local v c :: l1, s1) (l2, s2) = 
       (l2 = c :: Dispose v :: l1)
       /\ 
       (s2 = s1))``,
 RW_TAC std_ss [EQ_IMP_THM,Once small_ecases] THEN METIS_TAC(FUPDATE_EQ:: small_rulel));

val SMALL_LOCAL_THM = store_thm
 ("SMALL_LOCAL_THM",
  ``!s1 s2 l1 l2 v c. 
     SMALL_EVAL (Local v c :: l1, s1) (l2, s2) = 
      (l2 = c :: (if v IN FDOM s1 
                   then GenAssign v (Exp(s1 ' v)) 
                   else Dispose v) :: l1)
      /\ 
      (s2 = s1)``,
 METIS_TAC[SMALL_LOCAL_IN_THM,SMALL_LOCAL_NOT_IN_THM]);

val SMALL_PROC_THM = store_thm
 ("SMALL_PROC_THM",
  ``!s1 s2 l1 l2 f. 
     SMALL_EVAL (Proc f :: l1, s1) (l2, s2) = (f s1 = RESULT s2) /\ (l2 = l1)``,
  ONCE_REWRITE_TAC[small_ecases]
   THEN SIMP_TAC (srw_ss()) []
   THEN METIS_TAC[]);

val EVAL_IMP_SMALL_EVAL_LEMMA =
 store_thm
  ("EVAL_IMP_SMALL_EVAL_LEMMA",
   ``!c s1 s2. 
      EVAL c s1 s2 
      ==>
      (\c s1 s2. !l. TC SMALL_EVAL (c :: l, s1) (l, s2)) c s1 s2``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (rules,induction))
    THEN RW_TAC std_ss (TC_RULES :: small_rulel)
    THENL
     [METIS_TAC[SMALL_SEQ_THM,TC_RULES],     (* Seq *)
      METIS_TAC[SMALL_IF_T_THM,TC_RULES],    (* Cond true *)
      METIS_TAC[SMALL_IF_F_THM,TC_RULES],    (* Cond false *)
      METIS_TAC[SMALL_WHILE_T_THM,TC_RULES], (* While true *)
      IMP_RES_TAC small_rules                (* Local IN FDOM *)
       THEN `!l. TC SMALL_EVAL 
                  (c::GenAssign v (Exp(s1 ' v))::l,s1) 
                  (GenAssign v (Exp(s1 ' v))::l,s2)`
             by METIS_TAC[]
       THEN `!l. TC SMALL_EVAL 
                  (GenAssign v (Exp(s1 ' v))::l,s2) 
                  (l, s2 |+ (v,s1 ' v))`
             by METIS_TAC[small_rules,TC_RULES,neval_def,Update_Exp]
       THEN METIS_TAC [TC_RULES],
      METIS_TAC                              (* Local not IN FDOM *)
       [SMALL_LOCAL_NOT_IN_THM,SMALL_DISPOSE_THM,TC_RULES]]);

val EVAL_IMP_SMALL_EVAL =
 store_thm
  ("EVAL_IMP_SMALL_EVAL",
   ``!c s1 s2. EVAL c s1 s2 ==>TC SMALL_EVAL ([c], s1) ([], s2)``,
   METIS_TAC[EVAL_IMP_SMALL_EVAL_LEMMA]);

val SMALL_EVAL_NIL_LEMMA =
 store_thm
  ("SMALL_EVAL_NIL_LEMMA",
   ``!con1  con2.
      SMALL_EVAL con1 con2
      ==>
      (\con1 con2. ~(FST con1 = [])) con1 con2``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (small_rules,small_induction))
    THEN RW_TAC std_ss small_rulel);

val SMALL_EVAL_NIL =
 store_thm
  ("SMALL_EVAL_NIL",
   ``!s con. ~(SMALL_EVAL ([],s) con)``,
   METIS_TAC[pairTheory.FST,SMALL_EVAL_NIL_LEMMA]);

val TC_SMALL_EVAL_NIL_LEMMA =
 store_thm
  ("TC_SMALL_EVAL_NIL_LEMMA",
   ``!con1 con2. 
       TC SMALL_EVAL con1 con2 
       ==> 
       (\con1 con2. ~(FST con1 = [])) con1 con2``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (TC_RULES,TC_INDUCT))
    THEN RW_TAC std_ss [SMALL_EVAL_NIL_LEMMA]);

val TC_SMALL_EVAL_NIL =
 store_thm
  ("TC_SMALL_EVAL_NIL",
   ``!s con. ~(TC SMALL_EVAL ([],s) con)``,
   METIS_TAC[pairTheory.FST,TC_SMALL_EVAL_NIL_LEMMA]);

(* Seql[c1;c2;...;cn]  =  Seq c1 (Seq c2 ... (Seq cn Skip) ... ) *)
val Seql_def =
 Define
  `(Seql [] = Skip)
   /\
   (Seql (c :: l) = Seq c (Seql l))`;

(* http://www4.informatik.tu-muenchen.de/~nipkow/pubs/fac98.html *)
val RANAN_FRAER_LEMMA =
 store_thm
  ("RANAN_FRAER_LEMMA",
   ``!con1 con2.
     SMALL_EVAL con1 con2
     ==>
     (\con1 con2. 
       !s. EVAL (Seql(FST con2)) (SND con2) s
           ==>
           EVAL (Seql(FST con1)) (SND con1) s) con1 con2``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (small_rules,small_induction))
    THEN RW_TAC list_ss 
          [neval_def,Seql_def,Update_Exp,
           SKIP_THM,GEN_ASSIGN_THM,DISPOSE_THM,SEQ_THM,IF_THM,LOCAL_THM,PROC_THM]
    THEN TRY(METIS_TAC[WHILE_THM]));

val SMALL_EVAL_IMP_EVAL_LEMMA =
 store_thm
  ("SMALL_EVAL_IMP_EVAL_LEMMA",
   ``!con1 con2.
      TC SMALL_EVAL con1 con2 
      ==>
      (\con1 con2.
        !s. EVAL (Seql(FST con2)) (SND con2) s 
            ==> 
            EVAL (Seql(FST con1)) (SND con1) s) con1 con2``,
  IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (TC_RULES,TC_INDUCT))
    THEN RW_TAC std_ss []
    THEN METIS_TAC[RANAN_FRAER_LEMMA]);

val SMALL_EVAL_IMP_EVAL =
 store_thm
  ("SMALL_EVAL_IMP_EVAL",
   ``!c s1 s2. TC SMALL_EVAL ([c], s1) ([],s2) ==> EVAL c s1 s2``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC SMALL_EVAL_IMP_EVAL_LEMMA
    THEN FULL_SIMP_TAC list_ss [Seql_def,SEQ_THM,SKIP_THM]);

val EVAL_SMALL_EVAL =
 store_thm
  ("EVAL_SMALL_EVAL",
   ``!c s1 s2. EVAL c s1 s2 = TC SMALL_EVAL ([c], s1) ([],s2)``,
   METIS_TAC[EVAL_IMP_SMALL_EVAL,SMALL_EVAL_IMP_EVAL]); 

(* Technical theorem to make EVAL work with lists for executing STEP_LIST *)
val CONS_if =
 store_thm
  ("CONS_if",
   ``x :: (if b then l1 else l2) = if b then x :: l1 else x :: l2``,
   METIS_TAC[]);

(* Technical theorem to make EVAL work with output from SYMBOLIC_EVAL_PROVE *)
val ScalarOf_if =
 store_thm
  ("ScalarOf_if",
   ``ScalarOf((if b then s1 else s2) ' x) = 
      if b then ScalarOf(s1 ' x) else ScalarOf(s2 ' x)``,
   METIS_TAC[]);

(* More technical theorems for use with EVAL and the simplifier *)

val ScalarOfIf =
 store_thm
  ("ScalarOfIf",
   ``ScalarOf(if b then x else y) = if b then ScalarOf x else ScalarOf y``,
   METIS_TAC[]);

val ScalarIf =
 store_thm
  ("ScalarIf",
   ``Scalar(if b then x else y) = if b then Scalar x else Scalar y``,
   METIS_TAC[]);

val EqLeftIf =
 store_thm
  ("EqLeftIf",
   ``(c = if b then x else y) = if b then c = x else c = y``,
   METIS_TAC[]);

val EqRightIf =
 store_thm
  ("EqRightIf",
   ``((if b then x else y) = c) = if b then x = c else y = c``,
   METIS_TAC[]);

val _ = computeLib.add_persistent_funs
         [("ScalarOfIf",     ScalarOfIf),
          ("ScalarIf",       ScalarIf),
          ("EqLeftIf",       EqLeftIf),
          ("EqRightIf",      EqRightIf)];

(* Replaced by more general code below (will eventually be deleted)
val int_addLeftIf =
 store_thm
  ("int_addLeftIf",
   ``(n int_add (if b then x else y)) = if b then n int_add x else n int_add y``,
   METIS_TAC[]);

val int_addRightIf =
 store_thm
  ("int_addRightIf",
   ``((if b then x else y) int_add n) = if b then x int_add n else y int_add n``,
   METIS_TAC[]);

val int_subLeftIf =
 store_thm
  ("int_subLeftIf",
   ``(n int_sub (if b then x else y)) = if b then n int_sub x else n int_sub y``,
   METIS_TAC[]);

val int_subRightIf =
 store_thm
  ("int_subRightIf",
   ``((if b then x else y) int_sub n) = if b then x int_sub n else y int_sub n``,
   METIS_TAC[]);

val int_gtLeftIf =
 store_thm
  ("int_gtLeftIf",
   ``(n int_gt (if b then x else y)) = if b then n int_gt x else n int_gt y``,
   METIS_TAC[]);

val int_gtRightIf =
 store_thm
  ("int_gtRightIf",
   ``((if b then x else y) int_gt n) = if b then x int_gt n else y int_gt n``,
   METIS_TAC[]);

val _ = computeLib.add_persistent_funs
         [("int_addLeftIf",  int_addLeftIf),
          ("int_addRightIf", int_addRightIf),
          ("int_subLeftIf",  int_subLeftIf),
          ("int_subRightIf", int_subRightIf)
         ];
*)

val int_opLeftIf =
 store_thm
  ("int_opLeftIf",
   ``!(f:int->int->int). f n (if b then x else y) = if b then f n x else f n y``,
   METIS_TAC[]);

val int_opRightIf =
 store_thm
  ("int_opRightIf",
   ``!(f:int->int->int). f (if b then x else y) n = if b then f x n else f y n``,
   METIS_TAC[]);

val int_relLeftIf =
 store_thm
  ("int_relLeftIf",
   ``!(r:int->int->bool). r n (if b then x else y) = if b then r n x else r n y``,
   METIS_TAC[]);

val int_relRightIf =
 store_thm
  ("int_relRightIf",
   ``!(r:int->int->bool). r (if b then x else y) n = if b then r x n else r y n``,
   METIS_TAC[]);

val _ = 
  (map
    (fn con => 
      (save_thm ((fst(dest_const con) ^ "LeftIf"),   SPEC con int_opLeftIf);
       save_thm ((fst(dest_const con) ^ "RightIf"),  SPEC con int_opRightIf);
       computeLib.add_persistent_funs
        [((fst(dest_const con) ^ "LeftIf"),   SPEC con int_opLeftIf),
         ((fst(dest_const con) ^ "RightIf"),  SPEC con int_opRightIf)]))
    [``$int_add``,``$int_sub``]);

val _ = 
  (map
    (fn con => 
      (save_thm ((fst(dest_const con) ^ "LeftIf"),   SPEC con int_relLeftIf);
       save_thm ((fst(dest_const con) ^ "RightIf"),  SPEC con int_relRightIf);
       computeLib.add_persistent_funs
        [((fst(dest_const con) ^ "LeftIf"),   SPEC con int_relLeftIf),
         ((fst(dest_const con) ^ "RightIf"),  SPEC con int_relRightIf)]))
    [``$int_lt``,``$int_le``,``$int_gt``,``$int_ge``]);


(* Monad binding operation *)
val RUN_BIND_def =
 Define 
  `RUN_BIND m f = case m of
                     TIMEOUT s -> TIMEOUT s
                  || ERROR s   -> ERROR s
                  || RESULT s  -> f s`;

val _ = set_fixity ">>=" (Infixl 430);
val _ = overload_on (">>=", ``RUN_BIND``);

(* Monad unit function *)
val RUN_RETURN_def =
 Define 
  `RUN_RETURN x = RESULT x`;

val outcome_ss = srw_ss();    (* simplification set that knows about outcome *)

val RUN_MONAD_LAWS =
 store_thm
  ("RUN_MONAD_LAWS",
   ``((RUN_RETURN x) >>= f  =  f x)
     /\
     (m >>= RUN_RETURN  =  m)
     /\
     ((m >>= f) >>= g  =  m >>= (\x. (f x) >>= g))``,
   RW_TAC std_ss [RUN_BIND_def, RUN_RETURN_def]
    THEN Cases_on `m`
    THEN RW_TAC outcome_ss []);

val RUN_BIND_RUN_RETURN_def =
 Define
  `RUN_BIND_RUN_RETURN m f = m >>= (RUN_RETURN o f)`;

val RUN_BIND_RUN_RETURN =
 store_thm
  ("RUN_BIND_RUN_RETURN",
   ``RUN_BIND_RUN_RETURN m f =
      case m of
         TIMEOUT s -> TIMEOUT s
      || ERROR s   -> ERROR s
      || RESULT s  -> RESULT(f s)``,
   RW_TAC std_ss [RUN_BIND_RUN_RETURN_def,RUN_BIND_def,RUN_RETURN_def]);

(* Add to EVAL compset *)
val _ = computeLib.add_persistent_funs[("CONS_if",CONS_if)];

(* Technical theorems to make ML EVAL work with outcomes *)

val outcome_case_def =
 prove
  (``(!f f1 f2 a. outcome_case f f1 f2 (RESULT a) = f a) /\
     (!f f1 f2 a. outcome_case f f1 f2 (ERROR a) = f1 a) /\
     (!f f1 f2 a. outcome_case f f1 f2 (TIMEOUT a) = f2 a)``,
   RW_TAC outcome_ss []);

val outcome_case_if =
 store_thm
  ("outcome_case_if",
   ``!f f1 f2 b x y.
      outcome_case f f1 f2 (if b then x else y) = 
      if b then outcome_case f f1 f2 x else outcome_case f f1 f2 y``,
   RW_TAC std_ss []);

val pair_case_if =
 store_thm
  ("pair_case_if",
   ``!f b x y.
      pair_case f (if b then x else y) = 
      if b then f (FST x) (SND x) else f (FST y) (SND y)``,
   RW_TAC std_ss []
    THENL
     [Cases_on `x`
       THEN RW_TAC std_ss [],
      Cases_on `y`
       THEN RW_TAC std_ss []]);

(* Add to EVAL compset *)
val _ = computeLib.add_persistent_funs
         [("outcome_case_def",outcome_case_def),
          ("outcome_case_if",outcome_case_if),
          ("pair_case_if",pair_case_if)
         ];

(*===========================================================================*)
(* Clocked big step evaluator                                                *)
(*===========================================================================*)

(* Definition of RUN -- note use of monads to propagate outcomes *)
val RUN_def =
 Define
  `(RUN 0 c s = TIMEOUT s)
   /\  
   (RUN (SUC n) c s =
    case c of
        Skip          -> RESULT s
     || GenAssign v e -> RESULT(Update v e s)
     || Dispose v     -> RESULT(s \\ v)
     || Seq c1 c2     -> RUN n c1 s >>= RUN n c2
     || Cond b c1 c2  -> if beval b s
                          then RUN n c1 s
                          else RUN n c2 s
     || While b c     -> if beval b s 
                          then RUN n c s >>= RUN n (While b c) 
                          else RESULT s
     || Local v c     -> if v IN FDOM s
                          then RUN n c s >>= (RESULT o (\s'. s' |+ (v, (s ' v))))
                          else RUN n c s >>= (RESULT o (\s'. s' \\ v))
     || Proc f        -> f s
   )`;

(* Lemma needed for EVAL_RUN *)
val RUN_EVAL_LEMMA =
 prove
  (``!n c s1 s2. (RUN n c s1 = RESULT s2) ==> EVAL c s1 s2``,
   Induct
    THEN Cases_on `c`
    THEN RW_TAC std_ss [RUN_def,rules,RUN_BIND_def]
    THEN RW_TAC std_ss [RUN_def,rules,RUN_BIND_def]
    THEN Cases_on `RUN n p s1`
    THEN Cases_on `RUN n p' s1` (* hack for PolyML from Magnus *)
    THEN FULL_SIMP_TAC outcome_ss []
    THEN METIS_TAC[rules]);

(* Lemma needed for EVAL_RUN *)
val EVAL_RUN_LEMMA =
 prove
  (``!c s1 s2. 
      EVAL c s1 s2 
      ==> 
      (\c s1 s2. ?m. !n. m < n ==> (RUN n c s1 = RESULT s2)) c s1 s2``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (rules,induction))
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `0`         (* Skip *)
       THEN RW_TAC arith_ss []
       THEN `?m. n = SUC m` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC `0`         (* GenAssign *)
       THEN RW_TAC arith_ss []
       THEN `?m. n = SUC m` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC `0`         (* Dispose *)
       THEN RW_TAC arith_ss []
       THEN `?m. n = SUC m` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC `SUC(m+m')` (* Seq *)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC(m+m'+p)` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def]
       THEN `m < m+m'+p` by intLib.COOPER_TAC
       THEN `m' < m+m'+p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC `SUC m`     (* Cond - test true *)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC(m+p)` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def]
       THEN `m < m+p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC `SUC m`     (* Cond - test false *)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC(m+p)` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def]
       THEN `m < m+p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC `SUC m`     (* While - test false *)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC(m+p)` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def]
       THEN `m < m+p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC `SUC(m+m')` (* While - test rtue *)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC(m+m'+p)` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def]
       THEN `m < m+m'+p` by intLib.COOPER_TAC
       THEN `m' < m+m'+p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC  `SUC m`    (* Local -  v IN FDOM s1 case*)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC p` by intLib.COOPER_TAC
       THEN `m < p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC  `SUC m`    (* Local - ~(v IN FDOM s1) case*)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC p` by intLib.COOPER_TAC
       THEN `m < p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def],
      Q.EXISTS_TAC  `0`        (* Proc *)
       THEN RW_TAC arith_ss []
       THEN `?p. n = SUC p` by intLib.COOPER_TAC
       THEN RW_TAC std_ss [RUN_def,RUN_BIND_def]
     ]);

(* Correctness of RUN with respect to EVAL *)
val EVAL_RUN =
 store_thm
  ("EVAL_RUN",
   ``!c s1 s2. EVAL c s1 s2 = ?n. RUN n c s1 = RESULT s2``,
   METIS_TAC[DECIDE ``m < SUC m``, RUN_EVAL_LEMMA,EVAL_RUN_LEMMA]);

val SPEC_RUN =
 store_thm
  ("SPEC_RUN",
   ``SPEC P c Q = !s1 s2 n. P s1 /\ (RUN n c s1 = RESULT s2) ==> Q s2``,
   METIS_TAC[SPEC_def,EVAL_RUN]);

(* Corollary relating non-termination and TIMEOUT *)
val NOT_EVAL_RUN =
 store_thm
  ("NOT_EVAL_RUN",
   ``!c s1. ~(?s2. EVAL c s1 s2) = 
      !n. ?s2. (RUN n c s1 = ERROR s2) \/ (RUN n c s1 = TIMEOUT s2)``,
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Cases_on `RUN n c s1`
       THEN METIS_TAC[EVAL_RUN],
      `!x y. ~(RESULT x = ERROR y) /\ ~(RESULT x = TIMEOUT y)` 
       by RW_TAC outcome_ss []
       THEN METIS_TAC[EVAL_RUN]]);

(* Version of RUN for use by the HOL evaluator EVAL *)
val RUN =
 store_thm
  ("RUN",
   ``RUN n c s =
      if n = 0 
       then TIMEOUT(s)
       else
        case c of
            Skip          -> RESULT s
         || GenAssign v e -> RESULT(Update v e s)
         || Dispose v     -> RESULT(s \\ v)
         || Seq c1 c2     -> RUN (n-1) c1 s >>= RUN (n-1) c2
         || Cond b c1 c2  -> if beval b s
                              then RUN (n-1) c1 s
                              else RUN (n-1) c2 s
         || While b c     -> if beval b s 
                              then RUN (n-1) c s >>= RUN (n-1) (While b c)
                              else RESULT s
         || Local v c     -> if v IN FDOM s
                              then RUN (n-1) c s >>= (RESULT o (\s'. s' |+ (v, (s ' v))))
                              else RUN (n-1) c s >>=  (RESULT o (\s'. s' \\ v))
         || Proc f        -> f s``,
   Cases_on `n`
    THEN RW_TAC arith_ss [RUN_def,RUN_BIND_def]);

(* Tell EVAL about RUN and various properties of finite mape *)

val _ = computeLib.add_persistent_funs[("RUN",RUN)];

(* Small step next-state function                                            *)
(*===========================================================================*)

(* Single step *)
val STEP1_def =
 Define
  `(STEP1 ([], s) = ([], ERROR s))
   /\
   (STEP1 (Skip :: l, s) = (l, RESULT s))
   /\ 
   (STEP1 (GenAssign v e :: l, s) = (l, RESULT(Update v e s)))
   /\ 
   (STEP1 (Dispose v :: l, s) = (l, RESULT(s \\ v)))
   /\ 
   (STEP1 (Seq c1 c2 :: l, s) = (c1 :: c2 :: l, RESULT(s)))
   /\ 
   (STEP1 (Cond b c1 c2 :: l, s) = 
     if beval b s 
      then (c1 :: l, RESULT s) 
      else (c2 :: l, RESULT s))
   /\ 
   (STEP1 (While b c :: l, s) = 
     if beval b s 
      then (c :: While b c :: l, RESULT s) 
      else (l, RESULT s))
   /\ 
   (STEP1 (Local v c :: l, s) =
     if v IN FDOM s 
      then (c :: GenAssign v (Exp(s ' v)) :: l, RESULT s)
      else (c :: Dispose v :: l, RESULT s))
   /\ 
   (STEP1 (Proc f :: l, s) = (l, f s))`;

(* Version needed for evaluation by EVAL *)
val STEP1 =
 store_thm
  ("STEP1",
   ``!l s.
      STEP1 (l, s) = 
       if NULL l
        then (l, ERROR s)
        else
        case (HD l) of
            Skip          -> (TL l, RESULT s)
        ||  GenAssign v e -> (TL l, RESULT(Update v e s))
        ||  Dispose v     -> (TL l, RESULT(s \\ v))
        ||  Seq c1 c2     -> (c1 :: c2 :: TL l, RESULT s)
        ||  Cond b c1 c2  -> if beval b s 
                              then (c1 :: TL l, RESULT s) 
                              else (c2 :: TL l, RESULT s)
        ||  While b c     -> if beval b s 
                              then (c :: While b c :: TL l, RESULT s) 
                              else (TL l, RESULT s)
        ||  Local v c     -> if v IN FDOM s 
                              then (c :: GenAssign v (Exp(s ' v)) :: TL l, RESULT s)
                              else (c :: Dispose v :: TL l, RESULT s)
        ||  Proc f        -> (TL l, f s)``,
     Induct
      THEN RW_TAC list_ss [STEP1_def]
      THEN Cases_on `h`
      THEN RW_TAC list_ss [STEP1_def]);

(* Add to EVAL compset *)
val _ = computeLib.add_persistent_funs [("STEP1",STEP1)];

(* Various lemmas follow -- I'm not sure they are all needed *)
val SMALL_EVAL_IMP_STEP1 =
 prove
  (``!con1 con2.
      SMALL_EVAL con1 con2
      ==> 
      (\con1 con2.
       STEP1 con1 = (FST con2, RESULT(SND con2))) con1 con2``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (small_rules,small_induction))
    THEN RW_TAC list_ss [STEP1_def]);

val STEP1_IMP_SMALL_EVAL =
 prove
  (``!c l1 s1 l2 s2.
      (STEP1 (c :: l1, s1) = (l2, RESULT s2))
      ==> 
      SMALL_EVAL (c :: l1, s1) (l2, s2)``,
    Induct
     THEN RW_TAC std_ss 
           [STEP1_def,small_rules,neval_def,
            SMALL_GEN_ASSIGN_THM,SMALL_DISPOSE_THM,SMALL_IF_THM,SMALL_SEQ_THM,
            SMALL_LOCAL_THM,SMALL_PROC_THM]
     THEN METIS_TAC[small_rules]);

val STEP1_SMALL_EVAL =
 store_thm
  ("STEP1_SMALL_EVAL",
   ``!l1 s1 l2 s2.
      (STEP1 (l1, s1) = (l2, RESULT s2))
      = 
      SMALL_EVAL (l1, s1) (l2, s2)``,
   Induct
    THENL
     [RW_TAC outcome_ss [STEP1_def,SMALL_EVAL_NIL],
      METIS_TAC
       [STEP1_IMP_SMALL_EVAL,SMALL_EVAL_IMP_STEP1,
        pairTheory.FST,pairTheory.SND]]);

val NOT_SMALL_EVAL_ERROR =
 store_thm
  ("NOT_SMALL_EVAL_ERROR",
   ``!con1 con2.
      ~(?con2. SMALL_EVAL con1 con2) = 
       ?s. (SND(STEP1 con1 ) = ERROR s) \/ (SND(STEP1 con1 ) = TIMEOUT s)``,
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN Cases_on `con1` THEN TRY(Cases_on `q`) THEN TRY(Cases_on `h`)
    THEN RW_TAC (srw_ss()) [STEP1_def]
    THEN FULL_SIMP_TAC outcome_ss [STEP1_def]
    THEN TRY (METIS_TAC
          [SMALL_SKIP_THM,SMALL_GEN_ASSIGN_THM,SMALL_DISPOSE_THM,SMALL_IF_THM,SMALL_SEQ_THM,
           SMALL_LOCAL_THM,SMALL_PROC_THM,SMALL_WHILE_THM,outcome_distinct,outcome_11,
           pairTheory.SND,COND_RAND,SMALL_EVAL_NIL])
    THEN TRY(Cases_on `con2`)
    THEN TRY(POP_ASSUM(ASSUME_TAC o Q.GEN `l2` o Q.GEN `s2` o Q.SPEC `(l2,s2)`))
    THEN FULL_SIMP_TAC outcome_ss [SMALL_PROC_THM]
    THEN TRY (METIS_TAC
          [SMALL_SKIP_THM,SMALL_GEN_ASSIGN_THM,SMALL_DISPOSE_THM,SMALL_IF_THM,SMALL_SEQ_THM,
           SMALL_LOCAL_THM,SMALL_PROC_THM,SMALL_WHILE_THM,outcome_distinct,outcome_11,
           outcome_nchotomy,pairTheory.SND,COND_RAND,SMALL_EVAL_NIL]));

(* Iterated SMALL_EVAL *)
val SMALL_EVAL_ITER_def =
 Define
  `(SMALL_EVAL_ITER 0 con1 con2 = SMALL_EVAL con1 con2)
   /\
   (SMALL_EVAL_ITER (SUC n) con1 con2 =
     ?con. SMALL_EVAL con1 con /\ SMALL_EVAL_ITER n con con2)`;

(* More convenient version (doesn't introduce ``con``) *)
val SMALL_EVAL_ITER =
 store_thm
  ("SMALL_EVAL_ITER",
   ``(SMALL_EVAL_ITER 0 con1 con2 = SMALL_EVAL con1 con2)
     /\
     (SMALL_EVAL_ITER (SUC n) con1 con2 =
       ?l s. SMALL_EVAL con1 (l,s) /\ SMALL_EVAL_ITER n (l,s) con2)``,
   RW_TAC std_ss [pairTheory.EXISTS_PROD,SMALL_EVAL_ITER_def]);

val SMALL_EVAL_ITER_LEMMA =
 prove
  (``!n1 x y. 
      SMALL_EVAL_ITER n1 x y 
      ==>
      !n2 z. SMALL_EVAL_ITER n2 y z ==> ?n3. SMALL_EVAL_ITER n3 x z``,
   Induct
    THEN METIS_TAC[SMALL_EVAL_ITER_def]);

val SMALL_EVAL_ITER_TC_LEMMA1 =
 prove
  (``!n con1 con2. SMALL_EVAL_ITER n con1 con2 ==> TC SMALL_EVAL con1 con2``,
   Induct
    THEN METIS_TAC[SMALL_EVAL_ITER_def,TC_RULES]);

val SMALL_EVAL_ITER_TC_LEMMA2 =
 prove
  (``!con1 con2. 
      TC SMALL_EVAL con1 con2
      ==> 
      (\con1 con2. ?n. SMALL_EVAL_ITER n con1 con2) con1 con2``,
  IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (TC_RULES,TC_INDUCT))
    THEN RW_TAC std_ss []
    THEN METIS_TAC[SMALL_EVAL_ITER_def,TC_RULES,SMALL_EVAL_ITER_LEMMA]);

val SMALL_EVAL_ITER_TC =
 store_thm
  ("SMALL_EVAL_ITER_TC",
   ``!con1 con2. 
      TC SMALL_EVAL con1 con2 = ?n. SMALL_EVAL_ITER n con1 con2``,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN METIS_TAC[SMALL_EVAL_ITER_TC_LEMMA1,SMALL_EVAL_ITER_TC_LEMMA2,TC_RULES]);

val SMALL_EVAL_ITER_TC =
 store_thm
  ("SMALL_EVAL_ITER_TC",
   ``!con1 con2. 
      TC SMALL_EVAL con1 con2 = ?n. SMALL_EVAL_ITER n con1 con2``,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN METIS_TAC[SMALL_EVAL_ITER_TC_LEMMA1,SMALL_EVAL_ITER_TC_LEMMA2,TC_RULES]);

val SMALL_EVAL_TC_SMALL_EVAL =
 store_thm
  ("SMALL_EVAL_TC_SMALL_EVAL",
   ``!con1 con2. SMALL_EVAL con1 con2 ==> TC SMALL_EVAL con1 con2``,
   METIS_TAC[TC_RULES]);

val TC_SMALL_EVAL_TRANS =
 store_thm
  ("TC_SMALL_EVAL_TRANS",
   ``!con1 con2 con3. 
      TC SMALL_EVAL con1 con2 
      ==> 
      TC SMALL_EVAL con2 con3 
      ==> TC 
      SMALL_EVAL con1 con3``,
   METIS_TAC[TC_RULES]);

val STEP_BIND_def =
 Define 
  `STEP_BIND m f = case m of
                       (l, TIMEOUT s) -> (l, TIMEOUT s)
                    || (l, ERROR s)   -> (l, ERROR s)
                    || (l, RESULT s)  -> f(l, s)`;

val _ = overload_on (">>=", ``STEP_BIND``);

(* Monad unit function *)
val STEP_RETURN_def =
 Define 
  `STEP_RETURN x = (FST x, RESULT(SND x))`;

val STEP_MONAD_LAWS =
 store_thm
  ("STEP_MONAD_LAWS",
   ``((STEP_RETURN x) >>= f  =  f x)
     /\
     (m >>= STEP_RETURN  =  m)
     /\
     ((m >>= f) >>= g  =  m >>= (\x. (f x) >>= g))``,
   RW_TAC std_ss [STEP_BIND_def, STEP_RETURN_def]
    THEN Cases_on `m`
    THEN Cases_on `r`
    THEN RW_TAC outcome_ss []);


(* Clocked next-state function *)
val STEP_def =
 Define
  `STEP n (l,s) = 
    if (l = [])
     then ([], RESULT s)
     else if n = 0 
     then (l, TIMEOUT s) 
     else STEP1(l,s) >>= STEP (n-1)`;

val STEP0 =
 store_thm
  ("STEP0",
   ``STEP 0 (l,s) = if l = [] then ([], RESULT s) else (l, TIMEOUT s)``,
   METIS_TAC[STEP_def,STEP_BIND_def]);

val STEP_SUC =
 store_thm
  ("STEP_SUC",
   ``STEP (SUC n) (l, s) =
      if (l = []) 
       then ([], RESULT s)
       else STEP1(l,s) >>= STEP n``,
   METIS_TAC[STEP_def, DECIDE ``~(SUC n = 0) /\ ((SUC n) - 1 = n)``]);

(* Explode into various cases (could have been the definition of STEP) *)
val STEP =
 store_thm
  ("STEP",
   ``(STEP n ([],s) = ([], RESULT s))
     /\
     (STEP 0 (l,s) = if l = [] then ([], RESULT s) else (l, TIMEOUT s))
     /\
     (STEP (SUC n) (Skip :: l, s) =
       STEP n (l, s))
     /\
     (STEP (SUC n) (GenAssign v e :: l, s) =
       STEP n (l, Update v e s))
     /\ 
     (STEP (SUC n) (Dispose v :: l, s) = 
       STEP n (l, s \\ v))
     /\ 
     (STEP (SUC n) (Seq c1 c2 :: l, s) = 
       STEP n (c1 :: c2 :: l, s))
     /\ 
     (STEP (SUC n) (Cond b c1 c2 :: l, s) = 
       if beval b s 
        then STEP n (c1 :: l, s)
        else STEP n (c2 :: l, s))
     /\ 
     (STEP (SUC n) (While b c :: l, s) = 
       if beval b s 
        then STEP n (c :: While b c :: l, s)
        else STEP n (l, s))
     /\ 
     (STEP (SUC n) (Local v c :: l, s) =
       if v IN FDOM s 
        then STEP n (c :: GenAssign v (Exp(s ' v)) :: l, s)
        else STEP n (c :: Dispose v :: l, s))
     /\
     (STEP (SUC n) (Proc f :: l, s) = (l, f s) >>= STEP n)``,
   Induct_on `n`
    THEN RW_TAC list_ss [STEP1,STEP0,STEP_SUC,STEP_BIND_def]);

val STEP_NIL =
 store_thm
  ("STEP_NIL",
   ``!n l1 s1 l2 s2. (STEP n (l1,s1) = (l2, RESULT s2)) ==> (l2 = [])``,
   Induct
    THEN RW_TAC std_ss [STEP,STEP_BIND_def]
    THEN FULL_SIMP_TAC std_ss [STEP_SUC,STEP_BIND_def]
    THEN Cases_on `l1 = []`
    THEN RW_TAC std_ss []
    THEN POP_ASSUM(fn th => FULL_SIMP_TAC outcome_ss [th])
    THEN Cases_on `STEP1 (l1,s1)`
    THEN RW_TAC std_ss []
    THEN Cases_on `r`
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC outcome_ss []
    THEN METIS_TAC[]);
   
val STEP_MONO =
 store_thm
  ("STEP_MONO",
   ``!m n l1 s1 s2. 
      m <= n  /\ (STEP m (l1,s1) = ([], RESULT s2)) 
      ==> (STEP n (l1,s1) = ([], RESULT s2)) ``,
   Induct
    THEN RW_TAC std_ss [STEP,STEP_SUC,STEP_BIND_def]
    THEN Cases_on `STEP1 (l1,s1)`
    THEN RW_TAC std_ss []
    THEN Cases_on `r`
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC outcome_ss []
    THEN Induct_on `n`
    THEN RW_TAC std_ss [STEP,STEP_SUC,STEP_BIND_def]);

val SMALL_EVAL_ITER_IMP_STEP =
 store_thm
  ("SMALL_EVAL_ITER_IMP_STEP",
   ``!m n l1 s1 s2.
      SMALL_EVAL_ITER m (l1,s1) ([],s2) /\ m < n 
      ==> (STEP n (l1,s1) = ([], RESULT s2))``,
   Induct THEN Induct
    THEN FULL_SIMP_TAC outcome_ss 
          [SMALL_EVAL_ITER,STEP_SUC,STEP,GSYM STEP1_SMALL_EVAL,STEP_BIND_def]
    THEN Cases_on `l1 = []`
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC outcome_ss [STEP1]);

val STEP_IMP_SMALL_EVAL_ITER =
 store_thm
  ("STEP_IMP_SMALL_EVAL_ITER",
   ``!n l1 s1 s2.
      (STEP n (l1,s1) = ([], RESULT s2)) /\ ~(l1 = [])
      ==>
      ?m. m < n /\ SMALL_EVAL_ITER m (l1,s1) ([],s2)``, 
   Induct 
    THEN FULL_SIMP_TAC outcome_ss [SMALL_EVAL_ITER,STEP_SUC,STEP,STEP_BIND_def]
    THEN RW_TAC outcome_ss []
    THEN Cases_on `STEP1 (l1,s1)`
    THEN FULL_SIMP_TAC outcome_ss []
    THEN Cases_on `r`
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC outcome_ss []
    THEN Cases_on `q = []`
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC outcome_ss [STEP,STEP1_SMALL_EVAL]
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `0`
       THEN RW_TAC std_ss [SMALL_EVAL_ITER],
      RES_TAC
       THEN Q.EXISTS_TAC `SUC m`
       THEN RW_TAC std_ss [SMALL_EVAL_ITER]
       THEN METIS_TAC[]]);

val SMALL_EVAL_ITER_STEP =
 store_thm
  ("SMALL_EVAL_ITER_STEP",
   ``!n c l s1 s2.
      (?m. m < n /\ SMALL_EVAL_ITER m (c :: l, s1) ([],s2)) 
      = 
      (STEP n (c :: l, s1) = ([], RESULT s2))``,
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN RW_TAC pure_ss []
    THENL
     [METIS_TAC[SMALL_EVAL_ITER_IMP_STEP],
      `~(c :: l = [])` by RW_TAC list_ss []
       THEN METIS_TAC[STEP_IMP_SMALL_EVAL_ITER]]);

val TC_SMALL_EVAL_STEP =
 store_thm
  ("TC_SMALL_EVAL_STEP",
   ``!c l s1 s2.
      TC SMALL_EVAL (c :: l, s1) ([],s2)
      = 
      ?n. STEP n (c :: l, s1) = ([], RESULT s2)``,
   RW_TAC std_ss [SMALL_EVAL_ITER_TC,GSYM SMALL_EVAL_ITER_STEP]
    THEN METIS_TAC[DECIDE``n < SUC n``]);

(* Corollary relating non-termination and TIMEOUT *)
val NOT_SMALL_EVAL_STEP_COR =
 store_thm
  ("NOT_SMALL_EVAL_STEP_COR",
   ``!c l1 s1. 
      ~(?s2. TC SMALL_EVAL (c :: l1, s1) ([], s2)) = 
      !n. ?l2 s2. (STEP n (c :: l1, s1) = (l2,ERROR s2) )
                  \/ 
                  (STEP n (c :: l1, s1) = (l2,TIMEOUT s2))``,
   REPEAT STRIP_TAC
    THEN RW_TAC std_ss [TC_SMALL_EVAL_STEP]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Cases_on `STEP n (c :: l1, s1)`
       THEN Cases_on `r`
       THEN RW_TAC outcome_ss []
       THEN METIS_TAC[STEP_NIL],
      `!x y. ~(RESULT x = ERROR y) /\ ~(RESULT x = TIMEOUT y)` 
       by RW_TAC outcome_ss []
       THEN `?l2 s2. (STEP n (c::l1,s1) = (l2,ERROR s2)) 
                     \/ 
                     (STEP n (c::l1,s1) = (l2,TIMEOUT s2))`
        by METIS_TAC[]
       THEN RW_TAC outcome_ss []]);

val NOT_SMALL_EVAL_STEP =
 store_thm
  ("NOT_SMALL_EVAL_STEP",
   ``!c s1. 
      ~(?s2. TC SMALL_EVAL ([c], s1) ([], s2)) = 
      !n. ?l s2. (STEP n ([c], s1) = (l,ERROR s2) )
                  \/ 
                  (STEP n ([c], s1) = (l,TIMEOUT s2))``,
   METIS_TAC[NOT_SMALL_EVAL_STEP_COR]);

val EVAL_STEP =
 store_thm
  ("EVAL_STEP",
   ``!c s1 s2.
      EVAL c s1 s2 = ?n. STEP n ([c], s1) = ([], RESULT s2)``,
   RW_TAC list_ss [EVAL_SMALL_EVAL,TC_SMALL_EVAL_STEP]);

val RUN_STEP =
 store_thm
  ("RUN_STEP",
   ``!c s1 s2.
     (?n. RUN n c s1 = RESULT s2) = (?n. STEP n ([c],s1) = ([],RESULT s2))``,
   METIS_TAC[EVAL_SMALL_EVAL,EVAL_RUN,TC_SMALL_EVAL_STEP]);

(* Some lemmas *)

val FUPDATE_ID =
 store_thm
  ("FUPDATE_ID",
   ``!f x. x IN FDOM f ==> (f |+ (x, f ' x) = f)``,
   METIS_TAC[FDOM_EQ_FDOM_FUPDATE,FAPPLY_FUPDATE_THM,fmap_EQ_THM]);

val DOM_FUPDATE_DOMSUB =
 store_thm
  ("DOM_FUPDATE_DOMSUB",
   ``!f x y. x IN FDOM f ==> (FDOM((f \\ x) |+ (x,y)) = FDOM f)``,
   RW_TAC std_ss [FDOM_FUPDATE,FDOM_DOMSUB,pred_setTheory.INSERT_DELETE]);

val FUPDATE_DOMSUB =
 store_thm
  ("FUPDATE_DOMSUB",
   ``!f x. x IN FDOM f ==> (f \\ x |+ (x, f ' x) = f)``,
   RW_TAC std_ss []
    THEN `FDOM(f \\ x |+ (x,f ' x)) = FDOM f` 
          by METIS_TAC[FDOM_FUPDATE,FDOM_DOMSUB,pred_setTheory.INSERT_DELETE]
    THEN `!z. z IN FDOM f ==> ((f \\ x |+ (x,f ' x)) ' z = f ' z)`
          by METIS_TAC[FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM]
    THEN METIS_TAC[fmap_EQ_THM]);

val NEVAL_FUPDATE_LEMMA =
 prove
  (``!e s v. neval e (s |+ (v,s ' v)) = neval e s``,
   Induct
    THEN RW_TAC std_ss [neval_def,FAPPLY_FUPDATE_THM]);

val AEVAL_FUPDATE_LEMMA =
 prove
  (``!a s v. aeval a (s |+ (v,s ' v)) = aeval a s``,   
   Induct
    THEN RW_TAC std_ss 
     [aeval_def,FAPPLY_FUPDATE_THM,NOT_FDOM_FAPPLY_FEMPTY,NEVAL_FUPDATE_LEMMA]);

(* 
``ACC_PRED p c s1 s2`` is the constraint after 
executing command c in state s1 with precondition p 
*)

val ACC_PRED_def =
 Define
  `(ACC_PRED p Skip s1 = p)
   /\
   (ACC_PRED p (GenAssign v e) s1 =
     \s2.
      if v IN FDOM s1
       then ((s2 ' v = Update v e s1 ' v) /\ p(s2 |+ (v,(s1 ' v))))
       else ((s2 ' v = Update v e s1 ' v) /\ p(s2 \\ v)))
   /\
   (ACC_PRED p (Dispose v) s1 = 
     \s2. if v IN FDOM s1 then p(s2 |+ (v,(s1 ' v))) else p s2)
   /\
   (ACC_PRED p (Seq c1 c2) s1 = p)
   /\
   (ACC_PRED p (Cond b c1 c2) s1 = 
     if beval b s1
      then (\s2. beval b s2 /\ p s2)
      else (\s2. ~(beval b s2) /\ p s2))
   /\
   (ACC_PRED p (While b c) s1 = 
     if beval b s1
      then (\s2. beval b s2 /\ p s2)
      else (\s2. ~(beval b s2) /\ p s2))
   /\
   (ACC_PRED p (Local v c) s1 = 
     if v IN FDOM s1
      then (\s2. v IN FDOM s2 /\ p s2) 
      else (\s2. ~(v IN FDOM s2) /\ p s2))
   /\
   (ACC_PRED p (Proc f) s1 = \s2. (RESULT s2 = f s1) /\ p s1)`;

val ACC_PRED_ASSIGN_LEMMA =
 store_thm
  ("ACC_PRED_ASSIGN_LEMMA",
   ``!p v e s. p s ==> ACC_PRED p (GenAssign v e) s (Update v e s)``,
   RW_TAC std_ss []
    THEN Cases_on `e`
    THEN RW_TAC std_ss 
          [ACC_PRED_def,Update_def,FUPDATE_EQ,FAPPLY_FUPDATE,Update_def,
           FUPDATE_ID,NEVAL_FUPDATE_LEMMA,AEVAL_FUPDATE_LEMMA,
           DOMSUB_FUPDATE,DOMSUB_NOT_IN_DOM]);

val ACC_PRED_DISPOSE_LEMMA =
 store_thm
  ("ACC_PRED_DISPOSE_LEMMA",
   ``!p v s. p s ==> ACC_PRED p (Dispose v) s (s \\ v)``,
   RW_TAC std_ss 
    [ACC_PRED_def,FUPDATE_EQ,FAPPLY_FUPDATE,
     FUPDATE_ID,NEVAL_FUPDATE_LEMMA,AEVAL_FUPDATE_LEMMA,
     DOMSUB_FUPDATE,DOMSUB_NOT_IN_DOM,FUPDATE_DOMSUB]);

val SMALL_EVAL_ACC_PRED_LEMMA =
 store_thm
  ("SMALL_EVAL_ACC_PRED_LEMMA",
   ``!con1 con2.
      SMALL_EVAL con1 con2
      ==>
      (\con1 con2. 
        p(SND con1) 
        ==> 
        ACC_PRED p (HD(FST con1)) (SND con1) (SND con2))
      con1 con2``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (small_rules,small_induction))
    THEN RW_TAC list_ss [ACC_PRED_ASSIGN_LEMMA,ACC_PRED_DISPOSE_LEMMA]
    THEN RW_TAC list_ss [ACC_PRED_def]);

val SMALL_EVAL_ACC_PRED =
 store_thm
  ("SMALL_EVAL_ACC_PRED",
   ``!c p l1 l2 s1 s2. 
      p s1
      ==>
      SMALL_EVAL (c::l1,s1) (l2,s2)
      ==> 
      ACC_PRED p c s1 s2``,
   METIS_TAC
    [SMALL_EVAL_ACC_PRED_LEMMA,listTheory.HD,pairTheory.FST,pairTheory.SND]);

val STEP1_ACC_PRED =
 store_thm
  ("STEP1_ACC_PRED",
   ``!c p l1 l2 s1 s2. 
      p s1
      ==>
      (STEP1(c::l1,s1) = (l2, RESULT s2))
      ==> 
      ACC_PRED p c s1 s2``,
   METIS_TAC[SMALL_EVAL_ACC_PRED,STEP1_SMALL_EVAL]);

(*===========================================================================*)
(* Property-acculating small-step semantics as in Collavizza et al. paper    *)
(*===========================================================================*)

val ACC_SMALL_EVAL_def =
 Define
  `ACC_SMALL_EVAL (con1, p1) (con2, p2) = 
    SMALL_EVAL con1 con2 /\ (p2 = ACC_PRED p1 (HD(FST con1)) (SND con1))`;

val ACC_SMALL_EVAL =
 store_thm
  ("ACC_SMALL_EVAL",
   ``(ACC_SMALL_EVAL (([], s1), p1) ((l2, s2), p2) = F)
     /\
     (ACC_SMALL_EVAL ((c :: l1, s1), p1) ((l2, s2), p2) =
       SMALL_EVAL (c :: l1, s1) (l2, s2) /\ (p2 = ACC_PRED p1 c s1))``,
   RW_TAC list_ss [ACC_SMALL_EVAL_def,SMALL_EVAL_NIL]);

val IS_SOME_EXISTS =
 store_thm
  ("IS_SOME_EXISTS",
   ``!x. IS_SOME x = ?y. x = SOME y``,
   Cases
    THEN RW_TAC std_ss []);

val ACC_SMALL_EVAL_CLAUSES =
 store_thm
  ("ACC_SMALL_EVAL_CLAUSES",
   ``(!s1 p1 l2 s2 p2.
       ACC_SMALL_EVAL (([], s1), p1) ((l2, s2), p2) = F)
     /\
     (!s1 l p. 
       ACC_SMALL_EVAL ((Skip :: l, s1), p) ((l, s1), p))
     /\ 
     (!s1 v e l p. 
       v IN FDOM s1
       ==>
       ACC_SMALL_EVAL 
        ((GenAssign v e :: l, s1), p) 
        ((l, 
          Update v e s1), 
          \s2. (s2 ' v = Update v e s1 ' v) 
               /\ 
               p(s2 |+ (v,(s1 ' v)))))
     /\ 
     (!s1 v e l p. 
       ~(v IN FDOM s1)
       ==>
       ACC_SMALL_EVAL 
        ((GenAssign v e :: l, s1), p) 
        ((l, 
          Update v e s1), 
          \s2. (s2 ' v = Update v e s1 ' v) 
               /\ 
               p(s2 \\ v)))
     /\ 
     (!s1 v l p. 
       v IN FDOM s1
       ==>
       ACC_SMALL_EVAL 
        ((Dispose v :: l, s1), p) 
        ((l, s1 \\ v), \s2. p(s2 |+ (v,(s1 ' v)))))
     /\ 
     (!s1 v l p. 
       ~(v IN FDOM s1)
       ==>
       ACC_SMALL_EVAL 
        ((Dispose v :: l, s1), p) 
        ((l, s1 \\ v), p))
     /\ 
     (!s1 l c1 c2 p. 
       ACC_SMALL_EVAL 
        ((Seq c1 c2 :: l, s1), p) 
        ((c1 :: c2 :: l, s1), p))
     /\ 
     (!s1 l b c1 c2 p.  
       beval b s1
       ==> 
       ACC_SMALL_EVAL 
        ((Cond b c1 c2 :: l, s1), p)
        ((c1 :: l, s1), \s2. beval b s2 /\ p s2))
     /\ 
     (!s1 l b c1 c2 p.  
       ~(beval b s1)
       ==> 
       ACC_SMALL_EVAL 
        ((Cond b c1 c2 :: l, s1), p)
        ((c2 :: l, s1), \s2. ~(beval b s2) /\ p s2))
     /\
     (!s1 l b c p.  
       beval b s1
       ==> 
       ACC_SMALL_EVAL 
        ((While b c :: l, s1), p)
        ((c :: While b c :: l, s1), \s2. beval b s2 /\ p s2))
     /\
     (!s1 l b c p.  
       ~(beval b s1)
       ==> 
       ACC_SMALL_EVAL 
        ((While b c :: l, s1), p)
        ((l, s1), \s2. ~(beval b s2) /\ p s2))
     /\
     (!s1 l v c p.
       v IN FDOM s1
       ==>
       ACC_SMALL_EVAL 
        ((Local v c :: l, s1), p) 
        ((c :: GenAssign v (Exp(s1 ' v)) :: l, s1), 
         \s2. v IN FDOM s2 /\ p s2))
     /\
     (!s1 l v c p.
       ~(v IN FDOM s1)
       ==>
       ACC_SMALL_EVAL 
        ((Local v c :: l, s1), p) 
        ((c :: Dispose v :: l, s1), 
         \s2. ~(v IN FDOM s2) /\ p s2))
     /\
     (!s1 l f p s. 
       (f s1 = RESULT s)
       ==> 
       ACC_SMALL_EVAL 
        ((Proc f :: l, s1), p) 
        ((l, s), 
         \s2. (s2 = s) /\ p s1))``,
   RW_TAC list_ss 
    ([ACC_SMALL_EVAL,ACC_PRED_def,FUN_EQ_THM,IS_SOME_EXISTS,SMALL_PROC_THM] 
     @ small_rulel)
    THEN RW_TAC std_ss []
    THEN METIS_TAC []);

val ACC_SMALL_EVAL_TRUE =
 store_thm
  ("ACC_SMALL_EVAL_TRUE",
   ``!l1 l2 s1 s2 p1 p2.
      ACC_SMALL_EVAL ((l1,s1),p1) ((l2,s2),p2) /\ p1 s1 ==> p2 s2``,
   Cases
    THEN RW_TAC list_ss [ACC_SMALL_EVAL]
    THEN METIS_TAC[SMALL_EVAL_ACC_PRED]);

val ACC_SMALL_EVAL_SMALL_EVAL =
 store_thm
  ("ACC_SMALL_EVAL_SMALL_EVAL",
   ``!con1 con2 p1 p2.
      ACC_SMALL_EVAL (con1,p1) (con2,p2) ==> SMALL_EVAL con1 con2``,
   METIS_TAC[ACC_SMALL_EVAL_def]);

val ACC_SMALL_EVAL_THM =
 store_thm
  ("ACC_SMALL_EVAL_THM",
   ``!l1 l2 s1 s2 p1 p2.
      p1 s1
      ==>
      ACC_SMALL_EVAL ((l1,s1),p1) ((l2,s2),p2) 
      ==> 
      SMALL_EVAL (l1,s1) (l2,s2) /\ p2 s2``,
  METIS_TAC[ACC_SMALL_EVAL_TRUE,ACC_SMALL_EVAL_SMALL_EVAL]);

(*===========================================================================*)
(* Accumulating small step next-state function                               *)
(*===========================================================================*)

val ACC_STEP_BIND_def =
 Define 
  `ACC_STEP_BIND m f = case m of
                       ((l, TIMEOUT s), p) -> ((l, TIMEOUT s), p)
                    || ((l, ERROR s), p)   -> ((l, ERROR s), p)
                    || ((l, RESULT s), p)  -> f((l, s), p)`;

val _ = overload_on (">>=", ``ACC_STEP_BIND``);

(* Monad unit function *)
val ACC_STEP_RETURN_def =
 Define 
  `ACC_STEP_RETURN x = ((FST(FST x), RESULT(SND(FST x))), SND x)`;

val ACC_STEP_MONAD_LAWS =
 store_thm
  ("ACC_STEP_MONAD_LAWS",
   ``((ACC_STEP_RETURN x) >>= f  =  f x)
     /\
     (m >>= ACC_STEP_RETURN  =  m)
     /\
     ((m >>= f) >>= g  =  m >>= (\x. (f x) >>= g))``,
   RW_TAC std_ss [ACC_STEP_BIND_def, ACC_STEP_RETURN_def]
    THEN Cases_on `m`
    THEN Cases_on `q`
    THEN Cases_on `r'`
    THEN RW_TAC outcome_ss []);

val ACC_STEP_BIND_RESULT =
 store_thm
  ("ACC_STEP_BIND_RESULT",
   ``!l s p. ((l, RESULT s), p) >>= f = f((l,s),p)``,
   RW_TAC std_ss [ACC_STEP_BIND_def, ACC_STEP_RETURN_def]);

(* Single step *)
val ACC_STEP1_def =
 Define
  `ACC_STEP1 (con, p) = 
    (STEP1 con, 
     if NULL(FST con) then p else ACC_PRED p (HD(FST con)) (SND con))`;

(* Clocked accumulating next-state function *)

val ACC_STEP_def =
 Define
  `(ACC_STEP n (([],s),p) = (([], RESULT s), p))
   /\
   (ACC_STEP 0 ((l,s),p) = ((l, TIMEOUT s), p))
   /\
   (ACC_STEP (SUC n) ((l,s),p) = ACC_STEP1 ((l,s),p) >>=  ACC_STEP n)`;

val NOT_EMPTY_EXISTS =
 prove
  (``!l. ~(l = []) = ?x l'. l = x :: l'``,
   Induct
    THEN RW_TAC list_ss []);

val ACC_STEP =
 store_thm
  ("ACC_STEP",
   ``!n l s p.
      ACC_STEP n ((l,s),p) =
       if (l = []) 
        then (([], RESULT s), p) else
       if (n = 0)  
        then ((l, TIMEOUT s), p) 
        else ACC_STEP1 ((l,s),p) >>=  ACC_STEP (n-1)``,
    Cases
     THEN RW_TAC std_ss [ACC_STEP_def]
     THEN FULL_SIMP_TAC std_ss [NOT_EMPTY_EXISTS]
     THEN RW_TAC std_ss [ACC_STEP_def,ACC_STEP_BIND_def]);

(* Add to EVAL compset *)
val _ = computeLib.add_persistent_funs [("ACC_STEP",ACC_STEP)];

val ACC_STEP_STEP =
 store_thm
  ("ACC_STEP_STEP",
   ``!n l s1 s2 P Q.
      P s1 /\ (ACC_STEP n ((l,s1),P) = (([], RESULT s2), Q))
      ==>
      (STEP n (l,s1) = ([], RESULT s2)) /\ Q s2``,
   Induct
    THEN RW_TAC std_ss [ACC_STEP_def,STEP]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC outcome_ss [ACC_STEP_def,NOT_EMPTY_EXISTS]
    THEN RW_TAC std_ss [STEP_SUC]      
    THEN FULL_SIMP_TAC outcome_ss [ACC_STEP_def,NOT_EMPTY_EXISTS]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC outcome_ss 
          [ACC_STEP_def,NOT_EMPTY_EXISTS,ACC_STEP1_def,ACC_STEP_BIND_def,STEP_BIND_def]
    THENL
     [Cases_on `STEP1 (x::l',s1)`
       THEN FULL_SIMP_TAC outcome_ss []
       THEN Cases_on `r`
       THEN FULL_SIMP_TAC outcome_ss []
       THEN METIS_TAC[STEP1_ACC_PRED],
      Cases_on `l`
       THEN FULL_SIMP_TAC list_ss [ACC_STEP_def]
       THEN RW_TAC std_ss []
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC list_ss [ACC_STEP_BIND_def]
       THEN Cases_on `ACC_STEP1 ((h::t,s1),P)`
       THEN FULL_SIMP_TAC outcome_ss []
       THEN Cases_on `q`
       THEN FULL_SIMP_TAC outcome_ss []
       THEN Cases_on `r'`
       THEN FULL_SIMP_TAC outcome_ss [ACC_STEP1_def]
       THEN METIS_TAC[STEP1_ACC_PRED]]);

val SPEC_ACC_STEP =
 store_thm
  ("SPEC_ACC_STEP",
   ``!P c R.
      (!s1. ?n s2. ACC_STEP n (([c],s1),P) = (([], RESULT s2), R s1))
      ==>
      !s1 s2. P s1 /\ EVAL c s1 s2 ==> R s1 s2``,
   RW_TAC std_ss [EVAL_STEP]
    THEN `?n s2. ACC_STEP n (([c],s1),P) = (([],RESULT s2),R s1)` by METIS_TAC[]
    THEN IMP_RES_TAC ACC_STEP_STEP
    THEN `n <= n' \/ n' <= n` by DECIDE_TAC
    THEN IMP_RES_TAC STEP_MONO
    THEN `RESULT s2 = RESULT s2'` by METIS_TAC[pairTheory.PAIR_EQ]
    THEN FULL_SIMP_TAC outcome_ss []);

(* Some miscellaneous theorems used in PATH_EVAL. sml *)


(* Rearrangement lemma used in SYMBOLIC_EVAL_PROVE *)
val EVAL_SPEC_THM =
 store_thm
  ("EVAL_SPEC_THM",
   ``!A P c Q f. 
      (!s. A s ==> P s ==> (EVAL c s (f s) /\ (Q(f s) = T))) 
      ==> 
      SPEC (\s. P s /\ A s) c Q``,
   RW_TAC std_ss [SPEC_def]
    THEN RES_TAC
    THEN IMP_RES_TAC EVAL_DETERMINISTIC
    THEN RW_TAC std_ss []);

(* |- !f x y. f |+ (x,y) = f \\ x |+ (x,y)  *)
val FUPDATE_PRUNE_LEMMA =
 Q.GEN `f` 
  (Q.GEN `x` 
    (Q.GEN `y`
     (GSYM
       (CONV_RULE 
         EVAL 
         (Q.SPEC `x` (Q.SPEC `f |+ (x,y)` FUPDATE_DOMSUB))))));

val FUPDATE_PRUNE =
 store_thm
  ("FUPDATE_PRUNE",
   ``!f p. f |+ p = f \\ (FST p) |+ p``,
   RW_TAC std_ss []
    THEN Cases_on `p`
    THEN RW_TAC std_ss []
    THEN METIS_TAC [FUPDATE_PRUNE_LEMMA]);

val FUPDATE_LIST_FOLD_LEMMA =
 store_thm
  ("FUPDATE_LIST_FOLD_LEMMA",
   ``!f p. f |+ p = f |++ [p]``,
   RW_TAC list_ss [FUPDATE_LIST_THM]);

(* Ad hoc collection of theorems used in SYM_RUN *)

val NOT_IMP_EQ_F = 
 save_thm
  ("NOT_IMP_EQ_F",
   METIS_PROVE [] ``!t. ~t ==> (t =F)``);

val TC_SMALL_EVAL_IF =
 save_thm
  ("TC_SMALL_EVAL_IF",
   METIS_PROVE [] 
    ``!con b s1 s2.
       (b ==> TC SMALL_EVAL con ([],s1)) 
       /\ 
       (~b ==> TC SMALL_EVAL con ([],s2))
       ==>
       TC SMALL_EVAL con ([], if b then s1 else s2)``);

val LEFT_T_ELIM = 
 save_thm
  ("LEFT_T_ELIM",
   METIS_PROVE [] ``!b. T /\ b = b``);

val T_AND_T =
 save_thm
  ("T_AND_T",
   METIS_PROVE [] ``T /\ T = T``);

val NOT_EQ_F =
 save_thm
  ("NOT_EQ_F",
   METIS_PROVE [] ``!b. ~b ==> (b = F)``);

val NOT_EQ_T =
 save_thm
  ("NOT_EQ_T",
   METIS_PROVE [] ``!b. (b = T) ==> (~b = F)``);

val ABS_T_CONJ =
 save_thm
  ("ABS_T_CONJ",
   METIS_PROVE [] 
    ``!P Q (s:state). P s ==> (Q s = T) ==> (\s. P s /\ Q s) s``);

val ABS_F_CONJ =
 save_thm
  ("ABS_F_CONJ",
   METIS_PROVE [] 
    ``!P Q (s:state). P s ==> (~(Q s) = T) ==> (\s. P s /\ ~(Q s)) s``);

val STEP1_T =
 save_thm
  ("STEP1_T",
   METIS_PROVE []
   ``!bx b l s x y. 
      bx ==> (bx ==> b = T) ==> (STEP1 (l,s) = if b then x else y) 
      ==> (STEP1 (l,s) = x)``);

val STEP1_F =
 save_thm
  ("STEP1_F",
   METIS_PROVE []
   ``!bx b l s x y. 
      bx ==> (bx ==> ~b = T) ==> (STEP1 (l,s) = if b then x else y) 
      ==> (STEP1 (l,s) = y)``);

(* Utility theorem used by CONJ_DISCH_ALL *)
val CONJ_DISCH_ALL_THM =
 save_thm
  ("CONJ_DISCH_ALL_THM",
   METIS_PROVE [] ``!t1 t2 t. t1 ==> (t2 ==> t) = t2 /\ t1 ==> t``);

(* Utility theorem used by EVAL_IMP_INTRO *)
val IMP_INTRO_THM =
 store_thm
  ("IMP_INTRO_THM",
   ``!pre prog post. RSPEC pre prog post = IMP pre post prog``,
    METIS_TAC[IMP_def]);

val NOT_CONJ_IMP_F =
 save_thm
  ("NOT_CONJ_IMP_F",
   METIS_PROVE [] ``!p b : bool. ~(p /\ b) ==> ((p ==> ~b) = T)``);

(* Type annotations needed below as "~", "/\", "\/" are overloaded *)
val NOT_IMP_CONJ =
 save_thm
  ("NOT_IMP_CONJ",
   METIS_PROVE [] ``!A B C : bool . ~((A ==> B) /\ C) = (A /\ ~B) \/ ~C``);

val CONJ_RIGHT_ASSOC =
 save_thm
  ("CONJ_RIGHT_ASSOC",
   METIS_PROVE [] ``!A B C : bool. A /\ (B /\ C) = A /\ B /\ C``);

val CONJ_LEFT_ASSOC =
 save_thm
  ("CONJ_LEFT_ASSOC",
   METIS_PROVE [] ``!A B C : bool. (A /\ B) /\ C = A /\ B /\ C``);

val NOT_DISJ =
 save_thm
  ("NOT_DISJ",
   METIS_PROVE [] ``!A B : bool. ~(A \/ B) = ~A /\ ~B``);

val IMP_F_IS_F = 
 save_thm
  ("IMP_F_IS_F",
   METIS_PROVE [] ``!P : bool. (!Q. P ==> Q) ==> (P = F)``);

(* Identity wrapper to tag ILOG-generated assumptions *)
val ILOG_def = Define `ILOG(tm:bool) = tm`;

(* ============================================================================
Program transformation/normalisation rules
============================================================================ *)

(* Straight line (non-looping) programs *)
val STRAIGHT_def =
 Define
  `(STRAIGHT Skip = T)
   /\
   (STRAIGHT (GenAssign v e) = T)
   /\
   (STRAIGHT (Dispose v) = F)
   /\
   (STRAIGHT (Seq c1 c2) = STRAIGHT c1 /\ STRAIGHT c2)
   /\
   (STRAIGHT (Cond b c1 c2) = STRAIGHT c1 /\ STRAIGHT c2)
   /\
   (STRAIGHT (While b c) = F)
   /\
   (STRAIGHT (Local v c) = F)
   /\
   (STRAIGHT (Proc f) = F)`;

(* RUN straight line programs *)

(*
Semantics that represents states as key-value lists (key = string). If
kvl is such a list then the corresponding finite map is FEMPTY |++ kvl.
*)

(* Update value in a key-value list *)
val UPDATE_LIST_def =
 Define
  `(UPDATE_LIST [] (v,x) = [(v,x)])
   /\
   (UPDATE_LIST ((v2,x2) :: l) (v1,x1) =
     if v1 = v2 then (v1,x1) :: l else (v2,x2) :: UPDATE_LIST l (v1,x1))`;

(* 
ZIP_LIST b [(v1,x1);...;(vn,xn)] [(v1,y1);...;(vn,yn)] =
 [(v1,if b then x1 else y1);...;(vn,if b then xn else yn)]
*)

val ZIP_LIST_def =
 Define
  `(ZIP_LIST (b:bool) l1 [] = [])
   /\
   (ZIP_LIST (b:bool) [] l2 = [])
   /\
   (ZIP_LIST b ((v1,x1) :: l1) ((v2,x2) :: l2) =
    (v1, (if b then x1 else x2)) :: ZIP_LIST b l1 l2)`;

val STRAIGHT_RUN_def =
 Define
  `(STRAIGHT_RUN Skip l = l)
   /\
   (STRAIGHT_RUN (GenAssign v (INL e)) l = 
     UPDATE_LIST l (v,Scalar (neval e (FEMPTY |++ l))))
   /\
   (STRAIGHT_RUN (GenAssign v (INR a)) l = 
     UPDATE_LIST l (v,Array  (aeval a (FEMPTY |++ l))))
   /\
   (STRAIGHT_RUN (Seq c1 c2) s = STRAIGHT_RUN c2 (STRAIGHT_RUN c1 s))
   /\
   (STRAIGHT_RUN (Cond b c1 c2) l = 
    ZIP_LIST (beval b (FEMPTY |++ l)) (STRAIGHT_RUN c1 l) (STRAIGHT_RUN c2 l))`;

val DISTINCT_VARS_def =
 Define
  `DISTINCT_VARS l = ALL_DISTINCT(MAP FST l)`;

val FUPDATE_LIST_FUPDATE_NOT_MEM =
 store_thm
  ("FUPDATE_LIST_FUPDATE_NOT_MEM",
   ``!l. ~(MEM v (MAP FST l)) /\ DISTINCT_VARS l
         ==> !fm x y. fm |+ (v,x) |++ l = (fm |+ (v,y) |++ l) |+ (v,x)``,
   Induct
    THEN RW_TAC std_ss [FUPDATE_LIST_THM,FUPDATE_EQ]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT]
    THEN METIS_TAC[FUPDATE_EQ,FUPDATE_COMMUTES]);

val UPDATE_LIST_FUPDATE =
 store_thm
  ("UPDATE_LIST_FUPDATE",
   ``!l. DISTINCT_VARS l  
         ==> !fm v x. fm |++ UPDATE_LIST l (v,x) = (fm |++ l) |+ (v,x)``,
   Induct
    THEN RW_TAC std_ss [UPDATE_LIST_def,FUPDATE_LIST_THM]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC std_ss [UPDATE_LIST_def,FUPDATE_LIST_THM,listTheory.ALL_DISTINCT]
    THEN Cases_on `v = q`
    THEN FULL_SIMP_TAC list_ss 
          [UPDATE_LIST_def,FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT]
    THEN METIS_TAC[FUPDATE_LIST_FUPDATE_NOT_MEM,DISTINCT_VARS_def]);

val MAP_FST_UPDATE_LIST =
 prove
  (``!l. MAP FST (UPDATE_LIST l (v,x)) = 
          if MEM v (MAP FST l) then MAP FST l else (MAP FST l) ++ [v]``,
   Induct 
    THEN RW_TAC list_ss [DISTINCT_VARS_def,listTheory.ALL_DISTINCT,UPDATE_LIST_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,UPDATE_LIST_def]
    THEN Cases_on `q = v`
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,UPDATE_LIST_def]);

val UpdateDISTINCT =
 store_thm
  ("UpdateDISTINCT",
   ``!l. DISTINCT_VARS l ==> !v x. DISTINCT_VARS(UPDATE_LIST l (v,x))``,
   Induct 
    THEN RW_TAC list_ss [DISTINCT_VARS_def,listTheory.ALL_DISTINCT,UPDATE_LIST_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,UPDATE_LIST_def]
    THEN Cases_on `q = v`
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,
           UPDATE_LIST_def,MAP_FST_UPDATE_LIST]
    THEN Cases_on `MEM v (MAP FST l)`
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,
           UPDATE_LIST_def,MAP_FST_UPDATE_LIST]);

val MAP_FST_SUBSET_ZIP_LIST =
 prove
  (``!l1 l2 b x. MEM x (MAP FST (ZIP_LIST b l1 l2)) ==> MEM x (MAP FST l1)``,
   Induct 
    THENL[ALL_TAC,GEN_TAC]
    THEN Induct
    THEN RW_TAC list_ss [DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]
    THEN Cases_on `h` 
    THEN TRY(Cases_on `h'`)
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]
    THEN METIS_TAC[]);

val ZIP_LIST_DISTINCT =
 store_thm
  ("ZIP_LIST_DISTINCT",
   ``!l1 l2. DISTINCT_VARS l1 /\ DISTINCT_VARS l2 
             ==> !b. DISTINCT_VARS(ZIP_LIST b l1 l2)``,
   Induct 
    THENL[ALL_TAC,GEN_TAC]
    THEN Induct
    THEN RW_TAC list_ss [DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]
    THEN Cases_on `h` 
    THEN TRY(Cases_on `h'`)
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]
    THEN METIS_TAC[MAP_FST_SUBSET_ZIP_LIST]);

val STRAIGHT_RUN_DISTINCT =
 store_thm
  ("STRAIGHT_RUN_DISTINCT",
   ``!c. STRAIGHT c ==> !l. DISTINCT_VARS l ==> DISTINCT_VARS(STRAIGHT_RUN c l)``,
   Induct 
    THEN RW_TAC std_ss [rules,STRAIGHT_RUN_def,STRAIGHT_def]
    THEN TRY(Cases_on `s0`)
    THEN RW_TAC std_ss 
          [SEQ_THM,IF_THM,rules,GEN_ASSIGN_THM,Update_def,
           STRAIGHT_RUN_def,UPDATE_LIST_FUPDATE,UpdateDISTINCT]
    THEN METIS_TAC[ZIP_LIST_DISTINCT]);

val ZIP_LIST_T =
 prove
  (``!l1 l2. (LENGTH l1 = LENGTH l2) ==> (ZIP_LIST T l1 l2 = l1)``,
   Induct 
    THENL[ALL_TAC,GEN_TAC]
    THEN Induct
    THEN RW_TAC list_ss [DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]
    THEN Cases_on `h` 
    THEN TRY(Cases_on `h'`)
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]);

val ZIP_LIST_F =
 prove
  (``!l1 l2. (MAP FST l1 = MAP FST l2) ==> (ZIP_LIST F l1 l2 = l2)``,
   Induct 
    THENL[ALL_TAC,GEN_TAC]
    THEN Induct
    THEN RW_TAC list_ss [DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]
    THEN Cases_on `h` 
    THEN TRY(Cases_on `h'`)
    THEN FULL_SIMP_TAC list_ss 
          [FUPDATE_LIST_THM,DISTINCT_VARS_def,listTheory.ALL_DISTINCT,ZIP_LIST_def]);

(* Vars assigned to in a program *)
val VARS_def =
 Define
  `(VARS Skip = {})
   /\
   (VARS (GenAssign v e) = {v}) 
   /\
   (VARS (Seq c1 c2) = VARS c1 UNION VARS c2)
   /\
   (VARS (Cond b c1 c2) = VARS c1 UNION VARS c2)`;

val MAP_FST_ZIP_LIST =
 prove
  (``!l1 l2 l b. (MAP FST l1 = l) /\ (MAP FST l2 = l) ==> (MAP FST (ZIP_LIST b l1 l2) = l)``,
   Induct 
    THENL[ALL_TAC,GEN_TAC]
    THEN Induct
    THEN RW_TAC list_ss [ZIP_LIST_def]
    THEN Cases_on `h` 
    THEN Cases_on `h'`
    THEN FULL_SIMP_TAC list_ss [ZIP_LIST_def]);  

val VARS_IN_def =
 Define
   `VARS_IN c l = !v. v IN (VARS c) ==> MEM v (MAP FST l)`;

val VARS_STRAIGHT_RUN =
 prove
  (``!c l. STRAIGHT c /\ VARS_IN c l 
           ==> (MAP FST (STRAIGHT_RUN c l) = MAP FST l)``,
   Induct
    THEN TRY(Cases_on `s0`)
    THEN RW_TAC list_ss 
          [STRAIGHT_def,VARS_def,NOT_IN_EMPTY,IN_SING,STRAIGHT_RUN_def,
           MAP_FST_UPDATE_LIST,IN_UNION,VARS_IN_def]
    THEN METIS_TAC[MAP_FST_ZIP_LIST,VARS_IN_def]);

val VARS_STRAIGHT_RUN_COR =
 prove
  (``!c l. STRAIGHT c /\ VARS_IN c l 
           ==> (LENGTH(STRAIGHT_RUN c l) = LENGTH l)``,
    METIS_TAC[VARS_IN_def,rich_listTheory.LENGTH_MAP,VARS_STRAIGHT_RUN]);

val STRAIGHT_RUN_EVAL =
 store_thm
  ("STRAIGHT_RUN_EVAL",
   ``!c l. STRAIGHT c /\ VARS_IN c l /\ DISTINCT_VARS l 
           ==> (EVAL c (FEMPTY |++ l) (FEMPTY |++ STRAIGHT_RUN c l))``,
   Induct
    THEN RW_TAC std_ss 
          [VARS_IN_def,STRAIGHT_def, rules, STRAIGHT_RUN_def,VARS_def,IN_UNION]
    THEN TRY(Cases_on `s0`)
    THEN RW_TAC std_ss 
          [SEQ_THM,IF_THM,rules,GEN_ASSIGN_THM,Update_def,
           STRAIGHT_RUN_def,UPDATE_LIST_FUPDATE]
    THEN METIS_TAC
          [ZIP_LIST_DISTINCT,STRAIGHT_RUN_DISTINCT,ZIP_LIST_T,ZIP_LIST_F,
           VARS_IN_def,VARS_STRAIGHT_RUN,VARS_STRAIGHT_RUN_COR]);

val STRAIGHT_RUN_EVAL =
 store_thm
  ("STRAIGHT_RUN_EVAL",
   ``!c l. STRAIGHT c 
           ==> VARS_IN c l 
           ==> DISTINCT_VARS l 
           ==> (EVAL c (FEMPTY |++ l) (FEMPTY |++ STRAIGHT_RUN c l))``,
   Induct
    THEN RW_TAC std_ss 
          [VARS_IN_def,STRAIGHT_def, rules, STRAIGHT_RUN_def,VARS_def,IN_UNION]
    THEN TRY(Cases_on `s0`)
    THEN RW_TAC std_ss 
          [SEQ_THM,IF_THM,rules,GEN_ASSIGN_THM,Update_def,
           STRAIGHT_RUN_def,UPDATE_LIST_FUPDATE]
    THEN METIS_TAC
          [ZIP_LIST_DISTINCT,STRAIGHT_RUN_DISTINCT,ZIP_LIST_T,ZIP_LIST_F,
           VARS_IN_def,VARS_STRAIGHT_RUN,VARS_STRAIGHT_RUN_COR]);


(* ============================================================================
Implementation of functions by macro-expansion

 Locals [x1;x2; ... ;xn] c 
 --> 
 Local x1 (local x2 ... (local xn c) ...)

 Disposals [x1;x2; ... ;xn]
 -->
 (Dispose x1 ;; Dispose x2 ;; ... ;; Dispose xn)

 Fun [x1; ... ;xn] res c 
 --> 
 \[a1;...;an].
   Locals [x1;...;x2]
  (x1 ::= a1 ;; ... ;; xn ::= an ;; 
  c ;; 
  Result ::= res ;; 
  Disposals [x1;...;xn])
============================================================================ *)


val _ = export_theory();


