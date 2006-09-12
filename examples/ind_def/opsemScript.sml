(* =====================================================================*)
(* FILE		: opsemScript.sml					*)
(* DESCRIPTION   : Creates a theory of the syntax and operational 	*)
(* 		  semantics of a very simple imperative programming 	*)
(* 		  language.  Illustrates the inductive definitions 	*)
(* 		  package with proofs that the evaluation relation for	*)
(*		  the given semantics is deterministic and that the 	*)
(*		  Hoare-logic rule for while loops follows from a 	*)
(*		  suitable definition of partial correctness.		*)
(*									*)
(* AUTHORS	: Tom Melham and Juanito Camilleri			*)
(* DATE		: 91.10.09						*)
(* TRANSLATED   : Dec. 27, 1992 Konrad Slind                            *)
(* =====================================================================*)

(* Interactive prelude
  app load ["stringLib", "bossLib"];
*)


structure opsemScript =
struct

open HolKernel Parse boolLib stringLib bossLib IndDefLib IndDefRules;

(* ---------------------------------------------------------------------*)
(* Open a new theory and load the required libraries.			*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "opsem";

(* ===================================================================== *)
(* Syntax of the programming language.					 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Program variables will be represented by strings, and states will be  *)
(* modelled by functions from program variables to natural numbers.	 *)
(* --------------------------------------------------------------------- *)

val state = Type`:string->num`;

(* --------------------------------------------------------------------- *)
(* Natural number expressions and boolean expressions will just be 	 *)
(* modelled by total functions from states to numbers and booleans       *)
(* respectively.  This simplification allows us to concentrate in this   *)
(* example on defining the semantics of commands.			 *)
(* --------------------------------------------------------------------- *)

val nexp = Type`:^state -> num`;
val bexp = Type`:^state -> bool`;

(*---------------------------------------------------------------------------
     Lift type antiquotes so they can be used in term quotations.
 ---------------------------------------------------------------------------*)

val State = ty_antiq state;
val Bexp  = ty_antiq bexp;

(* ---------------------------------------------------------------------*)
(* We can now use the recursive types package to define the syntax of   *)
(* commands (or "programs').  We have the following types of commands:  *)
(*									*)
(*    C ::=   skip                     (does nothing)			*)
(*          | V := E                   (assignment)          		*)
(*          | C1 ; C2                  (sequencing)           		*)
(*          | if B then C1 else C2     (conditional)			*)
(*          | While B do C             (repetition)			*)
(*                                                                      *)
(* where V ranges over program variables, E ranges over natural number	*)
(* expressions, B ranges over boolean expressions, and C, C1 and C2     *)
(* range over commands.  						*)
(*									*)
(* In the logic, we represent this abstract syntax with a set of prefix *)
(* type constructors. So we have:					*)
(*						                        *)
(*    V := E                  represented by `assign V E`		*)
(*    C1 ; C2                 represented by `seq C1 C2`		*)
(*    if B then C1 else C2    represented by `if B C1 C2`		*)
(*    While B do C            represented by `While B C`		*)
(*									*)
(* ---------------------------------------------------------------------*)

val _ = Hol_datatype
          `comm
             = Skip
             | ::=    of string => ^nexp
             | ;;    of  comm => comm
             | If    of ^bexp => comm => comm
             | While of ^bexp => comm`;

val _ = (set_fixity "::=" (Infixr 400); set_MLname "::=" "assign_def");
val _ = (set_fixity ";;"  (Infixr 350); set_MLname ";;"  "seq_def");

(* ===================================================================== *)
(* Definition of the operational semantics.				 *)
(* ===================================================================== *)

(* ---------------------------------------------------------------------*)
(* The semantics of commands will be given by an evaluation relation	*)
(*									*)
(*       EVAL : comm -> state -> state -> bool     			*)
(*									*)
(* defined inductively such that 					*)
(*									*)
(*       EVAL C s1 s2							*)
(*									*)
(* holds exactly when executing the command C in the initial state s1 	*)
(* terminates in the final state s2. The evaluation relation is defined *)
(* inductively by the set of rules shown below.  			*)
(* ---------------------------------------------------------------------*)

val (rules,induction,ecases) = Hol_reln
     `(!s. EVAL Skip s s)
 /\   (!s V E. EVAL (V ::= E) s (\v. if v=V then E s else s v))
 /\   (!C1 C2 s1 s3.
        (?s2. EVAL C1 s1 s2 /\ EVAL C2 s2 s3) ==> EVAL (C1;;C2) s1 s3)
 /\   (!C1 C2 s1 s2 B. EVAL C1 s1 s2 /\  B s1 ==> EVAL (If B C1 C2) s1 s2)
 /\   (!C1 C2 s1 s2 B. EVAL C2 s1 s2 /\ ~B s1 ==> EVAL (If B C1 C2) s1 s2)
 /\   (!C s B.                           ~B s ==> EVAL (While B C) s s)
 /\   (!C s1 s3 B.
        (?s2. EVAL C s1 s2 /\
              EVAL (While B C) s2 s3 /\ B s1) ==> EVAL (While B C) s1 s3)`;

val rulel = CONJUNCTS rules;

(*---------------------------------------------------------------------------
      Note that the following input is also acceptable to the
      definition package (existentials on the left of implications
      have been made into universals). This is in some way
      cleaner, but some of the following proofs depend on the
      specific structure of formulas and therefore fail with the
      different representation.

       (!s. EVAL Skip s s)
   /\  (!s V E. EVAL (V ::= E) s (\v. if v=V then E s else s v))
   /\  (!C1 C2 s1 s2 s3.
                EVAL C1 s1 s2 /\ EVAL C2 s2 s3 ==> EVAL (C1;;C2) s1 s3)
   /\  (!C1 C2 s1 s2 B. EVAL C1 s1 s2 /\  B s1 ==> EVAL (If B C1 C2) s1 s2)
   /\  (!C1 C2 s1 s2 B. EVAL C2 s1 s2 /\ ~B s1 ==> EVAL (If B C1 C2) s1 s2)
   /\  (!C s B.                           ~B s ==> EVAL (While B C) s s)
   /\  (!C s1 s2 s3 B. EVAL C s1 s2 /\
                EVAL (While B C) s2 s3 /\ B s1 ==> EVAL (While B C) s1 s3)
 ---------------------------------------------------------------------------*)


(* --------------------------------------------------------------------- *)
(* Stronger form of rule induction.					 *)
(* --------------------------------------------------------------------- *)

val sind = derive_strong_induction(rules,induction);

(* ---------------------------------------------------------------------*)
(* Construct the standard rule induction tactic for EVAL.  This uses	*)
(* the "weaker' form of the rule induction theorem, and both premisses	*)
(* and side conditions are simply assumed (in stripped form).  This 	*)
(* served for many proofs, but when a more elaborate treatment of	*)
(* premisses or side conditions is needed, or when the stronger form of	*)
(* induction is required, a specialized  rule induction tactic is	*)
(* constructed on the fly.						*)
(* ---------------------------------------------------------------------*)

val RULE_INDUCT_TAC =
    RULE_INDUCT_THEN induction STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* =====================================================================*)
(* Derivation of backwards case analysis theorems for each rule.        *)
(*									*)
(* These theorems are consequences of the general case analysis theorem *)
(* proved above.  They are used to justify formal reasoning in which the*)
(* rules are driven "backwards', inferring premisses from conclusions.  *)
(* One infers from the assertion that:					*)
(*									*)
(*    1: EVAL C s1 s2 							*)
(*									*)
(* for a specific command C (e.g. for C = (--`Skip`--)) that the        *)
(* corresponding instance of the premisses of the rule(s) for C must    *)
(* also hold, since  (1) can hold only by virtue of being derivable by  *)
(* the rule for C. This kind of reasoning occurs frequently in proofs   *)
(* about operational semantics.  Formally, one must use the fact that   *)
(* the logical representations of syntactically different commands are  *)
(* distinct, a fact automatically proved by the recursive types package.*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* The following rule is used to simplify special cases of the general  *)
(* exhaustive case analysis theorem, which looks something like:	*)
(*									*)
(*      |- !C s1 s2.							*)
(*          EVAL C s1 s2 =						*)
(*             (C = Skip) ... \/					*)
(*             (?V E. (C = V ::= E) ...) \/				*)
(*             (?C1 C2 s2'. (C = C1 ; C2) ...) \/			*)
(*             (?C1 B C2. (C = If B C1 C2) /\ B s1 ...) \/		*)
(*             (?C2 B C1. (C = If B C1 C2) /\ ~B s1 ...) \/		*)
(*             (?B C'. (C = While B C') /\ ~B s1 ... ) \/		*)
(*             (?C' B s2'. (C = While B C') /\ B s1 ...)		*)
(*  									*)
(* If C is specialized to some particular syntactic form, for example   *)
(* to `C1;;C2`, then most of the disjuncts in the conclusion become     *)
(* just false because of the syntactic inequality of different commands.*)
(* These false can be simplified away by rewriting with the theorem	*)
(* distinct.  The disjuncts that match the command to which C is 	*)
(* specialized can also be simplified by rewriting with const11.  This  *)
(* changes equalities between similar commands, for example:		*)
(*									*)
(*    (C1 ;; C2) = (C1' ;; C2')						*)
(*									*)
(* to equalities between their coresponding constitutents:		*)
(*									*)
(*    C1 = C1'  /\  C2 = C2'						*)
(*									*)
(* These can then generally be used for substitution.			*)
(* ---------------------------------------------------------------------*)

val (distinct,const11) =
  let val (SOME facts) = TypeBase.read {Thy="opsem", Tyop="comm"}
      val thm1 = TypeBase.distinct_of ``:comm``
      val thm2 = TypeBase.one_one_of ``:comm``
  in
    (CONJ thm1 (GSYM thm1),thm2)
  end;

val SIMPLIFY = REWRITE_RULE [distinct, const11];

(* --------------------------------------------------------------------- *)
(* CASE_TAC : this is applicable to goals of the form:			 *)
(*									 *)
(*      TRANS C s1 s2 ==> P						 *)
(*									 *)
(* When applied to such a goal, the antecedant is matched to the general *)
(* case analysis theorem and a corresponding instance of its conclusion  *)
(* is obtained.  This is simplified using the SIMPLIFY rule described    *)
(* above and the result is assumed in stripped form.  Given this tactic, *)
(* the sequence of theorems given below are simple to prove.  The proofs *)
(* are fairly uniform; with a careful analysis of the regularities, one  *)
(* should be able to devise an automatic proof procedure for deriving    *)
(* sets of theorems of this type.					 *)
(* --------------------------------------------------------------------- *)

val CASE_TAC = DISCH_THEN
               (STRIP_ASSUME_TAC o SIMPLIFY o ONCE_REWRITE_RULE[ecases]);

(* --------------------------------------------------------------------- *)
(* SKIP_THM : EVAL Skip s1 s2 is provable only by the Skip rule, which   *)
(* requires that s1 and s2 be the same state.				 *)
(* --------------------------------------------------------------------- *)

val SKIP_THM = store_thm("SKIP_THM",
     (--`!s1 s2. EVAL Skip s1 s2 = (s1 = s2)`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [CASE_TAC THEN ASM_REWRITE_TAC [],
      DISCH_THEN SUBST1_TAC THEN MAP_FIRST RULE_TAC rulel]);


(* --------------------------------------------------------------------- *)
(* ASSIGN_THM : EVAL (V ::= E) s1 s2 is provable only by the assignment	 *)
(* rule, which requires that s2 be the state s1 with V updated to E.	 *)
(* --------------------------------------------------------------------- *)

val ASSIGN_THM = store_thm ("ASSIGN_THM",
 (--`!s1 s2 V E. EVAL (V ::= E) s1 s2
                   =
                 ((\v. if v=V then E s1 else s1 v) = s2)`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [CASE_TAC THEN ASM_REWRITE_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_FIRST RULE_TAC rulel]);


(* --------------------------------------------------------------------- *)
(* SEQ_THM : EVAL (C1;;C2) s1 s2 is provable only by the sequencing      *)
(* rule, which requires that some intermediate state s3 exists such      *)
(* that C1 in state s1 terminates in s3 and C3 in s3 terminates in s2.   *)
(* --------------------------------------------------------------------- *)

val SEQ_THM = store_thm("SEQ_THM",
--`!s1 s2 C1 C2.EVAL (C1;;C2) s1 s2 = ?s3. EVAL C1 s1 s3 /\ EVAL C2 s3 s2`--,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [CASE_TAC THEN EXISTS_TAC (--`s2':^State`--) THEN ASM_REWRITE_TAC [],
   DISCH_THEN (fn th => MAP_FIRST RULE_TAC rulel THEN MATCH_ACCEPT_TAC th)]);


(* --------------------------------------------------------------------- *)
(* IF_T_THM : if B(s1) is true, then EVAL (If B C2 C2) s1 s2 is provable *)
(* only by the first conditional rule, which requires that C1 when	 *)
(* evaluated in s1 terminates in s2.					 *)
(* --------------------------------------------------------------------- *)

val IF_T_THM = store_thm ("IF_T_THM",
(--`!s1 s2 B C1 C2. B s1 ==> (EVAL (If B C1 C2) s1 s2 = EVAL C1 s1 s2)`--),
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [CASE_TAC THEN EVERY_ASSUM (TRY o SUBST_ALL_TAC) THENL
      [FIRST_ASSUM ACCEPT_TAC, RES_TAC],
      DISCH_TAC THEN MAP_FIRST RULE_TAC rulel THEN FIRST_ASSUM ACCEPT_TAC]);


(* --------------------------------------------------------------------- *)
(* IF_F_THM : if B(s1) is false, then EVAL (if B C1 C2) s1 s2 is 	 *)
(* provable only by the second conditional rule, which requires that C2	 *)
(* when evaluated in s1 terminates in s2.				 *)
(* --------------------------------------------------------------------- *)

val IF_F_THM = store_thm ("IF_F_THM",
(--`!s1 s2 B C1 C2. ~B s1 ==> (EVAL (If B C1 C2) s1 s2 = EVAL C2 s1 s2)`--),
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   [CASE_TAC THEN EVERY_ASSUM (TRY o SUBST_ALL_TAC) THENL
    [RES_TAC, FIRST_ASSUM ACCEPT_TAC],
     DISCH_TAC THEN MAP_FIRST RULE_TAC (rev rulel) THEN
     FIRST_ASSUM ACCEPT_TAC]);


(* ---------------------------------------------------------------------*)
(* WHILE_T_THM : if B(s1) is true, then EVAL (While B C) s1 s2 is 	*)
(* provable only by the corresponding While rule, which requires that 	*)
(* there is an intermediate state s3 such that C in state s1 terminates *)
(* in s3, and While B do C in state s3 terminates in s2.		*)
(* ---------------------------------------------------------------------*)

val WHILE_T_THM = store_thm ("WHILE_T_THM",
     (--`!s1 s2 B C.
      B s1 ==> (EVAL (While B C) s1 s2 =
                (?s3. EVAL C s1 s3 /\ EVAL (While B C) s3 s2))`--),
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   [CASE_TAC THEN EVERY_ASSUM (TRY o SUBST_ALL_TAC) THENL
    [RES_TAC,
     EXISTS_TAC (--`s2':^State`--) THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC],
    STRIP_TAC THEN MAP_FIRST RULE_TAC (rev rulel) THEN
    EXISTS_TAC (--`s3:^State`--) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);


(* ---------------------------------------------------------------------*)
(* WHILE_F_THM : if B(s1) is false, then EVAL (While B C) s1 s2 is	*)
(* provable only by the corresponding While rule, which requires that 	*)
(* s2 equals the original state s1					*)
(* ---------------------------------------------------------------------*)

val WHILE_F_THM = store_thm ("WHILE_F_THM",
     (--`!s1 s2 B C. ~B s1 ==> (EVAL (While B C) s1 s2 = (s1 = s2))`--),
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [CASE_TAC THENL
      [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC,
       EVERY_ASSUM (TRY o SUBST_ALL_TAC) THEN RES_TAC],
      DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_FIRST RULE_TAC rulel THEN
      FIRST_ASSUM ACCEPT_TAC]);


(* ===================================================================== *)
(* THEOREM: the operational semantics is deterministic.			 *)
(*									 *)
(* Given the suite of theorems proved above, this proof is relatively    *)
(* strightforward.  The standard proof is by structural induction on C,  *)
(* but the proof by rule induction given below gives rise to a slightly  *)
(* easier analysis in each case of the induction.  There are, however,   *)
(* more cases---one per rule, rather than one per constructor.		 *)
(* ===================================================================== *)

val DETERMINISTIC = store_thm ("DETERMINISTIC",
(--`!C st1 st2. EVAL C st1 st2 ==> !st3. EVAL C st1 st3 ==> (st2 = st3)`--),
     RULE_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC [SKIP_THM],
      REWRITE_TAC [ASSIGN_THM],
      PURE_ONCE_REWRITE_TAC [SEQ_THM] THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC [],
      IMP_RES_TAC IF_T_THM THEN ASM_REWRITE_TAC [],
      IMP_RES_TAC IF_F_THM THEN ASM_REWRITE_TAC [],
      IMP_RES_TAC WHILE_F_THM THEN ASM_REWRITE_TAC [],
      IMP_RES_THEN (fn th =>  PURE_ONCE_REWRITE_TAC [th]) WHILE_T_THM THEN
      STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      RES_TAC THEN ASM_REWRITE_TAC []]);


(* ===================================================================== *)
(* Definition of partial correctness and derivation of proof rules.	 *)
(* ===================================================================== *)

val SPEC_DEF = new_definition ("SPEC_DEF",
     (--`SPEC P C Q = !s1 s2. (P s1 /\ EVAL C s1 s2) ==> Q s2`--));

(* --------------------------------------------------------------------- *)
(* Proof of the While rule in Hoare logic.				 *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* In the following proofs, theorems of the form:			 *)
(*									 *)
(*     |- !y1...yn. (C x1 ... xn = C y1 ... yn) ==> tm[y1,...,yn]	 *)
(*									 *)
(* frequently arise, where C is one of the constructors of the data type *)
(* of commands.  The following theorem-tactic simplifies such theorems   *)
(* by specializing yi to xi and then removing the resulting trivially    *)
(* true antecedent.  The result is:					 *)
(*									 *)
(*     |- tm[x1,...,xn/y1,...,yn]					 *)
(*									 *)
(* which is passed to the theorem continuation function. The tactic just *)
(* discards theorems not of the form shown above.   For the While proof  *)
(* given below, this has the effect of thinning out useless induction	 *)
(* hypotheses of the form:						 *)
(*									 *)
(*     |- !B' C'. (C = While B' C') ==> tm[B',C']			 *)
(* 									 *)
(* These are just discarded.						 *)
(* --------------------------------------------------------------------- *)

fun REFL_MP_THEN ttac th =
   let val tm = lhs(fst(dest_imp(snd(strip_forall(concl th)))))
   in ttac (MATCH_MP th (REFL tm))
   end handle HOL_ERR _ => ALL_TAC;

(* --------------------------------------------------------------------- *)
(* The following lemma states that the condition B in While B C must be  *)
(* false upon termination of a While loop.  The proof is by a rule 	 *)
(* induction specialized to the While rule cases.  We show that the set	 *)
(* 									 *)
(*    {(While B C,s1,s2) | ~(B s2)} U {(C,s1,s2) | ~(C = While B' C')}   *)
(*									 *)
(* is closed under the rules for the evaluation relation. Note that this *)
(* formulation illustrates a general way of proving a property of some   *)
(* specific class of commands by rule induction.  One takes the union of *)
(* the set containing triples with the desired property and the set of   *)
(* all other triples whose command component is NOT an element of the    *)
(* class of commands of interest.					 *)
(*									 *)
(* The proof is trivial for all but the two While rules, since this set	 *)
(* contains all triples (C,s1,s2) for which C is not a While command.  	 *)
(* The subgoals corresponding to these cases are vacuously true, since 	 *)
(* they are implications with antecedents of the form (C = While B' C'), *)
(* where C is a command syntactically distinct from any While command.	 *)
(*									 *)
(* Showing that the above set is closed under the two While rules is     *)
(* likewise trivial.  For the While axiom, we get ~(B s2) immediately 	 *)
(* from the side condition. For the other While rule, the statement to	 *)
(* prove is just one of the induction hypotheses; since RULE_INDUCT_TAC  *)
(* uses STRIP_ASSUME_TAC on this hypothesis, this subgoal is solved	 *)
(* immediately.								 *)
(* --------------------------------------------------------------------- *)


val WHILE_LEMMA1 = TAC_PROOF(([],
 (--`!C s1 s2. EVAL C s1 s2 ==> !B' C'. (C = While B' C') ==> ~(B' s2)`--)),
     RULE_INDUCT_TAC THEN REWRITE_TAC [distinct, const11] THEN
     REPEAT GEN_TAC THEN DISCH_THEN (STRIP_THM_THEN SUBST_ALL_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

(* ---------------------------------------------------------------------*)
(* The second lemma deals with the invariant part of the Hoare proof 	*)
(* rule for While commands.  We show that if P is an invariant of C, 	*)
(* then it is also an invariant of While B C.  The proof is essentially *)
(* an induction on the number of applications of the evaluation rule for*)
(* While commands.  This is expressed as a rule induction, which 	*)
(* establishes that the set:						*)
(*									*)
(*    {(While B C,s1,s2) | P invariant of C ==> (P s1 ==> P s2)}	*)
(*									*)
(* is closed under the transition rules.  As in lemma 1, the rules for  *)
(* other kinds of commands are dealt with by taking the union of this 	*)
(* set with 								*)
(* 									*)
(*    {(C,s1,s2) | ~(C = While B' C')}					*)
(*									*)
(* Closure under evaluation rules other than the two rules for While is *)
(* therefore trivial, as outlined in the comments to lemma 1 above. 	*)
(*									*)
(* The proof in fact proceeds by strong rule induction.  With ordinary  *)
(* rule induction, one obtains hypotheses that are too weak to imply the*)
(* desired conclusion in the step case of the While rule.  To see why, 	*)
(* try replacing strong by weak induction in the tactic proof below.	*)
(*									*)
(* Note that REFL_MP_THEN is used to simplify the induction hypotheses  *)
(* before adding them to the assumption list.  This avoids having the 	*)
(* assumptions in an awkward form (try using ASSUME_TAC instead). Note	*)
(* also that in the case of the While axiom, the states s1 and s2 are	*)
(* identical, so the corresponding subgoal is trivial and is solved by	*)
(* the rewriting step.							*)
(* ---------------------------------------------------------------------*)

val WHILE_LEMMA2 =
    TAC_PROOF(([],
  --`!C s1 s2.
     EVAL C s1 s2 ==>
     !B' C'. (C = While B' C') ==>
             (!s1 s2. P s1 /\ B' s1 /\ EVAL C' s1 s2 ==> P s2) ==>
             (P s1 ==> P s2)`--),
     RULE_INDUCT_THEN sind (REFL_MP_THEN ASSUME_TAC) ASSUME_TAC THEN
     REWRITE_TAC [distinct, const11] THEN REPEAT GEN_TAC THEN
     DISCH_THEN (STRIP_THM_THEN SUBST_ALL_TAC) THEN
     REPEAT STRIP_TAC THEN RES_TAC);

(* ---------------------------------------------------------------------*)
(* The proof rule for While commands in Hoare logic is:			*)
(*									*)
(*         |- {P /\ B} C {P}						*)
(*      ----------------------						*)
(*        |- {P} C {P /\ ~B}						*)
(* 									*)
(* Given the two lemmas proved above, it is trivial to prove this rule. *)
(* The antecedent of the rule is just the assumption of invariance of P *)
(* for C which occurs in lemma 2.  Note that REFL_MP_THEN is used to    *)
(* simplify the conclusions of the lemmas after one resolution step.	*)
(* ---------------------------------------------------------------------*)

val WHILE = store_thm ("WHILE",
     (--`!P C. SPEC (\s. P s /\ B s) C P ==>
            SPEC P (While B C) (\s. P s /\ ~B s)`--),
     PURE_ONCE_REWRITE_TAC [SPEC_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL CONJ_ASSOC)] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_THEN (REFL_MP_THEN IMP_RES_TAC) WHILE_LEMMA2,
      IMP_RES_THEN (REFL_MP_THEN IMP_RES_TAC) WHILE_LEMMA1]);

(* ---------------------------------------------------------------------*)
(* End of example.							*)
(* ---------------------------------------------------------------------*)

val _ = export_theory();

end;
