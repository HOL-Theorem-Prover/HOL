(* ===================================================================== *)
(* File		: algebra.ml						 *)
(* DESCRIPTION  : Maximal trace semantics and transition semantics of a  *)
(*		  small process algebra.              			 *)
(*									 *)
(* AUTHORS	: Juanito Camilleri and Tom Melham		       	 *)
(* DATE		: 91.05.13						 *)
(* ===================================================================== *)

(*
  app load ["IndDefLib", "stringLib", "bossLib"];
*)

structure algebraScript =
struct

(* --------------------------------------------------------------------- *)
(* Open a new theory and load the inductive definitions library and      *)
(* other libraries.                                                      *)
(* --------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib
     IndDefLib IndDefRules listTheory;

local open stringTheory in end;

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;


val _ = new_theory "algebra";


(* ===================================================================== *)
(* Syntax of a small process algebra		        		 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We use the recursive types package to define the syntax of a small	 *)
(* process algebra, with processes					 *)
(*									 *)
(*    agent  ::=   Nil                    [does nothing]		 *)
(*               | Pre  label agent       [prefix agent with label]	 *)
(*               | Sum  agent agent       [nondeterministic choice]	 *)
(*	         | Prod agent agent       [composition]			 *)
(*									 *)
(* The different syntactic classes of processes are thus represented by  *)
(* the constructors (constant functions):				 *)
(*									 *)
(*  Nil:agent, Pre:label->agent->agent, Sum and Prod:agent->agent->agent *)
(*									 *)
(* for the concrete data type :agent.  The type :label here is just an	 *)
(* abbreviation for :string.						 *)
(* --------------------------------------------------------------------- *)

val  label = Type`:string`;

val _ = Hol_datatype `agent
                        = Nil
                        | Pre of  ^label => agent
                        | Sum of   agent => agent
                        | Prod of  agent => agent`;


(* --------------------------------------------------------------------- *)
(* structural induction theorem for agent.                               *)
(* --------------------------------------------------------------------- *)

val induct = TypeBase.induction_of "agent";

(* --------------------------------------------------------------------- *)
(* cases theorem for agent.                                              *)
(* --------------------------------------------------------------------- *)

val cases = TypeBase.nchotomy_of "agent";

(* --------------------------------------------------------------------- *)
(* The constructors of the type :agent yield syntactically distinct      *)
(* values. One typically needs all symmetric forms of the inequalities,  *)
(* so we package them all together here.                                 *)
(* --------------------------------------------------------------------- *)

val distinct =
   let val ths = CONJUNCTS (TypeBase.distinct_of "agent")
       val rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths
   in
     LIST_CONJ (ths @ rths)
   end;

(* --------------------------------------------------------------------- *)
(* The constructors Pre, Sum and Prod are one-to-one.                    *)
(* --------------------------------------------------------------------- *)

val agent11 = CONJUNCTS (TypeBase.one_one_of "agent");

(* ===================================================================== *)
(* Definition of a maximal trace semantics for the process algebra.	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Traces are just finite sequences of labels, represented by lists      *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Inductive definition of a trace relation MTRACE.  This is defined so	 *)
(* that MTRACE P A means A is the maximal trace of the process P. The 	 *)
(* definition is done inductively by the rules given below.	     	 *)
(* --------------------------------------------------------------------- *)

val (trules,tind,tcases) = 
  IndDefLib.Hol_reln
   `(MTRACE Nil []) /\
    (!P A a. MTRACE P A ==> MTRACE (Pre a P) (a::A)) /\
    (!P Q A. MTRACE P A ==> MTRACE (Sum P Q) A) /\
    (!P Q A. MTRACE Q A ==> MTRACE (Sum P Q) A) /\
    (!P Q A. MTRACE P A /\
             MTRACE Q A ==> MTRACE (Prod P Q) A)`;

(* --------------------------------------------------------------------- *)
(* Stronger form of rule induction.					 *)
(* --------------------------------------------------------------------- *)

val tsind = IndDefRules.derive_strong_induction (CONJUNCTS trules,tind);

(* --------------------------------------------------------------------- *)
(* Definition of a terminal process: one with [] as a maximal trace.	 *)
(* --------------------------------------------------------------------- *)

val TERMINAL_DEF =
    new_definition ("TERMINAL_DEF", Term`TERMINAL P = MTRACE P []`);

(* --------------------------------------------------------------------- *)
(* Standard rule induction tactic for MTRACE. This uses the weaker form  *)
(* of the rule induction theorem, and both premisses and side conditions *)
(* are just assumed (in stripped form).  				 *)
(* --------------------------------------------------------------------- *)

val MTRACE_INDUCT_TAC =
    RULE_INDUCT_THEN tind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* ===================================================================== *)
(* Inductive definition of a labelled transition system.                 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We now define a labelled transition relation TRANS P l Q to mean	 *)
(* that process P can participate in action l and thereby evolve into	 *)
(* process Q.  The definition is done inductively, as usual.             *)
(* --------------------------------------------------------------------- *)

val (lrules,lind,lcases) =
  Hol_reln
     `(!a Q. TRANS (Pre a Q) a Q) /\
      (!a P P' Q. TRANS P a P' ==> TRANS (Sum P Q) a P') /\
      (!a P Q Q'. TRANS Q a Q' ==> TRANS (Sum P Q) a Q') /\
      (!a P P' Q Q'. TRANS P a P' /\ 
                     TRANS Q a Q' ==> TRANS (Prod P Q) a (Prod P' Q'))`;

(* --------------------------------------------------------------------- *)
(* Strong form of rule induction for TRANS.	      			 *)
(* --------------------------------------------------------------------- *)

val lsind = derive_strong_induction (CONJUNCTS lrules,lind);

(* ===================================================================== *)
(* Inductive definition of a trace transition system                	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We now define a transition system that accumulates the trace of a	 *)
(* process.  This is essentially the reflexive-transitive closure of	 *)
(* TRANS, but with the label being a list of the labels from TRANS.	 *)
(* --------------------------------------------------------------------- *)

val (Lrules,Lind,Lcases) =
 Hol_reln
   `(!P. TRANSIT P [] P) /\
    (!a P P' B. (?Q. TRANS P a Q /\ TRANSIT Q B P') ==> TRANSIT P (a::B) P')`;

(* --------------------------------------------------------------------- *)
(* Strong form of rule induction for labelled (trace) transitions.       *)
(* --------------------------------------------------------------------- *)

val Lsind = derive_strong_induction (CONJUNCTS Lrules,Lind);

(* --------------------------------------------------------------------- *)
(* Rule induction tactic for TRANSIT.					 *)
(* --------------------------------------------------------------------- *)

val TRANSIT_INDUCT_TAC = RULE_INDUCT_THEN Lind ASSUME_TAC ASSUME_TAC;

(* ===================================================================== *)
(* Theorem 1: Maximal trace semantics "agrees' with transition semantics *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Lemma 1 is to prove the following theorem:				 *)
(*									 *)
(*    |- !P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (CONS a A)  *)
(*									 *)
(* The proof is a straightforward rule induction on TRANS, followed by	 *)
(* a case analysis on MTRACE Q A when Q is a product (Prod), and then	 *)
(* completed by a simple search for the proof of the conclusion using 	 *)
(* the tactic MTRACE_TAC.						 *)
(* --------------------------------------------------------------------- *)

val Lemma1 = prove
(--`!P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (a::A)`--,
 HO_MATCH_MP_TAC lind 
 THEN REPEAT CONJ_TAC
 THENL [ALL_TAC,ALL_TAC,ALL_TAC,
        REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC 
          THEN DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [tcases]) 
          THEN RW_TAC std_ss []]
 THEN PROVE_TAC [trules]);

(* --------------------------------------------------------------------- *)
(* Theorem 1:  |- !P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A    *)
(*									 *)
(* This theorem shows that the trace semantics agrees with the 		 *)
(* trace-transition semantics, in the sense that if we follow the	 *)
(* transitions of a process P until we reach a terminal process Q, that	 *)
(* is a process with an empty maximal trace, then we will have gone	 *)
(* through a maximal trace of P.					 *)
(* --------------------------------------------------------------------- *)

val Theorem1 = store_thm ("Theorem1",
--`!P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A`--,
  TRANSIT_INDUCT_TAC THEN PROVE_TAC [Lemma1,TERMINAL_DEF]);

(* --------------------------------------------------------------------- *)
(* Corollary 1: !P A Q. TRANSIT P A Nil ==> MTRACE P A                   *)
(*									 *)
(* Note that the converse does not hold.				 *)
(* --------------------------------------------------------------------- *)

val Corollary1 = store_thm ("Corollary1",
  --`!P A. TRANSIT P A Nil ==> MTRACE P A`--,
  PROVE_TAC [Theorem1,TERMINAL_DEF,trules]);

(* ===================================================================== *)
(* Theorem 2: Transition semantics "agrees" with maximal trace semantics *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Lemma 2 shows that the trace of a product is just the trace of its	 *)
(* two components in the relation TRANSIT. The proof is a sraightfoward	 *)
(* structural induction on the list A, with simplification using the     *)
(* case analysis theorem for TRANSIT.					 *)
(* --------------------------------------------------------------------- *)

val Lemma2 = prove
(--`!A P Q P' Q'.
    TRANSIT P A Q /\ TRANSIT P' A Q' ==> TRANSIT (Prod P P') A (Prod Q Q')`--,
 Induct THEN PURE_ONCE_REWRITE_TAC [Lcases] 
        THEN RW_TAC std_ss [] 
        THEN PROVE_TAC [Lrules,lrules]);

(* --------------------------------------------------------------------- *)
(* Theorem 2:  |- !P A. MTRACE P A ==> ?Q. TRANSIT P A Q /\ TERMINAL Q	 *)
(*									 *)
(* This theorem shows that the transition semantics "agrees" with the	 *)
(* trace semantics, in the sense that every maximal trace A leads in the *)
(* transition semantics to a terminal process.  The proof proceeds by	 *)
(* rule induction on MTRACE P A, followed by semi-automatic search for 	 *)
(* proofs of TRANSIT P A Q and TERMINAL Q.  The user supplies a witness  *)
(* for any existential goals that arise.  There is also a case analysis  *)
(* on the TRANSIT assumption in the Sum cases, there being different 	 *)
(* witnesses required for the two TRANSIT rules.			 *)
(* --------------------------------------------------------------------- *)

val Theorem2 = store_thm ("Theorem2",
(--`!P A. MTRACE P A ==> ?Q. TRANSIT P A Q /\ TERMINAL Q`--),
  PURE_ONCE_REWRITE_TAC [TERMINAL_DEF] 
    THEN MTRACE_INDUCT_TAC
    THENL [ALL_TAC, ALL_TAC, 
           RULE_ASSUM_TAC(ONCE_REWRITE_RULE [Lcases]) THEN RW_TAC std_ss [],
           RULE_ASSUM_TAC(ONCE_REWRITE_RULE [Lcases]) THEN RW_TAC std_ss [],
           ALL_TAC]
    THEN PROVE_TAC [Lrules,trules,lrules,Lemma2]);

(* ===================================================================== *)
(* Theorem3: The transition and maximal trace semantics "agree".	 *)
(* ===================================================================== *)

val Theorem3 =
    store_thm
    ("Theorem3",
     --`!P A. MTRACE P A = ?Q. TRANSIT P A Q /\ TERMINAL Q`--,
    PROVE_TAC [Theorem2,Theorem1]);


(* ===================================================================== *)
(* Definitions of notions of equivalence                                 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Maximal trace equivalence. Two processes are maximal trace equivalent *)
(* if they have the same maximal traces.				 *)
(* --------------------------------------------------------------------- *)

val MEQUIV_DEF =
    new_infixl_definition
    ("MEQUIV_DEF",
     (--`MEQUIV P Q = (!A. MTRACE P A = MTRACE Q A)`--),725);

(* --------------------------------------------------------------------- *)
(* Bisimulation equivalence.  A binary relation s:agent->agent->bool is  *)
(* a simulation if s P Q implies that any transitions that P can do can  *)
(* also be done by Q such that the corresponding successive pairs of	 *)
(* agents remain in the relation s.  Equivalence is then defined to be 	 *)
(* the bisimulation (simulation whose inverse is also a simulation).	 *)
(* --------------------------------------------------------------------- *)

val SIM_DEF =
    new_definition
    ("SIM_DEF",
     (--`SIM s =
      !P Q. s P Q ==>
            !a P'. TRANS P a P' ==> ?Q'. TRANS Q a Q' /\ s P' Q'`--));

val BEQUIV_DEF =
    new_infixl_definition
    ("BEQUIV_DEF",
     (--`BEQUIV P Q = ?s. SIM s /\ s P Q /\ SIM(\x y. s y x)`--),725);


(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

val _ = export_theory();

end;
