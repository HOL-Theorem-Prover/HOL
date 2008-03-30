(* ===================================================================== *)
(* File		: algebraScript.sml                                      *)
(* DESCRIPTION  : Maximal trace semantics and transition semantics of a  *)
(*		  small process algebra.              			 *)
(*									 *)
(* AUTHORS	: Juanito Camilleri and Tom Melham		       	 *)
(* DATE		: 91.05.13						 *)
(* ===================================================================== *)

(*
  app load ["stringLib"];
*)

structure algebraScript =
struct

(* --------------------------------------------------------------------- *)
(* Open a new theory and load the inductive definitions library and      *)
(* other libraries.                                                      *)
(* --------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib 
     listTheory IndDefRules IndDefLib stringLib;

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

val _ = type_abbrev ("label",``:string``);

val _ = 
 Hol_datatype 
    `agent = Nil
           | Pre of  label => agent
           | Sum of  agent => agent
           | Prod of agent => agent`;


(* ===================================================================== *)
(* Definition of a maximal trace semantics for the process algebra.	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Type abbreviation for traces.   These are just finite sequences of 	 *)
(* labels, represented here by lists.					 *)
(* --------------------------------------------------------------------- *)

val _ = type_abbrev("trace", ``:label list``);

(* --------------------------------------------------------------------- *)
(* Inductive definition of a trace relation MTRACE.  This is defined so	 *)
(* that MTRACE P A means A is the maximal trace of the process P. The 	 *)
(* definition is done inductively by the rules given below.	     	 *)
(* --------------------------------------------------------------------- *)

val (trules, tind, tcases) = Hol_reln
     `MTRACE Nil []
 /\   (!P A a. MTRACE P A ==> MTRACE (Pre a P) (a::A))
 /\   (!P Q A. MTRACE P A ==> MTRACE (Sum P Q) A)
 /\   (!P Q A. MTRACE Q A ==> MTRACE (Sum P Q) A)
 /\   (!P Q A. MTRACE P A /\ MTRACE Q A ==> MTRACE (Prod P Q) A)`;


val trulel = CONJUNCTS trules;

(* --------------------------------------------------------------------- *)
(* Stronger form of rule induction.					 *)
(* --------------------------------------------------------------------- *)

val tsind = derive_strong_induction (trules,tind);

(* --------------------------------------------------------------------- *)
(* Definition of a terminal process: one with [] as a maximal trace.	 *)
(* --------------------------------------------------------------------- *)

val TERMINAL_def =
 Define
   `TERMINAL P = MTRACE P []`;

(* ===================================================================== *)
(* Inductive definition of a labelled transition system.                 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We now define a labelled transition relation TRANS P l Q to mean	 *)
(* there that process P can participate in action l and thereby evolve	 *)
(* into process Q.  The definition is done inductively, as usual.        *)
(* --------------------------------------------------------------------- *)

val (lrules, lind, lcases) = Hol_reln
    `(!Q a. TRANS (Pre a Q) a Q)
 /\  (!P P' Q a. TRANS P a P' ==> TRANS (Sum P Q) a P')
 /\  (!P Q Q' a. TRANS Q a Q' ==> TRANS (Sum P Q) a Q')
 /\  (!P P' Q Q' a. TRANS P a P' /\ TRANS Q a Q'
                ==> TRANS (Prod P Q) a (Prod P' Q'))`;

val lrulel = CONJUNCTS lrules;

(* --------------------------------------------------------------------- *)
(* Strong form of rule induction for TRANS.	      			 *)
(* --------------------------------------------------------------------- *)

val lsind = derive_strong_induction (lrules,lind);


(* ===================================================================== *)
(* Inductive definition of a trace transition system                	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We now define a transition system that accumulates the trace of a	 *)
(* process.  This is essentially the reflexive-transitive closure of	 *)
(* TRANS, but with the label being a list of the labels from TRANS.	 *)
(* --------------------------------------------------------------------- *)

val (Lrules, Lind, Lcases) = Hol_reln
   `(!P. TRANSIT P [] P)
/\  (!P P' B a Q. TRANS P a Q /\ TRANSIT Q B P' ==> TRANSIT P (a::B) P')`;

val Lrulel = CONJUNCTS Lrules;

(* --------------------------------------------------------------------- *)
(* Strong form of rule induction for labelled (trace) transitions.       *)
(* --------------------------------------------------------------------- *)

val Lsind = derive_strong_induction (Lrules,Lind);

(* ===================================================================== *)
(* Theorem 1: Maximal trace semantics "agrees' with transition semantics *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Lemma 1 is to prove the following theorem:				 *)
(*									 *)
(*    |- !P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (a::A)      *)
(*									 *)
(* The proof is a straightforward rule induction on TRANS, followed by	 *)
(* a case analysis on MTRACE Q A when Q is a product (Prod), and then	 *)
(* completed by a simple search for the proof of the conclusion using 	 *)
(* the tactic MTRACE_TAC.						 *)
(* --------------------------------------------------------------------- *)

val Lemma1 = Q.prove
(`!P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (a::A)`,
 HO_MATCH_MP_TAC lind THEN RW_TAC std_ss [] THENL
 [METIS_TAC trulel,
  METIS_TAC trulel,
  METIS_TAC trulel,
  RULE_ASSUM_TAC (REWRITE_RULE [Once tcases]) THEN 
   FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss [] THEN
   METIS_TAC [trules]]);

(* --------------------------------------------------------------------- *)
(* Theorem 1:  |- !P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A    *)
(*									 *)
(* This theorem shows that the trace semantics agrees with the 		 *)
(* trace-transition semantics, in the sense that if we follow the	 *)
(* transitions of a process P until we reach a terminal process Q, that	 *)
(* is a process with an empty maximal trace, then we will have gone	 *)
(* through a maximal trace of P.					 *)
(* --------------------------------------------------------------------- *)

val Theorem1 = Q.store_thm
("Theorem1",
 `!P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A`,
 REWRITE_TAC [TERMINAL_def] THEN
 HO_MATCH_MP_TAC Lind THEN METIS_TAC [Lemma1]);


(* --------------------------------------------------------------------- *)
(* Corollary 1: !P A Q. TRANSIT P A Nil ==> MTRACE P A                   *)
(*									 *)
(* Note that the converse does not hold.				 *)
(* --------------------------------------------------------------------- *)

val Corollary1 = Q.store_thm
("Corollary1",
 `!P A. TRANSIT P A Nil ==> MTRACE P A`,
 METIS_TAC (TERMINAL_def::Theorem1::trulel));


(* ===================================================================== *)
(* Theorem 2: Transition semantics "agrees" with maximal trace semantics *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Lemma 2 shows that the trace of a product is just the trace of its	 *)
(* two components in the relation TRANSIT. The proof is a sraightfoward	 *)
(* structural induction on the list A, with simplification using the     *)
(* case analysis theorem for TRANSIT.					 *)
(* --------------------------------------------------------------------- *)

val Lemma2 = Q.prove
(`!A P Q P' Q'.
    TRANSIT P A Q /\ TRANSIT P' A Q' ==> TRANSIT (Prod P P') A (Prod Q Q')`,
 Induct THEN PURE_ONCE_REWRITE_TAC [Lcases] THEN 
  RW_TAC std_ss [] THEN METIS_TAC lrulel);

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

val Theorem2 = Q.store_thm 
("Theorem2",
 `!P A. MTRACE P A ==> ?Q. TRANSIT P A Q /\ TERMINAL Q`,
 HO_MATCH_MP_TAC tind THEN RW_TAC std_ss [] THENL
 [METIS_TAC (TERMINAL_def::Lrulel@trulel@lrulel),
  METIS_TAC (Lrulel@trulel@lrulel),
  RULE_ASSUM_TAC (REWRITE_RULE [Once Lcases]) 
    THEN RW_TAC list_ss [] 
    THEN METIS_TAC (TERMINAL_def::Lrulel@trulel@lrulel),
  RULE_ASSUM_TAC (REWRITE_RULE [Once Lcases]) 
    THEN RW_TAC list_ss [] 
    THEN METIS_TAC (TERMINAL_def::Lrulel@trulel@lrulel),
  METIS_TAC (Lemma2::TERMINAL_def::Lrulel@trulel@lrulel)]);


(* ===================================================================== *)
(* Theorem3: The transition and maximal trace semantics "agree".	 *)
(* ===================================================================== *)

val Theorem3 = Q.store_thm
("Theorem3",
 `!P A. MTRACE P A = ?Q. TRANSIT P A Q /\ TERMINAL Q`,
 METIS_TAC [Theorem1,Theorem2]);


(* ===================================================================== *)
(* Definitions of notions of equivalence                                 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Maximal trace equivalence. Two processes are maximal trace equivalent *)
(* if they have the same maximal traces.				 *)
(* --------------------------------------------------------------------- *)

val _ = set_fixity "MEQUIV" (Infixl 701);
val _ = set_fixity "BEQUIV" (Infixl 701);

val MEQUIV_def =
 Define
  `(P MEQUIV Q) = !A. MTRACE P A = MTRACE Q A`;

(* --------------------------------------------------------------------- *)
(* Bisimulation equivalence.  A binary relation s:agent->agent->bool is  *)
(* a simulation if s P Q implies that any transitions that P can do can  *)
(* also be done by Q such that the corresponding successive pairs of	 *)
(* agents remain in the relation s.  Equivalence is then defined to be 	 *)
(* the bisimulation (simulation whose inverse is also a simulation).	 *)
(* --------------------------------------------------------------------- *)

val SIM_def =
 Define
   `SIM s = !P Q. s P Q ==> 
                   !a P'. TRANS P a P' ==> 
                           ?Q'. TRANS Q a Q' /\ s P' Q'`;

val BEQUIV_def =
 Define
   `(P BEQUIV Q) = ?s. SIM s /\ s P Q /\ SIM(\x y. s y x)`;


(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

val _ = export_theory();

end;


