(* =====================================================================*)
(* FILE		: milScript.sml						*)
(* DESCRIPTION   : Defines a proof system for minimal intuitionistic 	*)
(*                 logic, and proves the Curry-Howard isomorphism for	*)
(*                 this and typed combinatory logic.			*)
(*									*)
(* AUTHOR	: Tom Melham and Juanito Camilleri			*)
(* DATE		: 90.12.03						*)
(* =====================================================================*)

(*
  app load ["IndDefLib", "Datatype", "clTheory"] ;
*)

structure milScript =
struct

open HolKernel Parse boolLib
     IndDefLib IndDefRules Datatype clTheory;

infix ## |-> THEN THENL THENC ORELSE; infixr 3 -->;



(* --------------------------------------------------------------------- *)
(* Open a new theory and load the inductive definitions library.	 *)
(* --------------------------------------------------------------------- *)

val _ = new_theory"mil";

(* ===================================================================== *)
(* Combinatory logic types and type judgements.				 *)
(* ===================================================================== *)

val _ = Hol_datatype `ty = G  of 'a  
                         | -> of ty => ty`;

val _ = set_fixity "->" (Infixr 800);
val _ = set_MLname "->" "ARROW_DEF";

(* ===================================================================== *)
(* Standard syntactic theory, derived by the recursive types package.	 *)
(* ===================================================================== *)

val SOME tyfacts = TypeBase.read {Thy="mil", Tyop="ty"};

(* --------------------------------------------------------------------- *)
(* structural induction theorem for ty.                                  *)
(* --------------------------------------------------------------------- *)

val ty_induct = TypeBase.induction_of ``:'a ty``;

(* --------------------------------------------------------------------- *)
(* cases theorem for ty.                                                 *)
(* --------------------------------------------------------------------- *)

val ty_cases = TypeBase.nchotomy_of ``:'a ty``;

(* --------------------------------------------------------------------- *)
(* The constructors of the type :ty yield syntactically distinct         *)
(* values. One typically needs all symmetric forms of the inequalities,  *)
(* so we package them all together here.                                 *)
(* --------------------------------------------------------------------- *)

val ty_distinct =
   let val distinct = TypeBase.distinct_of ``:'a ty``
       val ths = CONJUNCTS distinct
       val rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths
   in 
     LIST_CONJ (ths @ rths)
   end;

(* --------------------------------------------------------------------- *)
(* The constructors Pre, Sum and Prod are one-to-one.                    *)
(* --------------------------------------------------------------------- *)

val Gfun11 =
   let val one2 = TypeBase.one_one_of ``:'a ty``
   in CONJUNCTS one2
   end;


(* ===================================================================== *)
(* Definition of well-typed terms of combinatory logic.			 *)
(* ===================================================================== *)

val _ = set_fixity "IN" (Infixr 700);

val (TYrules,TYind,TYcases) = Hol_reln
    `(!A B.   K IN (A -> B -> A))
 /\  (!A B C. S IN ((A -> B -> C) -> (A -> B) -> (A -> C)))
 /\  (!M N t2.  (?t1. M IN (t1 -> t2) /\ N IN t1) ==> (M#N) IN t2)`;


val TYrules = CONJUNCTS TYrules;

(* ======================================================================== *)
(* Mimimal intuitionistic logic.  We now reinterpret -> as implication,     *)
(* types P:('a)ty as terms of the logic (i.e. propositions), and define a   *)
(* provability predicate `THM` on these terms. The definition is done       *)
(* inductively by the proof rules for the logic.			    *)
(* ======================================================================== *)

val (THMrules, THMind, THMcases) = 
 Hol_reln
    `(!A B.    THM (A -> B -> A))
 /\  (!A B C.  THM ((A -> B -> C) -> (A -> B) -> (A -> C)))
 /\  (!Q. (?P. THM (P -> Q) /\ THM P) ==> THM Q)`;

val THMrules = CONJUNCTS THMrules;

(* ===================================================================== *)
(* Derivation of the Curry-Howard isomorphism.				 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* The left-to-right direction is proved by rule induction for the	 *)
(* inductively defined relation THM, followed by use of the typing rules *)
(* (i.e. the tactics for them) to prove the conclusion. The proof is	 *)
(* completely straightforward.						 *)
(* (kls) existential witness P' not used, since hol90 does not do the    *)
(* (unnecessary) renaming that hol88 does.                               *)
(* --------------------------------------------------------------------- *)

val ISO_THM1 = Q.prove
(`!P. THM P ==> ?M. M IN P`,
 RULE_INDUCT_THEN THMind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
 REPEAT GEN_TAC THENL map Q.EXISTS_TAC [`K`, `S`, `M # M'`] THEN
 MAP_FIRST RULE_TAC TYrules THEN
 Q.EXISTS_TAC `P` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);

(* --------------------------------------------------------------------- *)
(* The proof for the other direction proceeds by induction over the 	 *)
(* typing relation.  Again, simple.					 *)
(* --------------------------------------------------------------------- *)

val ISO_THM2 =
    TAC_PROOF
    (([], (--`!P:'a ty. !M:cl. M IN P ==> THM P`--)),
     RULE_INDUCT_THEN TYind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
     REPEAT GEN_TAC THEN
     MAP_FIRST RULE_TAC THMrules THEN
     EXISTS_TAC (--`t1:'a ty`--) THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);

(* --------------------------------------------------------------------- *)
(* The final result.							 *)
(* --------------------------------------------------------------------- *)

val CURRY_HOWARD = store_thm
    ("CURRY_HOWARD",
    (--`!P:'a ty. THM P = ?M:cl. M IN P`--),
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    IMP_RES_TAC (CONJ ISO_THM1 ISO_THM2) THEN
    EXISTS_TAC (--`M:cl`--) THEN FIRST_ASSUM ACCEPT_TAC);


(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

val _ = export_theory();

end;
