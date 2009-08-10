(* =====================================================================*)
(* FILE		: milScript.sml						*)
(* DESCRIPTION  : Defines a proof system for minimal intuitionistic 	*)
(*                logic, and proves the Curry-Howard isomorphism for	*)
(*                this and typed combinatory logic.			*)
(* AUTHOR	: Tom Melham and Juanito Camilleri			*)
(* DATE		: 90.12.03						*)
(* =====================================================================*)

(*
  app load ["IndDefLib", "clTheory"] ;
*)

structure milScript =
struct

open HolKernel Parse boolLib bossLib
     IndDefLib IndDefRules clTheory;

(* --------------------------------------------------------------------- *)
(* Open a new theory and load the inductive definitions library.	 *)
(* --------------------------------------------------------------------- *)

val _ = new_theory "mil";

(* ===================================================================== *)
(* Combinatory logic types and type judgements.				 *)
(* ===================================================================== *)

val _ =
 Hol_datatype `ty = G  of 'a
                  | -> of ty => ty`;

val _ = set_fixity "->" (Infixr 800);
val _ = set_MLname "->" "ARROW_DEF";

(* ===================================================================== *)
(* Definition of well-typed terms of combinatory logic.			 *)
(* ===================================================================== *)

val _ = set_fixity "IN" (Infixr 700);

val (TYrules,TYind,TYcases) = Hol_reln
    `(!A B.   K IN (A -> B -> A))
 /\  (!A B C. S IN ((A -> B -> C) -> (A -> B) -> (A -> C)))
 /\  (!M N t1 t2.  M IN (t1 -> t2) /\ N IN t1 ==> (M#N) IN t2)`;


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
 /\  (!Q P.    THM (P -> Q) /\ THM P ==> THM Q)`;

val THMrules = CONJUNCTS THMrules;

(* ===================================================================== *)
(* Derivation of the Curry-Howard isomorphism.				 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* The left-to-right direction is proved by rule induction for the	 *)
(* inductively defined relation THM, followed by use of the typing rules *)
(* to prove the conclusion. The proof is completely straightforward.     *)
(* --------------------------------------------------------------------- *)

val ISO_THM1 = Q.prove
(`!P. THM P ==> ?M. M IN P`,
 HO_MATCH_MP_TAC THMind THEN RW_TAC std_ss [] THEN METIS_TAC TYrules);

(* --------------------------------------------------------------------- *)
(* The proof for the other direction proceeds by induction over the 	 *)
(* typing relation.  Again, simple.					 *)
(* --------------------------------------------------------------------- *)

val ISO_THM2 = Q.prove
(`!M P. M IN P ==> THM P`,
 HO_MATCH_MP_TAC TYind THEN RW_TAC std_ss [] THEN METIS_TAC THMrules);


(* --------------------------------------------------------------------- *)
(* The final result.							 *)
(* --------------------------------------------------------------------- *)

val CURRY_HOWARD = Q.store_thm
("CURRY_HOWARD",
 `!P:'a ty. THM P = ?M:cl. M IN P`,
 METIS_TAC [ISO_THM1,ISO_THM2]);

(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

val _ = export_theory();

end;
