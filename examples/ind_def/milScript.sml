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
  app load ["ind_defLib", "Datatype", "clTheory"] ;
*)

structure milScript =
struct

open HolKernel Parse boolLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

open IndDefLib Datatype clTheory;


(* --------------------------------------------------------------------- *)
(* Open a new theory and load the inductive definitions library.	 *)
(* --------------------------------------------------------------------- *)
val _ = new_theory"mil";

(* ===================================================================== *)
(* Combinatory logic types and type judgements.				 *)
(* ===================================================================== *)

(* ----------------------------------------------------------------------
    Overloading of implication symbol is perhaps a little dangerous
    because of potential for confusion, but works well in this example.
   ---------------------------------------------------------------------- *)

val _ = Hol_datatype `ty = G  of 'a
                         | ==> of ty => ty`;

val _ = set_MLname "==>" "Arrow_def";

(* --------------------------------------------------------------------- *)
(* Structural induction theorem for types.				 *)
(* --------------------------------------------------------------------- *)

val tyinfo = valOf (TypeBase.read "ty");
val ty_induct = TypeBase.induction_of "ty";

(* --------------------------------------------------------------------- *)
(* Exhaustive case analysis theorem for types.				 *)
(* --------------------------------------------------------------------- *)

val ty_cases = TypeBase.nchotomy_of "ty"

(* --------------------------------------------------------------------- *)
(* The arrow and ground type constructors are one-to-one.	         *)
(* --------------------------------------------------------------------- *)

val Gfun11 = TypeBase.one_one_of "ty";

(* --------------------------------------------------------------------- *)
(* Prove that the constructors yield syntactically distinct values. One	 *)
(* typically needs all symmetric forms of the inequalities.		 *)
(* --------------------------------------------------------------------- *)

val ty_distinct =
    let val ths = CONJUNCTS (TypeBase.distinct_of "ty")
        val rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths
    in LIST_CONJ (ths @ rths)
    end;

(* ===================================================================== *)
(* Definition of well-typed terms of combinatory logic.			 *)
(* ===================================================================== *)

val _ = set_fixity "IN" (Infixr 450);

val (TYrules,TYind, TYcases) =
  IndDefLib.Hol_reln
    `(!A B. K IN (A ==> (B ==> A)))

                /\

     (!A B C. S IN ((A ==> (B ==> C)) ==> ((A ==> B) ==> (A ==> C))))

                /\

     (!U V t1 t2.
           U IN (t1 ==> t2) /\ V IN t1 ==>
           U # V IN t2)`;

(* ======================================================================== *)
(* Mimimal intuitionistic logic.  We now reinterpret ==> as implication,     *)
(* types P:('a)ty as terms of the logic (i.e. propositions), and define a   *)
(* provability predicate `THM` on these terms. The definition is done       *)
(* inductively by the proof rules for the logic.			    *)
(* ======================================================================== *)

val (THMrules, THMind, THMcases) =
    IndDefLib.Hol_reln
      `(!A B.  THM (A ==> (B ==> A)))

               /\

       (!A B C. THM ((A ==> (B ==> C)) ==> ((A ==> B) ==> (A ==> C))))

               /\

       (!P Q.   THM (P ==> Q) /\ THM P ==> THM Q)`;


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

open IndDefRules
val ISO_THM1 = prove(
   --`!P:'a ty. THM P ==> ?M:cl. M IN P`--,
   HO_MATCH_MP_TAC THMind THEN bossLib.PROVE_TAC [TYrules]);

(* --------------------------------------------------------------------- *)
(* The proof for the other direction proceeds by induction over the 	 *)
(* typing relation.  Again, simple.					 *)
(* --------------------------------------------------------------------- *)

val ISO_THM2 = prove(
   --`!P:'a ty. !M:cl. M IN P ==> THM P`--,
   RULE_INDUCT_THEN TYind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
   bossLib.PROVE_TAC [THMrules]);

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
