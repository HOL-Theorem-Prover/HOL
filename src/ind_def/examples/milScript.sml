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
app load ["IndDefLib", "Datatype", "ConstrProofs", "clTheory"] ;
*)

structure milScript =
struct

open HolKernel Parse basicHol90Lib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

open ind_defLib Define_type ConstrProofs clTheory;

(*---------------------------------------------------------------------------*
 * Help for writing prettier rule sets.                                      *
 *---------------------------------------------------------------------------*)

val TY_ANTIQ = Term.ty_antiq o Type;
val relation = TY_ANTIQ`:'a -> 'a -> bool`;

infix 5 -------------------------------------------------------------------;
fun (x ------------------------------------------------------------------- y)
    = (x,y);

(* --------------------------------------------------------------------- *)
(* Open a new theory and load the inductive definitions library.	 *)
(* --------------------------------------------------------------------- *)
val _ = new_theory"mil";

(* ===================================================================== *)
(* Combinatory logic types and type judgements.				 *)
(* ===================================================================== *)

val tyax = define_type{name="ty",
                     type_spec = `ty = G  of 'a  |  -> of ty => ty`,
                     fixities = [Prefix, Infix 800]};

val _ = set_MLname "->_DEF" "Arrow_def";

(* ===================================================================== *)
(* Standard syntactic theory, derived by the recursive types package.	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Structural induction theorem for types.				 *)
(* --------------------------------------------------------------------- *)

val ty_induct = save_thm ("ty_induct",prove_induction_thm tyax);

(* --------------------------------------------------------------------- *)
(* Exhaustive case analysis theorem for types.				 *)
(* --------------------------------------------------------------------- *)

val ty_cases = save_thm ("ty_cases", prove_cases_thm ty_induct);

(* --------------------------------------------------------------------- *)
(* Prove that the arrow and ground type constructors are one-to-one.	 *)
(* --------------------------------------------------------------------- *)

val Gfun11 = save_thm("Gfun11", prove_constructors_one_one tyax);

(* --------------------------------------------------------------------- *)
(* Prove that the constructors yield syntactically distinct values. One	 *)
(* typically needs all symmetric forms of the inequalities.		 *)
(* --------------------------------------------------------------------- *)

val ty_distinct =
    let val ths = CONJUNCTS (prove_constructors_distinct tyax)
        val rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths 
    in save_thm("ty_distinct", LIST_CONJ (ths @ rths))
    end;

(* ===================================================================== *)
(* Definition of well-typed terms of combinatory logic.			 *)
(* ===================================================================== *)

infix 5 -------------------------------------------------------------------;
fun (x ------------------------------------------------------------------- y)
    = (x,y);

val {rules=TYrules,induction=TYind} =
let val TY = Term`IN : cl->'a ty->bool`
in
  indDefine "CL_TYPE_DEF"
   [

      ([],                                                            [])
      -------------------------------------------------------------------
                          `^TY k  (A -> (B -> A))`                      ,



      ([],                                                            [])
      -------------------------------------------------------------------
              `^TY s ((A -> (B -> C)) -> ((A -> B) -> (A -> C)))`       ,



      ([     `^TY U (t1 -> t2)`,                 `^TY V t1`         ],[])
      -------------------------------------------------------------------
                               `^TY (U # V) t2`                        

   ]    (Infix 400)  (`^TY c t`, [])
end;

(* ======================================================================== *)
(* Mimimal intuitionistic logic.  We now reinterpret -> as implication,     *)
(* types P:('a)ty as terms of the logic (i.e. propositions), and define a   *)
(* provability predicate `THM` on these terms. The definition is done       *)
(* inductively by the proof rules for the logic.			    *)
(* ======================================================================== *)

val {rules=THMrules, induction=THMind} =
let val THM = Term`THM:'a ty->bool`
in
  indDefine "THM_DEF"
   [

      ([],                                                            [])
      -------------------------------------------------------------------
                          `^THM  (A -> (B -> A))`                       ,


      ([],                                                            [])
      -------------------------------------------------------------------
               `^THM  ((A -> (B -> C)) -> ((A -> B) -> (A -> C)))`      ,



      ([       `^THM  (P -> Q)`,                `^THM P`            ],[])
      -------------------------------------------------------------------
                                  `^THM  Q`                            

  ]  Prefix (`^THM p`, [])
end;




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

val ISO_THM1 = prove(--`!P:('a)ty. THM P ==> ?M:cl. M IN P`--,
   RULE_INDUCT_THEN THMind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
   REPEAT GEN_TAC THENL
   map (EXISTS_TAC o Term) [`k:cl`, `s:cl`, `M # M'`] THEN
   MAP_FIRST RULE_TAC TYrules THEN
(*   EXISTS_TAC (--`P': 'a ty`--) THEN *)
   EXISTS_TAC (--`P: 'a ty`--) THEN
   CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);

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
