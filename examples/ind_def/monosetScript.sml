(* =====================================================================*)
(* FILE		: monosetScript.sml                                     *)
(* DESCRIPTION  : Creates a new monoset including the EVERY operator, 	*)
(*                 and uses it to define a relation and its strong	*)
(*                 induction theorem.					*)
(*									*)
(* AUTHOR	: Peter Vincent Homeier					*)
(* DATE		: 2006.09.08						*)
(* =====================================================================*)

(*
  app load ["IndDefLib", "Datatype", "clTheory"] ;
*)

structure monosetScript =
struct

open HolKernel Parse boolLib listLib listTheory IndDefLib IndDefRules
     bossLib

(* --------------------------------------------------------------------- *)
(* Open a new theory.							 *)
(* --------------------------------------------------------------------- *)

val _ = new_theory"monoset";

(* --------------------------------------------------------------------- *)
(* We intend to add a new monotonic operator to the standard monoset	 *)
(* provided as 'InductiveDefinition.bool_monoset'.  A monotonic operator *)
(* is a (possibly curried) operator which yields a boolean result, some  *)
(* of whose operands also yield boolean results, and where the set of    *)
(* operand values for which the operator yields true only increases      *)
(* ("monotonically") when the operands (considered as sets) increase.    *)
(*									 *)
(* The standard monoset supports the following monotonic operators:      *)
(* 	/\   \/   ?   !   ==>   ~   <abstraction, or "lambda">		 *)
(*									 *)
(* The following script illustrates how to add a new monotonic operator, *)
(* in this case the EVERY operator from the list theory, including the   *)
(* ability to handle tupled abstractions as arguments to EVERY, by also  *)
(* adding a monotonicity result for the UNCURRY operator that underlies  *)
(* tupled abstractions.                                                  *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* The following theorem states that EVERY is monotonic.		 *)
(* --------------------------------------------------------------------- *)

val MONO_EVERY = store_thm
  ("MONO_EVERY",
    ``(!x:'a. MEM x l ==> (P x ==> Q x)) ==>
      (EVERY P l ==> EVERY Q l)``,
    Induct_on `l` THEN SRW_TAC [][]);

(* and this is the analogous result for UNCURRY *)
val MONO_UNCURRY = store_thm(
  "MONO_UNCURRY",
  ``(!p:'a q:'b. P p q ==> Q p q) ==> (UNCURRY P x ==> UNCURRY Q x)``,
  Cases_on `x` THEN SRW_TAC [][])

(* --------------------------------------------------------------------- *)
(* We will use this theorem in constructing a tactic to prove that	 *)
(* EVERY expressions are monotonic.					 *)
(* --------------------------------------------------------------------- *)

val MONO_EVERY_TAC = InductiveDefinition.BACKCHAIN_TAC MONO_EVERY
val MONO_UNCURRY_TAC = InductiveDefinition.BACKCHAIN_TAC MONO_UNCURRY

(* --------------------------------------------------------------------- *)
(* To create the new monoset, we add a pair to the front of the		 *)
(* standard list.  The pair contains the name of the constant as a	 *)
(* string, and also the tactic to prove monotonicity.			 *)
(* --------------------------------------------------------------------- *)

val every_monoset = ("EVERY", MONO_EVERY_TAC) ::
                    ("UNCURRY", MONO_UNCURRY_TAC) ::
                    InductiveDefinition.bool_monoset;

(* --------------------------------------------------------------------- *)
(* Now we apply the new monoset to an example definition.		 *)
(* --------------------------------------------------------------------- *)

val _ = print "Testing inductive definitions - extended monoset\n"

val (EC_rules, EC_ind, EC_cases) = prim_Hol_reln every_monoset ``
  (EC r []) /\
  (!a ps. EC r ps ==> EC r ((a,a)::ps)) /\
  (!ps. EVERY (\(a:'a,b). r a b) ps ==> EC r ps)
``;

val strongEC = prim_derive_strong_induction every_monoset (EC_rules, EC_ind);


(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

val _ = export_theory();

end;
