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

open HolKernel Parse boolLib listLib listTheory IndDefLib bossLib

(* --------------------------------------------------------------------- *)
(* Open a new theory.							 *)
(* --------------------------------------------------------------------- *)

val _ = new_theory"monoset";

(* ---------------------------------------------------------------------

    We intend to add a new monotonic operator to the standard monoset
    that is used by the Hol_reln function for defining inductively
    defined relations.  A monotonic operator is a (possibly curried)
    operator which yields a boolean result, some of whose operands
    also yield boolean results, and where the set of operand values
    for which the operator yields true only increases
    ("monotonically") when the operands (considered as sets) increase.

    As theories load new operators can be proven monotone, thereby
    allowing inductive definitions to use those operators in addition
    to standard boolean operators such as /\, \/ and !.  To "use" an
    operator is to have instances of the new inductive constants appear
    as arguments to them.

    The following script illustrates how the existing theory of lists
    provides a monotonicity result for EVERY, and then shows how this is
    done by defining an isomorphic constant called "every", and setting
    it up to also be monotone.

   --------------------------------------------------------------------- *)

(* our example tests whether or not every number occurring in a t-value
   is even *)
val _ = Hol_datatype `t = v of num | app of t list`

val (alleven_rules, alleven_ind, alleven_cases) = Hol_reln `
  (!n. EVEN n ==> alleven (v n)) /\
  (!ts. EVERY alleven ts ==> alleven (app ts))
`;

val strong_alleven_ind = save_thm(
  "strong_alleven_ind",
  derive_strong_induction (alleven_rules, alleven_ind));

(* ----------------------------------------------------------------------
    now we define our own version EVERY, putting the arguments in a
    different order just to be perverse.
   ---------------------------------------------------------------------- *)

val every_def = Define`(every [] P = T) /\
                       (every (h :: t) P = P h /\ every t P)`
(* note how we could have defined this relation inductively too *)

(* now we have to prove that this operator is monotone *)
val mono_every = store_thm(
  "mono_every",
  ``(!x. P x ==> Q x) ==> (every l P ==> every l Q)``,
  Induct_on `l` THEN SRW_TAC [][every_def])

(* and export it, so that Hol_reln knows all about it *)
val _ = export_mono "mono_every"

(* having done that, we can use every just as we did above, but for the
   sake of variety, this time we will use a schematic variable too.
   Now, we will test that every n in a t-value is bigger than the given
   parameter (which is the schematic variable)  *)
val (allbigger_rules, allbigger_ind, allbigger_cases) = Hol_reln`
  (!n. m < n ==> allbigger m (v n)) /\
  (!ts. every ts (allbigger m) ==> allbigger m (app ts))
`;

val strong_allbigger_ind = save_thm(
  "strong_allbigger_ind",
  derive_strong_induction (allbigger_rules, allbigger_ind))

(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

val _ = export_theory();

end;
