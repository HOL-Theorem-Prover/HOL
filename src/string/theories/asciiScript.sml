(* =====================================================================*)
(* FILE		: mk_ascii.ml						*)
(* DESCRIPTION   : Creates a theory of 8-bit ascii character codes	*)
(* WRITES FILES	: ascii.th						*)
(*									*)
(* AUTHOR	: (c) T. Melham 1988					*)
(* DATE		: 87.07.27						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATED   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)
open HolKernel Parse Define_type Prim_rec ConstrProofs;

val _ = new_theory "ascii";

(* ---------------------------------------------------------------------*)
(* define the type :ascii						*)
(* ---------------------------------------------------------------------*)
val ascii_Axiom = define_type{name="ascii_Axiom",
 type_spec=`ascii = ASCII of bool=>bool=>bool=>bool=>bool=>bool=>bool=>bool`,
 fixities = [Prefix]};

(* ---------------------------------------------------------------------*)
(* prove induction theorem for ascii.					*)
(* ---------------------------------------------------------------------*)
val ascii_Induct = save_thm ("ascii_Induct", prove_induction_thm ascii_Axiom);

(* ---------------------------------------------------------------------*)
(* prove cases theorem for ascii.					*)
(* ---------------------------------------------------------------------*)
val ascii_CASES = save_thm ("ascii_CASES", prove_cases_thm ascii_Induct);

(* ---------------------------------------------------------------------*)
(* prove that the constructor ASCII is one-to-one			*)
(* ---------------------------------------------------------------------*)
val ASCII_11 = save_thm ("ASCII_11", prove_constructors_one_one ascii_Axiom);

val ascii_case_def = 
new_recursive_definition {name="ascii_case_def",
  def = Term`ascii_case f (ASCII v1 v2 v3 v4 v5 v6 v7 v8) 
                             = f v1 v2 v3 v4 v5 v6 v7 v8`,
  rec_axiom = ascii_Axiom, 
  fixity = Prefix};

val _ = export_theory();
