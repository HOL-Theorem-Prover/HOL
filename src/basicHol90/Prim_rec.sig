(* ===================================================================== *)
(* FILE          : prim_rec.sig                                          *)
(* DESCRIPTION   : Signature for primitive recursive definitions over    *)
(*                 recursive types. Translated from hol88.               *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge 1987          *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Prim_rec =
sig

   type term = Term.term
   type thm = Thm.thm
   type tactic = Abbrev.tactic

   (* Returns the types defined by an axiom.

      Does not return type operators that are applied to other types
      that are defined in the axiom.  This is a test for detecting
      nested recursion, where the operator must already have an axiom
      elsewhere.  *)
   val new_types : thm -> Type.hol_type list

   (* given a type axiom and the type name, returns the constructors
      associated with that type in the axiom *)
   val type_constructors : thm -> string -> term list


   val new_recursive_definition : {name:string, rec_axiom:thm, def:term} -> thm

   (* because a type axiom can be for multiple (mutually recursive) types at
      once, this function returns the definitions of the case constants for
      each type in a list *)
   val define_case_constant : thm -> thm list


   val INDUCT_THEN                 : thm -> (thm -> tactic) -> tactic
   val prove_rec_fn_exists         : thm -> term -> thm
   val prove_induction_thm         : thm -> thm

   (* similarly, this function returns a list of theorems where each theorem
      in the list is the cases theorem for a type characterised in the axiom
   *)
   val prove_cases_thm             : thm -> thm list
   val case_cong_thm               : thm -> thm -> thm
   val prove_constructors_distinct : thm -> thm option list
   val prove_constructors_one_one  : thm -> thm option list

end;
