signature Prim_rec =
sig

   include Abbrev

   (*-----------------------------------------------------------------------
       Returns the types defined by an axiom. Does not return type
       operators that are applied to other types that are defined in
       the axiom.  This is a test for detecting nested recursion, where
       the operator must already have an axiom elsewhere.
    ------------------------------------------------------------------------*)

   val doms_of_tyaxiom : thm -> hol_type list

   (*------------------------------------------------------------------------
      Given a type axiom and the type name, returns the constructors
      associated with that type in the axiom.
    -------------------------------------------------------------------------*)

   val type_constructors : thm -> string -> term list
   val type_constructors_with_args : thm -> string -> term list


   val new_recursive_definition : {name:string, rec_axiom:thm, def:term} -> thm

   (*------------------------------------------------------------------------
      Because a type axiom can be for multiple (mutually recursive) types at
      once, this function returns the definitions of the case constants for
      each type introduced by an axiom.
    -------------------------------------------------------------------------*)

   val define_case_constant : thm -> thm list
   val case_constant_name : {type_name:string} -> string
   val case_constant_defn_name : {type_name:string} -> string

   val INDUCT_THEN                 : thm -> (thm -> tactic) -> tactic
   val prove_rec_fn_exists         : thm -> term -> thm
   val prove_induction_thm         : thm -> thm

   (*-------------------------------------------------------------------------
      Similarly, this function returns a list of theorems where each theorem
      in the list is the cases theorem for a type characterised in the axiom.
    -------------------------------------------------------------------------*)

   val prove_cases_thm             : thm -> thm list
   val case_cong_thm               : thm -> thm -> thm
   val prove_constructors_distinct : thm -> thm option list
   val prove_constructors_one_one  : thm -> thm option list
   val prove_case_rand_thm         : {case_def : thm, nchotomy : thm} -> thm
   val prove_case_elim_thm         : {case_def : thm, nchotomy : thm} -> thm
   val prove_case_eq_thm           : {case_def : thm, nchotomy : thm} -> thm

   (* A utility function *)
   val EXISTS_EQUATION             : term -> thm -> thm

end;
