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
   type fixity = Term.fixity
   type thm = Thm.thm
   type tactic = Abbrev.tactic

   val new_recursive_definition 
     : {name:string, fixity:fixity, rec_axiom:thm, def:term} -> thm

   val INDUCT_THEN         : thm -> (thm -> tactic) -> tactic
   val prove_rec_fn_exists : thm -> term -> thm
   val prove_induction_thm : thm -> thm
   val prove_cases_thm     : thm -> thm
   val case_cong_thm       : thm -> thm -> thm

end;
