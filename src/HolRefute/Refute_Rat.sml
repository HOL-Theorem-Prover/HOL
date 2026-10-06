(* Optional rational Quickcheck and model-finder support. *)
structure Refute_Rat :> Refute_Rat = struct
  local open Refute refuteRatTheory in end
  structure MFH = Refute_ModelFinder_HOL
  val dest_frac_atom = Refute_ModelFinder_Model.dest_frac_atom

  fun frac_atom_to_rat term =
    case dest_frac_atom term of
        NONE => term
      | SOME (numerator, denominator) =>
          (let
             val rat_cons = Term.prim_mk_const {Thy = "rat", Name = "rat_cons"}
             val denominator =
               if Arbint.compare
                    (intSyntax.int_of_term numerator, Arbint.zero) = EQUAL
               then intSyntax.term_of_int Arbint.one
               else denominator
           in
             Term.list_mk_comb (rat_cons, [numerator, denominator])
           end handle Feedback.HOL_ERR _ => term)

  fun register () =
    (Refute_ModelFinder_Model.register_frac_type_with_display
       (MFH.rat_frac_registration, ratSyntax.rat_ty, frac_atom_to_rat);
     Refute_EvalRat.register ())

  val () = register ()
end
