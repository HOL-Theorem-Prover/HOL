structure setLib :> setLib =
struct

 type tactic = Abbrev.tactic
 type conv = Abbrev.conv

  val SET_SPEC_CONV = Gspec.SET_SPEC_CONV setTheory.GSPECIFICATION
  val SET_INDUCT_TAC = Set_ind.SET_INDUCT_TAC setTheory.FINITE_INDUCT;

  open Fset_conv
    
end;
