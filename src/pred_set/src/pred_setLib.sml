structure pred_setLib :> pred_setLib =
struct

  type tactic = Abbrev.tactic
  type conv = Abbrev.conv

  local open pred_setTheory in end;

  val SET_SPEC_CONV = PGspec.SET_SPEC_CONV pred_setTheory.GSPECIFICATION
  val SET_INDUCT_TAC = PSet_ind.SET_INDUCT_TAC pred_setTheory.FINITE_INDUCT
  open PFset_conv;
    
end;
