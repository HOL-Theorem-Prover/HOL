structure pred_setLib :> pred_setLib =
struct

  local open pred_setTheory in end

  open Abbrev PFset_conv (* pred_setSyntax should be opened too *);

  val SET_SPEC_CONV  = PGspec.SET_SPEC_CONV pred_setTheory.GSPECIFICATION

  val SET_INDUCT_TAC = PSet_ind.SET_INDUCT_TAC pred_setTheory.FINITE_INDUCT

  val PRED_SET_ss    = pred_setSimps.PRED_SET_ss

end
