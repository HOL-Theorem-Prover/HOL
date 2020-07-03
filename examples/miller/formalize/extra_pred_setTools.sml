(* ------------------------------------------------------------------------- *)
(* Some miscellaneous tools that come in useful in the probability           *)
(* development.                                                              *)
(* ------------------------------------------------------------------------- *)

structure extra_pred_setTools :> extra_pred_setTools =
struct

open HolKernel Parse boolLib;
open bossLib pred_setTheory hurdUtils subtypeTheory extra_pred_setTheory;

infixr 0 ++ || ORELSEC ## THENC -->;
infix 1 >> |->;
nonfix THEN ORELSE;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Set simplification.                                                       *)
(* ------------------------------------------------------------------------- *)

val set_rewrs
  = [INTER_EMPTY, INTER_UNIV, UNION_EMPTY, UNION_UNIV, DISJOINT_UNION,
     DISJOINT_INSERT, DISJOINT_EMPTY, GSYM DISJOINT_EMPTY_REFL,
     DISJOINT_BIGUNION, INTER_SUBSET, INTER_IDEMPOT, UNION_IDEMPOT,
     SUBSET_UNION];

val elt_rewrs
  = [SUBSET_DEF, IN_COMPL, IN_DIFF, IN_UNIV, NOT_IN_EMPTY, IN_UNION,
     IN_INTER, IN_IMAGE, IN_FUNSET, IN_DFUNSET, GSPECIFICATION,
     DISJOINT_DEF, IN_BIGUNION, IN_BIGINTER, IN_COUNT, IN_o,
     IN_UNIONL, IN_DELETE, IN_PREIMAGE, IN_SING, IN_INSERT];

fun rewr_ss ths =
  simpLib.++
  (std_ss,
   simpLib.SSFRAG
   {ac = [],
    name = NONE,
    convs = [],
    dprocs = [],
    filter = NONE,
    rewrs = map (fn th => (NONE, th)) (set_rewrs @ elt_rewrs),
    congs = []});

val pset_set_ss = rewr_ss set_rewrs;
val pset_elt_ss = rewr_ss elt_rewrs;
val pset_ss = rewr_ss (set_rewrs @ elt_rewrs);

fun PSET_TAC ths =
  REPEAT (POP_ASSUM MP_TAC)
  ++ RW_TAC pset_set_ss ths
  ++ REPEAT (POP_ASSUM MP_TAC)
  ++ RW_TAC pset_elt_ss ths;

end;
