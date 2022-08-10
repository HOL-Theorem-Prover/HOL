(* non-interactive mode
*)
structure finite_groupContext :> finite_groupContext =
struct
open HolKernel Parse boolLib;

(* interactive mode
if !show_assums then () else
 (loadPath := ".."::"../../prob"::(!loadPath);
  load "bossLib";
  load "pred_setTheory";
  load "millerTools";
  load "miller_extraTheory";
  show_assums := true);
*)

open subtypeTools hurdUtils groupContext finite_groupTheory;

infixr 0 ++ || ORELSEC ## THENC THEN_TCL ORELSE_TCL;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op!! = op REPEAT;
val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* --------------------------------------------------------------------- *)
(* Subtype checking.                                                     *)
(* --------------------------------------------------------------------- *)

val finite_group2_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [] @
  map SC_SUBTYPE
  [FINITE_GSET_SUBTYPE,
   GORD_SUBTYPE,
   ELT_SUBGROUP_SUBTYPE,
   ADD_GROUP_SUBTYPE];

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

val finite_group1_pc = precontext_add
  ("finite_group1",
   map C_FORWARDS
   [FINITE_GROUP_FINITE,
    FINITE_GROUP_GROUP])
  group_pc;

val finite_group2_pc = precontext_add
  ("finite_group2",
   map C_SUBTYPE finite_group2_sc @
   map C_THM
   [ADD_GROUP_SET_ZERO,
    ADD_GROUP_SET_FINITE,
    ADD_GROUP_SET_CARD,
    GPOW_GORD,
    GPOW_MOD_GORD,
    LCOSET_REFL,
    CARD_GROUP,
    CARD_LCOSET,
    POWER_ORDER,
    MOD_SUC_MOD,
    MOD_MULT_MOD,
    MOD_ADD_CANCEL] @
   map C_FORWARDS
   [SUBGROUP_FINITE_GROUP])
  finite_group1_pc;

val finite_group3_pc = precontext_add
  ("finite_group3",
   map C_THM
   [GORD_GID,
    GORD_GINV])
  finite_group2_pc;

val finite_group_pc = finite_group3_pc;
val finite_group_c = precontext_compile finite_group_pc;

(* non-interactive mode
*)
end;
