(* non-interactive mode
*)
structure groupContext :> groupContext =
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

open subtypeTools pred_setContext groupTheory hurdUtils arithContext
     listContext;

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

val group1_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [] @
  map SC_SUBTYPE
  [GSET_SUBTYPE,
   GOP_SUBTYPE,
   GID_SUBTYPE,
   GINV_SUBTYPE];

val group3_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [] @
  map SC_SUBTYPE
  [GPOW_SUBTYPE];

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

val std_pc = precontext_mergel [arith_pc, list_pc, pred_set_pc];

val group1_pc = precontext_add
  ("group1",
   map C_SUBTYPE group1_sc @
   map C_THM
   [GROUP_LCANCEL,
    GROUP_RCANCEL,
    GROUP_LCANCEL_ID,
    GROUP_RCANCEL_ID,
    GROUP_LID,
    GROUP_RID,
    GROUP_LINV,
    GROUP_RINV,
    PROD_GROUP_SET,
    PROD_GROUP_OP])
  std_pc;

val group2_pc = precontext_add
  ("group2",
   map C_FORWARDS
   [SUBGROUP_SET,
    SUBGROUP_GROUP,
    SUBGROUP_OP,
    SUBGROUP_ID,
    SUBGROUP_INV,
    PSUBGROUP_SUBGROUP,
    PSUBGROUP_PSUBSET])
  group1_pc;

val group3_pc = precontext_add
  ("group3",
   map C_SUBTYPE group3_sc @
   map C_THM
   [GPOW,
    GPOW_ID,
    GPOW_ADD,
    GPOW_MULT])
  group2_pc;

val group_pc = precontext_add
  ("group",
   map (C_SUBTYPE o SC_SUBTYPE)
   [GPOW_SUBTYPE] @
   map C_THM
   [GINV_GID,
    GPOW_1,
    GINV_EQ_GID])
  group3_pc;

val group_c = precontext_compile group_pc;

(* non-interactive mode
*)
end;
