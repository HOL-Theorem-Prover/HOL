(* non-interactive mode
*)
structure mult_groupContext :> mult_groupContext =
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

open subtypeTools hurdUtils finite_groupContext mult_groupTheory;

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

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

val mult_group_pc = precontext_add
  ("mult_group",
   map (C_SUBTYPE o SC_SUBTYPE)
   [MULT_GROUP_SUBTYPE] @
   map (C_SUBTYPE o SC_JUDGEMENT)
   [MULT_SUBSET_ADD] @
   map C_THM
   [MULT_GROUP_SET_FINITE,
    FERMAT_LITTLE] @
   map C_FORWARDS
   [])
  finite_group_pc;

val mult_group_c = precontext_compile mult_group_pc;

(* non-interactive mode
*)
end;
