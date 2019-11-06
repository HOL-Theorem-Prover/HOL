(* non-interactive mode
*)
structure listContext :> listContext =
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

open bossLib pairTheory pred_setTheory
     res_quanTheory extra_listTheory listTheory
     hurdUtils ho_basicTools ho_proverTools res_quanTools
     subtypeTools numContext;

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

val list_sc =
  map SC_SIMPLIFICATION
  [LIST_UNIV] @
  map SC_JUDGEMENT
  [GTLIST0_SUBTYPE_JUDGEMENT, GTLIST1_SUBTYPE_JUDGEMENT,
   GTLIST1_SUBSET_GTLIST0, LIST_SUBSET] @
  map SC_SUBTYPE
  [NIL_SUBTYPE, CONS_SUBTYPE, MAP_SUBTYPE, HD_SUBTYPE, TL_SUBTYPE,
   LENGTH_SUBTYPE];

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

(* Rules *)

(* Congruences *)

(* Rewrites *)

(* The module *)

val list_pc = precontext_add
  ("list",
   map C_SUBTYPE list_sc @
   map C_THM
   [GTLIST0_SUBTYPE_REWRITE,
    GTLIST1_SUBTYPE_REWRITE,
    NOT_CONS_NIL,
    NOT_NIL_CONS,
    CONS_11,
    MEM_KILL_DUPS,
    HD,
    TL])
  num_pc;

val list_c = precontext_compile list_pc;

(* non-interactive mode
*)
end;



