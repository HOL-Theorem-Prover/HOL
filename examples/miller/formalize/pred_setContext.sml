(* non-interactive mode
*)
structure pred_setContext :> pred_setContext =
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

open pairTheory pred_setTheory extra_pred_setTheory
     res_quanTheory hurdUtils ho_proverTools res_quanTools subtypeTools
     boolContext;

infixr 0 ++ || ORELSEC ## THENC THEN_TCL ORELSE_TCL;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* --------------------------------------------------------------------- *)
(* Subtype checking.                                                     *)
(* --------------------------------------------------------------------- *)

val pred_set_sc =
  map SC_SIMPLIFICATION
  [SET_UNIV] @
  map SC_JUDGEMENT
  [FINITE_SUBTYPE_JUDGEMENT, NONEMPTY_SUBTYPE_JUDGEMENT, SET_SUBSET] @
  map SC_SUBTYPE
  [EMPTY_SUBTYPE, INSERT_SUBTYPE, INTER_SUBTYPE, UNION_SUBTYPE,
   CHOICE_SUBTYPE, REST_SUBTYPE, DELETE_SUBTYPE, IMAGE_SUBTYPE,
   CARD_SUBTYPE];

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

(* Rules *)

(* Rewrites *)

(* The precontext *)

val pred_set_pc = precontext_add
  ("pred_set",
   map C_SUBTYPE pred_set_sc @
   map C_THM
   [INSERT_THM1, FINITE_INSERT,
    FINITE_EMPTY, CARD_EMPTY, CARD_INSERT, FINITE_UNION, ELT_IN_DELETE,
    EMPTY_SUBSET, SUBSET_UNIV, SUBSET_REFL, SUBSET_EMPTY, UNIV_SUBSET,
    INTER_EMPTY, UNION_EMPTY, NOT_INSERT_EMPTY, NOT_EMPTY_INSERT,
    EMPTY_UNION, EMPTY_UNION_ALT, FINITE_DELETE, FINITE_SUBTYPE_REWRITE,
    IMAGE_EMPTY, IMAGE_EQ_EMPTY, NONEMPTY_SUBTYPE_REWRITE,
    LIST_ELTS, FINITE_BIJ, DELETE_THEN_INSERT])
  bool_pc;

(* The context *)

val pred_set_c = precontext_compile pred_set_pc;

(*
try prove
(``!p. ((!x. p x) = T) ==> !y. p y``,
 SIMPLIFY_TAC bool_c []);

reset_traces ();
allow_trace "SIMPLIFY_TYPECHECK: (tm, res)";

try prove (``!x. ~x \/ ~~x``, SIMPLIFY_TAC bool_c []);

try prove (``!a :: p. (\x :: p. T) a``, SIMPLIFY_TAC bool_c []);
*)

(* non-interactive mode
*)
end;
