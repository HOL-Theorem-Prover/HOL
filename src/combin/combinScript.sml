(* ===================================================================== *)
(* FILE          : mk_combin.sml                                         *)
(* DESCRIPTION   : Basic combinator definitions and some theorems about  *)
(*                 them. Translated from hol88.                          *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.02.26                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)

structure combinScript =
struct

(* Parent theory *)
local open boolTheory in end;

open HolKernel Parse basicHol90Lib;

type thm = Thm.thm;
infix THEN;

val _ = new_theory "combin";

(* Some basic combinators: function composition, S, K, and I.          *)

val o_DEF = new_infixr_definition("o_DEF", --`$o f g = \x. f(g x)`--,  800);

val K_DEF = new_definition("K_DEF",       --`K = \x y. x`--);

val S_DEF = new_definition("S_DEF",       --`S = \f g x. f x (g x)`--);

(*---------------------------------------------------------------------------
 * The type constraint is necessary in order to meet one of the criteria
 * for a definition : the tyvars of the lhs must be a superset of those
 * on the rhs.
 *---------------------------------------------------------------------------*)
val I_DEF = new_definition("I_DEF",       --`I = S K (K:'a->'a->'a)`--);


(* Theorem about application of composed functions.      *)
val o_THM = store_thm("o_THM",
   --`! f g x. (f o g) x = f(g x)`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ o_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

(* This theorem states that function composition is associative.  *)
val o_ASSOC = store_thm("o_ASSOC",
   --`!f g h. f o (g o h) = (f o g) o h`--,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [ o_DEF ]
   THEN CONV_TAC (REDEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

(* Theorem about application of K.          *)
val K_THM = store_thm("K_THM",
    --`!x y. K x y = x`--,
    REPEAT GEN_TAC
    THEN PURE_REWRITE_TAC [ K_DEF ]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN REFL_TAC);

(* Theorem about application of S.          *)
val S_THM = store_thm("S_THM",
   --`!f g x. S f g x = f x (g x)`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ S_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

(* Theorem about application of I.          *)
val I_THM = store_thm("I_THM",
   --`!x. I x = x`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ I_DEF, S_THM, K_THM ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

(* I is the identity for function composition.        *)
val I_o_ID = store_thm("I_o_ID",
   --`!f. (I o f = f) /\ (f o I = f)`--,
   REPEAT STRIP_TAC
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   THEN REWRITE_TAC [ o_DEF ]
   THEN CONV_TAC (REDEPTH_CONV BETA_CONV)
   THEN REWRITE_TAC [ I_THM ]);

val _ = export_theory();

end;
