(* ===================================================================== *)
(* FILE          : combinScript.sml                                      *)
(* DESCRIPTION   : Basic combinator definitions and some theorems about  *)
(*                 them. Translated from hol88.                          *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.02.26                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* AUGMENTED     : (kxs) added C and W combinators                       *)
(* ===================================================================== *)

structure combinScript =
struct

open HolKernel Parse boolLib;

val _ = new_theory "combin";

(*---------------------------------------------------------------------------*)
(*  Some basic combinators: function composition, S, K, I, W, and C.         *)
(*---------------------------------------------------------------------------*)

val K_DEF = Q.new_definition("K_DEF",        `K = \x y. x`);
val S_DEF = Q.new_definition("S_DEF",        `S = \f g x. f x (g x)`);
val I_DEF = Q.new_definition("I_DEF",        `I = S K (K:'a->'a->'a)`);
val C_DEF = Q.new_definition("C_DEF",        `C = \f x y. f y x`);
val W_DEF = Q.new_definition("W_DEF",        `W = \f x. f x x`);
val o_DEF = Q.new_infixr_definition("o_DEF", `$o f g = \x. f(g x)`, 800);

(*---------------------------------------------------------------------------*
 * In I_DEF, the type constraint is necessary in order to meet one of        *
 * the criteria for a definition : the tyvars of the lhs must be a           *
 * superset of those on the rhs.                                             *
 *---------------------------------------------------------------------------*)


val o_THM = store_thm("o_THM",
   --`!f g x. (f o g) x = f(g x)`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ o_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val o_ASSOC = store_thm("o_ASSOC",
   --`!f g h. f o (g o h) = (f o g) o h`--,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [ o_DEF ]
   THEN CONV_TAC (REDEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val o_ABS_R = store_thm(
  "o_ABS_R",
  ``f o (\x. g x) = (\x. f (g x))``,
  REWRITE_TAC [FUN_EQ_THM, o_THM] THEN BETA_TAC THEN REWRITE_TAC []);

val K_THM = store_thm("K_THM",
    --`!x y. K x y = x`--,
    REPEAT GEN_TAC
    THEN PURE_REWRITE_TAC [ K_DEF ]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN REFL_TAC);

val S_THM = store_thm("S_THM",
   --`!f g x. S f g x = f x (g x)`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ S_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val S_ABS_L = store_thm(
  "S_ABS_L",
  ``S (\x. f x) g = \x. (f x) (g x)``,
  REWRITE_TAC [FUN_EQ_THM, S_THM] THEN BETA_TAC THEN REWRITE_TAC []);

val S_ABS_R = store_thm(
  "S_ABS_R",
  ``S f (\x. g x) = \x. (f x) (g x)``,
  REWRITE_TAC [FUN_EQ_THM, S_THM] THEN BETA_TAC THEN REWRITE_TAC[]);

val C_THM = store_thm("C_THM",
   --`!f x y. C f x y = f y x`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ C_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val C_ABS_L = store_thm(
  "C_ABS_L",
  ``C (\x. f x) y = (\x. f x y)``,
  REWRITE_TAC [FUN_EQ_THM, C_THM] THEN BETA_TAC THEN REWRITE_TAC []);

val W_THM = store_thm("W_THM",
   --`!f x. W f x = f x x`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ W_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val I_THM = store_thm("I_THM",
   --`!x. I x = x`--,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ I_DEF, S_THM, K_THM ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val I_o_ID = store_thm("I_o_ID",
   --`!f. (I o f = f) /\ (f o I = f)`--,
   REWRITE_TAC [I_THM, o_THM, FUN_EQ_THM]);

val K_o_THM = store_thm("K_o_THM",
  --`(!f v. K v o f = K v) /\ (!f v. f o K v = K (f v))`--,
  REWRITE_TAC [o_THM, K_THM, FUN_EQ_THM]);

(*---------------------------------------------------------------------------*)
(* Theorems using combinators to specify let-movements                       *)
(*---------------------------------------------------------------------------*)

val GEN_LET_RAND = store_thm(
  "GEN_LET_RAND",
  ``P (LET f v) = LET (P o f) v``,
  REWRITE_TAC [LET_THM, o_THM]);

val GEN_LET_RATOR = store_thm(
  "GEN_LET_RATOR",
  ``(LET f v) x = LET (C f x) v``,
  REWRITE_TAC [LET_THM, C_THM]);

val LET_FORALL_ELIM = store_thm(
  "LET_FORALL_ELIM",
  ``LET f v = (!) (S ((==>) o Abbrev o (C (=) v)) f)``,
  REWRITE_TAC [S_DEF, LET_THM, C_DEF] THEN BETA_TAC THEN
  REWRITE_TAC [o_THM, markerTheory.Abbrev_def] THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    ASM_REWRITE_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC
  ]);

val GEN_literal_case_RAND = store_thm(
  "GEN_literal_case_RAND",
  ``P (literal_case f v) = literal_case (P o f) v``,
  REWRITE_TAC [literal_case_THM, o_THM]);

val GEN_literal_case_RATOR = store_thm(
  "GEN_literal_case_RATOR",
  ``(literal_case f v) x = literal_case (C f x) v``,
  REWRITE_TAC [literal_case_THM, C_THM]);

val literal_case_FORALL_ELIM = store_thm(
  "literal_case_FORALL_ELIM",
  ``literal_case f v = (!) (S ((==>) o Abbrev o (C (=) v)) f)``,
  REWRITE_TAC [S_DEF, literal_case_THM, C_DEF] THEN BETA_TAC THEN
  REWRITE_TAC [o_THM, markerTheory.Abbrev_def] THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    ASM_REWRITE_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC
  ]);


(*---------------------------------------------------------------------------*)
(*  Tag combinator equal to K. Used in generating ML from HOL                *)
(*---------------------------------------------------------------------------*)

val FAIL_DEF = Q.new_definition("FAIL_DEF", `FAIL = \x y. x`);
val FAIL_THM = Q.store_thm("FAIL_THM", `FAIL x y = x`,
    REPEAT GEN_TAC
    THEN PURE_REWRITE_TAC [ FAIL_DEF ]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN REFL_TAC);

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in
    S "val _ = Parse.hide \"C\";"; NL();
    S "val _ ="; NL();
    S "   let open computeLib" ; NL();
    S "       val K_tm = Term.prim_mk_const{Name=\"K\",Thy=\"combin\"}"; NL();
    S "   in add_funs [K_THM,S_DEF,I_THM,C_DEF,W_DEF,o_DEF];"; NL();
    S "      set_skip the_compset K_tm (SOME 1)"; NL();
    S "   end;";
    NL()
  end)};


val _ =
 let open EmitML
 in
   emitML (!Globals.emitMLDir)
     ("combin",
       map DEFN [S_THM, K_THM, I_THM, W_THM, C_THM, o_THM, FAIL_THM])
 end;

val _ = export_theory();

end;
