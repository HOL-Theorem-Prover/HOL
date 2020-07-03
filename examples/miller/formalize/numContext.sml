(* non-interactive mode
*)
structure numContext :> numContext =
struct
open HolKernel Parse boolLib;

structure Parse = struct
  open Parse
  val (Type,Term) =
      pred_setTheory.pred_set_grammars
        |> apsnd ParseExtras.grammar_loose_equality
        |> parse_from_grammars
end
open Parse
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
     res_quanTheory arithmeticTheory extra_numTheory
     hurdUtils ho_basicTools ho_proverTools res_quanTools
     subtypeTools boolContext prim_recTheory;

infixr 0 ++ || ORELSEC ## THENC THEN_TCL ORELSE_TCL |->;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op!! = op REPEAT;
val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Debugging.                                                                *)
(* ------------------------------------------------------------------------- *)

val trace_level = ref 0;
val _ = Feedback.register_trace ("numContext", trace_level, 10);
fun trace l s = if l > !trace_level then () else say (s ^ "\n");
fun trace_x l s f x =
  if l > !trace_level then () else say (s ^ ":\n" ^ f x ^ "\n");
fun trace_CONV l s tm = (trace_x l s term_to_string tm; ALL_CONV tm);

(* --------------------------------------------------------------------- *)
(* Subtype checking.                                                     *)
(* --------------------------------------------------------------------- *)

val num_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [GTNUM0_SUBTYPE_JUDGEMENT, GTNUM1_SUBTYPE_JUDGEMENT, GTNUM1_SUBSET_GTNUM0] @
  map SC_SUBTYPE
  [SUC_SUBTYPE, ADD_SUBTYPE, MULT_SUBTYPE, MIN_SUBTYPE, EXP_SUBTYPE,
   FUNPOW_SUBTYPE, NUMERAL_BIT1_SUBTYPE, NUMERAL_BIT2_SUBTYPE, NUMERAL_SUBTYPE];

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

(* Rules *)

(* Congruences *)

(* Rewrites *)

val subtype_thms = [GTNUM0_SUBTYPE_REWRITE, GTNUM1_SUBTYPE_REWRITE];

val suc_thms =
  [prim_recTheory.INV_SUC_EQ,
   numTheory.NOT_SUC,
   arithmeticTheory.SUC_NOT,
   SUC_0];

val addition_thms =
  map (fn g => prove (g, DECIDE_TAC))
  [``!n : num. 0 + n = n``,
   ``!n : num. n + 0 = n``,
   ``!m n : num. (m + n = 0) = (m = 0) /\ (n = 0)``,
   ``!m n : num. (m + n = 1) = ((m = 1) /\ (n = 0)) \/ ((m = 0) /\ (n = 1))``,
   ``!n a b : num. (n + a = n + b) = (a = b)``,
   ``!n a b : num. (a + n = b + n) = (a = b)``,
   ``!n a b : num. (n + a = b + n) = (a = b)``,
   ``!n a b : num. (a + n = n + b) = (a = b)``,
   ``!n a b : num. (n + a <= n + b) = (a <= b)``,
   ``!n a b : num. (a + n <= b + n) = (a <= b)``,
   ``!n a b : num. (n + a <= b + n) = (a <= b)``,
   ``!n a b : num. (a + n <= n + b) = (a <= b)``,
   ``!n a b : num. (n + a < n + b) = (a < b)``,
   ``!n a b : num. (a + n < b + n) = (a < b)``,
   ``!n a b : num. (n + a < b + n) = (a < b)``,
   ``!n a b : num. (a + n < n + b) = (a < b)``];

val subtraction_thms =
  map
  (prove o
   add_snd (RW_TAC arith_ss [SUB_MONO_EQ, SUB_EQUAL_0]))
  [``!n : num. n - 0 = n``,
   ``!n : num. n - n = 0``,
   ``!n : num. 0 - n = 0``,
   ``!m n : num. (m - n = 0) = m <= n``,
   ``!m n : num. SUC m - SUC n = m - n``,
   ``!m n : num. n <= m ==> (n + (m - n) = m)``,
   ``!m n : num. n <= m ==> ((m - n) + n = m)``];

val order_thms =
  map (prove o add_snd DECIDE_TAC)
  [``0 : num < 1``,
   ``!n : num. 0 < SUC n``,
   ``!n : num. ~(n < 0)``,
   ``!n : num. ~(n < n)``,
   ``!n : num. n < SUC n``,
   ``!n : num. ~(SUC n < n)``,
   ``!m n : num. SUC m < SUC n = m < n``,
   ``0 : num <= 1``,
   ``!n : num. 0 <= n``,
   ``!n : num. (n <= 0) = (n = 0)``,
   ``!n : num. n <= n``,
   ``!n : num. n <= SUC n``,
   ``!n : num. ~(SUC n <= n)``,
   ``!m n : num. SUC m <= SUC n = m <= n``,
   ``!m n : num. m < n ==> m <= n``];

val multiplication_thms =
  map (fn g => prove
       (g, Cases ++ RW_TAC arith_ss [] ++
        PROVE_TAC [MULT_CLAUSES, MULT_MONO_EQ, MULT_COMM,
                   MULT_LESS_EQ_SUC, LESS_MULT_MONO, MULT_EQ_0,
                   MULT_EQ_1, LESS_0_MULT2]))
  [``!n : num. 1 * n = n``,
   ``!n : num. n * 1 = n``,
   ``!n : num. 0 * n = 0``,
   ``!n : num. n * 0 = 0``,
   ``!m n : num. (m * n = 0) = (m = 0) \/ (n = 0)``,
   ``!m n : num. (m * n = 1) = (m = 1) /\ (n = 1)``,
   ``!m n : num. 0 < m * n = 0 < m /\ 0 < n``,
   ``!n a b : num. 0 < n ==> ((n * a = n * b) = (a = b))``,
   ``!n a b : num. 0 < n ==> ((a * n = b * n) = (a = b))``,
   ``!n a b : num. 0 < n ==> ((n * a = b * n) = (a = b))``,
   ``!n a b : num. 0 < n ==> ((a * n = n * b) = (a = b))``,
   ``!n a b : num. 0 < n ==> ((n * a <= n * b) = (a <= b))``,
   ``!n a b : num. 0 < n ==> ((a * n <= b * n) = (a <= b))``,
   ``!n a b : num. 0 < n ==> ((n * a <= b * n) = (a <= b))``,
   ``!n a b : num. 0 < n ==> ((a * n <= n * b) = (a <= b))``,
   ``!n a b : num. 0 < n ==> ((n * a < n * b) = (a < b))``,
   ``!n a b : num. 0 < n ==> ((a * n < b * n) = (a < b))``,
   ``!n a b : num. 0 < n ==> ((n * a < b * n) = (a < b))``,
   ``!n a b : num. 0 < n ==> ((a * n < n * b) = (a < b))``];

val min_thms =
  [MIN_0L, MIN_0R, MIN_REFL, LEQ_MINL, LEQ_MINR, LESS_MINL, LESS_MINR];

val exp_thms =
  map (fn g => prove
       (g, Cases ++ RW_TAC arith_ss [EXP, EXP_1]))
  [``!n : num. n EXP 0 = 1``,
   ``!n : num. n EXP 1 = n``,
   ``!n : num. 0 < n ==> (0 EXP n = 0)``,
   ``!n : num. 1 EXP n = 1``];

val div_mod_thms =
  [DIV_1, MOD_1, LESS_DIV_EQ_ZERO, ZERO_DIV, X_MOD_X, MOD_MOD,
   MOD_LESS, LESS_MOD_EQ, DIV_EQ_0, MOD_EQ_X, MOD_EXP, MULT_DIV];

local
  val GSYM_MOD_PLUS1 = GSYM MOD_PLUS1;
  val GSYM_MOD_PLUS2 = GSYM MOD_PLUS2;
  val x = ``x:num``;
  val target = ``0 < (x:num)``;
in
  val mod_plus_rewr = pattern_rewr
    (``(a + b) MOD n``,
     fn simplifier => fn prover =>
     CHANGED_CONV
     (trace_CONV 2 "mod_plus_rewr input"
      THENC RAND_CONV simplifier THENC
      (fn tm =>
       let
         val qprover =
           let
             val modulus = rand tm
             val goal = subst [(x |-> modulus)] target
             val th = prover goal
           in
             fn g =>
             if g ~~ goal then th
             else raise ERR "mod_plus_rewr" "modulus changed"
           end
       in
         (ho_COND_REWR_CONV GSYM_MOD_PLUS1 qprover
          THENC ho_COND_REWR_CONV GSYM_MOD_PLUS2 qprover
          THENC trace_CONV 4 "mod_plus_rewr after preparation"
          THENC
          (RATOR_CONV o RAND_CONV)
          ((RATOR_CONV o RAND_CONV) simplifier THENC RAND_CONV simplifier)
          THENC TRYC (ho_COND_REWR_CONV MOD_PLUS1 qprover)
          THENC TRYC (ho_COND_REWR_CONV MOD_PLUS2 qprover)) tm
       end)
      THENC trace_CONV 2 "mod_plus_rewr result"))
end;

local
  val GSYM_MOD_MULT1 = GSYM MOD_MULT1;
  val GSYM_MOD_MULT2 = GSYM MOD_MULT2;
  val x = ``x:num``;
  val target = ``0 < (x:num)``;
in
  val mod_mult_rewr = pattern_rewr
    (``(a * b) MOD n``,
     fn simplifier => fn prover =>
     CHANGED_CONV
     (trace_CONV 2 "mod_mult_rewr input"
      THENC RAND_CONV simplifier THENC
      (fn tm =>
       let
         val qprover =
           let
             val modulus = rand tm
             val goal = subst [(x |-> modulus)] target
             val th = prover goal
           in
             fn g =>
             if g ~~ goal then th
             else raise ERR "mod_mult_rewr" "modulus changed"
           end
       in
         (ho_COND_REWR_CONV GSYM_MOD_MULT1 qprover
          THENC ho_COND_REWR_CONV GSYM_MOD_MULT2 qprover
          THENC trace_CONV 4 "mod_mult_rewr after preparation"
          THENC
          (RATOR_CONV o RAND_CONV)
          ((RATOR_CONV o RAND_CONV) simplifier THENC RAND_CONV simplifier)
          THENC TRYC (ho_COND_REWR_CONV MOD_MULT1 qprover)
          THENC TRYC (ho_COND_REWR_CONV MOD_MULT2 qprover)) tm
       end)
      THENC trace_CONV 2 "mod_mult_rewr result"))
end;

(* old---hopefully obsolete
local
  val GSYM_MOD_MULT1 = GSYM MOD_MULT1
  val GSYM_MOD_MULT2 = GSYM MOD_MULT2
in
  val mod_mult_rewr = pattern_rewr
    (``(a * b) MOD n``,
     fn simplifier => fn prover =>
     CHANGED_CONV
     (trace_CONV 2 "mod_mult_rewr input"
      THENC RAND_CONV simplifier
      THENC ho_COND_REWR_CONV GSYM_MOD_MULT1 prover
      THENC ho_COND_REWR_CONV GSYM_MOD_MULT2 prover
      THENC trace_CONV 4 "mod_mult_rewr after preparation"
      THENC
      (RATOR_CONV o RAND_CONV)
      ((RATOR_CONV o RAND_CONV) simplifier THENC RAND_CONV simplifier)
      THENC TRYC (ho_COND_REWR_CONV MOD_MULT1 prover)
      THENC TRYC (ho_COND_REWR_CONV MOD_MULT2 prover)
      THENC trace_CONV 2 "mod_mult_rewr result"))
end;
*)

(* The module *)

val num_pc = precontext_add
  ("num",
   map C_REWR [mod_plus_rewr, mod_mult_rewr] @
   map C_THM
   (suc_thms @
    addition_thms @
    subtraction_thms @
    order_thms @
    multiplication_thms @
    min_thms @
    exp_thms @
    div_mod_thms @
    subtype_thms) @
   map C_SUBTYPE num_sc)
  bool_pc;

val num_c = precontext_compile num_pc;

(*
allow_trace "GEN_SIMPLIFY_CONV";
allow_trace "SIMPLIFY_REWR_CONV";
reset_traces ();
allow_trace "SIMPLIFY_CONV";
allow_trace "mod_plus_rewr";

SIMPLIFY_CONV num_c ``(a + b) MOD n``;
SIMPLIFY_CONV num_c ``0 < n ==> P ((a + b MOD n + c) MOD n)``;
*)

(* non-interactive mode
*)
end;
