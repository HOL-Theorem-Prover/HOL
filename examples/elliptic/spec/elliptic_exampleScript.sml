(* ========================================================================= *)
(* Create "elliptic_exampleTheory" compiling elliptic curve operations.      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
val () = loadPath := [] @ !loadPath;
val () = app load ["bossLib", "metisLib", "wordsLib", "ellipticTheory"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib
     arithmeticTheory wordsTheory ellipticTheory;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "elliptic".                                     *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "elliptic_example";

(* ------------------------------------------------------------------------- *)
(* Sort out the parser.                                                      *)
(* ------------------------------------------------------------------------- *)

val () = Parse.add_infix ("/", 600, HOLgrammars.LEFT);

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;

(* ------------------------------------------------------------------------- *)
(* Extensions to HOL theories to define the ex_ constants.                   *)
(* ------------------------------------------------------------------------- *)

val word_mod_def = Define
  `word_mod a b = a - (b * word_div a b)`;

val SUM_FUN_RANGE = prove (
``!n f. SUM n f = SUM n (\m. if (m < n) then f m else 0)``,

REWRITE_TAC [sum_numTheory.SUM] THEN
REPEAT GEN_TAC THEN
MATCH_MP_TAC sum_numTheory.GSUM_FUN_EQUAL THEN
SIMP_TAC std_ss []);


val w2n_lsr = store_thm ("w2n_lsr",
``(w2n (w >>> m)) = (w2n w DIV 2**m)``,

Induct_on `m` THENL [
       SIMP_TAC std_ss [SHIFT_ZERO, EXP],

       SIMP_TAC std_ss [EXP] THEN
       ONCE_REWRITE_TAC[MULT_SYM] THEN
       SIMP_TAC std_ss [GSYM DIV_DIV_DIV_MULT] THEN
       POP_ASSUM (fn thm => REWRITE_TAC [GSYM thm]) THEN
       `(w >>> SUC m) = ((w >>> m) >>> (SUC 0))` by ALL_TAC THEN1 (
               REWRITE_TAC [LSR_ADD, ADD_CLAUSES]
       ) THEN
       POP_ASSUM (fn thm => REWRITE_TAC [thm]) THEN
       Q.ABBREV_TAC `v = w >>> m` THEN
       POP_ASSUM (fn thm => ALL_TAC) THEN

       FULL_SIMP_TAC std_ss [word_lsr_def, w2n_def] THEN
       `0 < dimindex (:'a)` by REWRITE_TAC [DIMINDEX_GT_0] THEN
       Q.ABBREV_TAC `a = dimindex (:'a)` THEN
       `a <= dimindex (:'a)` by ASM_SIMP_TAC arith_ss [] THEN
       Q.PAT_ASSUM `Abbrev x` (fn thm => ALL_TAC) THEN
       Induct_on `a` THENL [
               SIMP_TAC std_ss [],

               Cases_on `a` THENL [
                       FULL_SIMP_TAC arith_ss [sum_numTheory.SUM_def, fcpTheory.FCP_BETA,
DIMINDEX_GT_0, bitTheory.SBIT_def, COND_RAND, COND_RATOR],

                       REPEAT STRIP_TAC THEN
                       FULL_SIMP_TAC arith_ss [] THEN
                       ONCE_REWRITE_TAC [sum_numTheory.SUM_def] THEN
                       SIMP_TAC std_ss [] THEN
                       `!x. ((x + SBIT (v %% SUC n) (SUC n)) DIV 2) =
                                 (x DIV 2 + SBIT (v %% SUC n) n)` by ALL_TAC THEN1 (
                               ONCE_REWRITE_TAC [ADD_COMM] THEN
                               Tactical.REVERSE (`SBIT (v %% SUC n) (SUC n) = SBIT (v %% SUC n) n * 2` by
ALL_TAC) THEN1 (
                                       ASM_SIMP_TAC std_ss [ADD_DIV_ADD_DIV]
                               ) THEN
                               SIMP_TAC arith_ss [bitTheory.SBIT_def, COND_RATOR, COND_RAND, EXP]
                       ) THEN
                       POP_ASSUM (fn thm => REWRITE_TAC[thm]) THEN
                       Q.PAT_ASSUM `a = b` (fn thm => REWRITE_TAC[GSYM thm]) THEN
                       ONCE_REWRITE_TAC[SUM_FUN_RANGE] THEN
                       FULL_SIMP_TAC arith_ss [fcpTheory.FCP_BETA, ADD_CLAUSES] THEN
                       SIMP_TAC std_ss [sum_numTheory.SUM_def] THEN
                       ONCE_REWRITE_TAC[SUM_FUN_RANGE] THEN
                       SIMP_TAC arith_ss [bitTheory.SBIT_def, SUC_ONE_ADD]
               ]
       ]
]);

(* ------------------------------------------------------------------------- *)
(* Elliptic curve theory to support the compiled functions.                  *)
(* ------------------------------------------------------------------------- *)

val example_prime_def = Define `example_prime = 751`;

val example_field_def = Define `example_field = GF example_prime`;

val example_curve_def = Define
  `example_curve = curve example_field 0 0 1 (example_prime - 1) 0`;

val ex_field_elt_def = Define
  `ex_field_elt (n : num) : word32 = n2w n`;

val ex_field_num_def = Define
  `ex_field_num (n : num) : word32 = ex_field_elt (n MOD example_prime)`;

val ex_curve_point_def = Define
  `ex_curve_point =
   affine_case example_curve (0w,0w) (\x y. (ex_field_elt x, ex_field_elt y))`;

(* ========================================================================= *)
(* All the below functions need to be compiled.                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Representing GF(p) field elements with words.                             *)
(* ------------------------------------------------------------------------- *)

val ex_field_zero_def = Define
  `ex_field_zero = ex_field_num 0`;

val ex_field_neg_def = Define
  `ex_field_neg (x : word32) =
   if x = 0w then 0w else n2w example_prime - x`;

val ex_field_add_def = Define
  `ex_field_add (x : word32, y : word32) =
   let z = x + y in
   if z < n2w example_prime then z else z - n2w example_prime`;

val ex_field_sub_def = Define
  `ex_field_sub (x : word32, y : word32) =
   ex_field_add (x, ex_field_neg y)`;

val ex_field_mult_def = Define
  `ex_field_mult (x : word32, y : word32) =
   word_mod (x * y) (n2w example_prime)`;

val (ex_field_exp_aux_def,ex_field_exp_aux_ind) = Defn.tprove
  (Hol_defn "ex_field_exp_aux"
   `ex_field_exp_aux (x : word32, n : word32, acc : word32) =
    if n = 0w then acc
    else
      let x' = ex_field_mult (x,x) in
      let n' = n >>> 1 in
      let acc' = if n && 1w = 0w then acc else ex_field_mult (acc,x) in
      ex_field_exp_aux (x',n',acc')`,
   WF_REL_TAC `measure (\(x,y,z). w2n y)`
   ++ RW_TAC arith_ss [w2n_lsr]
   ++ Know `~(w2n n = 0)` >> METIS_TAC [n2w_w2n]
   ++ Q.SPEC_TAC (`w2n n`,`n`)
   ++ POP_ASSUM (K ALL_TAC)
   ++ RW_TAC arith_ss []
   ++ Know `2 * (n DIV 2) <= n`
   >> PROVE_TAC [TWO, ellipticTheory.DIV_THEN_MULT]
   ++ DECIDE_TAC);

val ex_field_exp_def = Define
  `ex_field_exp (x : word32, n : word32) = ex_field_exp_aux (x,n,1w)`;

val ex_field_inv_def = Define
  `ex_field_inv (x : word32) =
   ex_field_exp (x, n2w (example_prime - 2))`;

val ex_field_div_def = Define
  `ex_field_div (x : word32, y : word32) =
   ex_field_mult (x, ex_field_inv y)`;

(* ------------------------------------------------------------------------- *)
(* Elliptic curve operations in terms of the above field operations.         *)
(* ------------------------------------------------------------------------- *)

val ex_curve_zero_def = Define
  `ex_curve_zero = ex_curve_point (curve_zero example_curve)`;

val ex_curve_neg_def = Define
  `ex_curve_neg (x1,y1) =
   let $~ = ex_field_neg in
   let $- = CURRY ex_field_sub in
   let $* = CURRY ex_field_mult in
   let a1 = ex_field_elt example_curve.a1 in
   let a3 = ex_field_elt example_curve.a3 in
   if (x1,y1) = ex_curve_zero then ex_curve_zero
   else
     let x = x1 in
     let y = ~y1 - a1 * x1 - a3 in
     (x,y)`;

val ex_curve_double_def = Define
  `ex_curve_double (x1,y1) =
   let $& = ex_field_num in
   let $~ = ex_field_neg in
   let $+ = CURRY ex_field_add in
   let $- = CURRY ex_field_sub in
   let $* = CURRY ex_field_mult in
   let $/ = CURRY ex_field_div in
   let $** = CURRY ex_field_exp in
   let a1 = ex_field_elt example_curve.a1 in
   let a2 = ex_field_elt example_curve.a2 in
   let a3 = ex_field_elt example_curve.a3 in
   let a4 = ex_field_elt example_curve.a4 in
   let a6 = ex_field_elt example_curve.a6 in
   if (x1,y1) = ex_curve_zero then ex_curve_zero
   else
     let d = & 2 * y1 + a1 * x1 + a3 in
     if d = ex_field_zero then ex_curve_zero
     else
       let l = (& 3 * x1 ** 2w + & 2 * a2 * x1 + a4 - a1 * y1) / d in
       let m = (~(x1 ** 3w) + a4 * x1 + & 2 * a6 - a3 * y1) / d in
       let x = l ** 2w + a1 * l - a2 - &2 * x1 in
       let y = ~(l + a1) * x - m - a3 in
       (x,y)`;

val curve_add_def = Define
  `curve_add (x1,y1,x2,y2) =
   if (x1 = x2) /\ (y1 = y2) then ex_curve_double (x1,y1)
   else
     let $& = ex_field_num in
     let $~ = ex_field_neg in
     let $+ = CURRY ex_field_add in
     let $- = CURRY ex_field_sub in
     let $* = CURRY ex_field_mult in
     let $/ = CURRY ex_field_div in
     let $** = CURRY ex_field_exp in
     let a1 = ex_field_elt example_curve.a1 in
     let a2 = ex_field_elt example_curve.a2 in
     let a3 = ex_field_elt example_curve.a3 in
     let a4 = ex_field_elt example_curve.a4 in
     let a6 = ex_field_elt example_curve.a6 in
     if (x1,y1) = ex_curve_zero then (x2,y2)
     else if (x2,y2) = ex_curve_zero then (x1,y1)
     else if x1 = x2 then ex_curve_zero
     else
       let d = x2 - x1 in
       let l = (y2 - y1) / d in
       let m = (y1 * x2 - y2 * x1) / d in
       let x = l ** 2w + a1 * l - a2 - x1 - x2 in
       let y = ~(l + a1) * x - m - a3 in
       (x,y)`;

val () = export_theory ();
