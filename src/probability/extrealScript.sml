(* ------------------------------------------------------------------------- *)
(* Measure Theory defined on the extended reals and includes Borel spaces    *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013, 2015)            *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Updated and further enriched by Chun Tian (2018-2020)                     *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open metisLib combinTheory pred_setTheory res_quanTools pairTheory RealArith
     prim_recTheory arithmeticTheory realTheory realLib real_sigmaTheory
     seqTheory limTheory Diff transcTheory jrhUtils pred_setLib tautLib;

open hurdUtils util_probTheory cardinalTheory;

val _ = new_theory "extreal";

fun METIS ths tm = prove(tm, METIS_TAC ths);
val set_ss = std_ss ++ PRED_SET_ss;

(* ********************************************* *)
(*              Type Definiton                   *)
(* ********************************************* *)

val extreal_def = Datatype
   `extreal = NegInf | PosInf | Normal real`;

(* INFINITY, the vertical position of UTF8.chr 0x2212 is better than "-" *)
val _ = Unicode.unicode_version {u = "+" ^ UTF8.chr 0x221E,
                                 tmnm = "PosInf"};
val _ = Unicode.unicode_version {u = UTF8.chr 0x2212 ^ UTF8.chr 0x221E,
                                 tmnm = "NegInf"};

val _ = TeX_notation {hol = "+" ^ UTF8.chr 0x221E,
                      TeX = ("\\ensuremath{+\\infty}", 1)};

val _ = TeX_notation {hol = "-" ^ UTF8.chr 0x221E,
                      TeX = ("\\ensuremath{-\\infty}", 1)};

Definition extreal_of_num_def :
    extreal_of_num n = Normal (&n)
End

Definition real_def :
    real x = if (x = NegInf) \/ (x = PosInf) then (0 :real)
             else @r. x = Normal r
End

(* convert an extreal set to a real set, used in borelTheory *)
Definition real_set_def :
    real_set s = {real x | x <> PosInf /\ x <> NegInf /\ x IN s}
End

Theorem real_normal :
    !x. real (Normal x) = x
Proof
    RW_TAC std_ss [real_def]
QED

Theorem normal_real :
    !x. x <> NegInf /\ x <> PosInf ==> (Normal (real x) = x)
Proof
    RW_TAC std_ss [real_def]
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >> Cases_on `x`
 >> METIS_TAC []
QED

(* ********************************************* *)
(*     Definitions of Arithmetic Operations      *)
(* ********************************************* *)

(* old definition, which (wrongly) allows `PosInf + NegInf = PosInf`:

val extreal_add_def = Define
  `(extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add PosInf a = PosInf) /\
   (extreal_add a PosInf = PosInf) /\
   (extreal_add NegInf b = NegInf) /\
   (extreal_add c NegInf = NegInf)`;

   new definition:
 *)
Definition extreal_add_def :
   (extreal_add (Normal x) (Normal y) = Normal (x + y)) /\
   (extreal_add (Normal _) a = a) /\
   (extreal_add b (Normal _) = b) /\
   (extreal_add NegInf NegInf = NegInf) /\
   (extreal_add PosInf PosInf = PosInf)
End

(* old definition, which (wrongly) allows `PosInf - PosInf = PosInf` and
   `NegInf - NegInf = PosInf`:

val extreal_sub_def = Define
  `(extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub PosInf a = PosInf) /\
   (extreal_sub b PosInf = NegInf) /\
   (extreal_sub NegInf NegInf = PosInf) /\
   (extreal_sub NegInf c = NegInf) /\
   (extreal_sub c NegInf = PosInf)`;

   new definition:
 *)
Definition extreal_sub_def :
   (extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub a (Normal _) = a) /\
   (extreal_sub (Normal _) NegInf = PosInf) /\
   (extreal_sub (Normal _) PosInf = NegInf) /\
   (extreal_sub NegInf PosInf = NegInf) /\
   (extreal_sub PosInf NegInf = PosInf)
End

Definition extreal_le_def :
   (extreal_le (Normal x) (Normal y) = (x <= y)) /\
   (extreal_le NegInf _ = T) /\
   (extreal_le _ PosInf = T) /\
   (extreal_le _ NegInf = F) /\
   (extreal_le PosInf _ = F)
End

Definition extreal_lt_def :
   extreal_lt x y = ~extreal_le y x
End

(* "The rationaly behind our definitions is to understand PosInf (or
    NegInf) in every instance as the limit of some (possibly each time
    different) sequence, and '0' as a bona fide zero. Then

       `0 * PosInf (or NegInf) = 0 * lim a_n = lim (0 * a_n) = lim 0 = 0`

    while expressions of the type `PosInf - PosInf` or `PosInf / PosInf`
    become `lim (a_n - b_n)` or `lim a_n / lim b_n` where two
    sequences compete and do not lead to unique results." [1, p.58]
 *)
Definition extreal_mul_def :
   (extreal_mul NegInf NegInf = PosInf) /\
   (extreal_mul NegInf PosInf = NegInf) /\
   (extreal_mul PosInf NegInf = NegInf) /\
   (extreal_mul PosInf PosInf = PosInf) /\
   (extreal_mul (Normal x) NegInf =
       (if x = 0 then (Normal 0) else (if 0 < x then NegInf else PosInf))) /\
   (extreal_mul NegInf (Normal y) =
       (if y = 0 then (Normal 0) else (if 0 < y then NegInf else PosInf))) /\
   (extreal_mul (Normal x) PosInf =
       (if x = 0 then (Normal 0) else (if 0 < x then PosInf else NegInf))) /\
   (extreal_mul PosInf (Normal y) =
       (if y = 0 then (Normal 0) else (if 0 < y then PosInf else NegInf))) /\
   (extreal_mul (Normal x) (Normal y) = Normal (x * y))
End

(* from now on, ``0x`` is intepreted as ``0 :extreal`` *)
val _ = add_numeral_form (#"x", SOME "extreal_of_num");

val _ = overload_on ("+",    Term `extreal_add`);
val _ = overload_on ("-",    Term `extreal_sub`);
val _ = overload_on ("*",    Term `extreal_mul`);
val _ = overload_on ("<=",   Term `extreal_le`);

(* ********************************************* *)
(*     Properties of Extended Real Numbers       *)
(* ********************************************* *)

Theorem extreal_cases :
    !x. (x = NegInf) \/ (x = PosInf) \/ (?r. x = Normal r)
Proof
    Cases >> RW_TAC std_ss []
QED

Theorem extreal_eq_zero[simp] :
    !x. (Normal x = 0) <=> (x = 0)
Proof
    RW_TAC std_ss [extreal_of_num_def]
QED

Theorem extreal_not_infty[simp] :
    !x. (Normal x <> NegInf) /\ (Normal x <> PosInf)
Proof
    RW_TAC std_ss []
QED

Theorem num_not_infty[simp] :
    !n. (&n <> NegInf) /\ (&n <> PosInf)
Proof
    RW_TAC std_ss [extreal_of_num_def]
QED

Theorem extreal_11[simp] :
    !a a'. (Normal a = Normal a') <=> (a = a')
Proof
    RW_TAC std_ss []
QED

(* ********************************************* *)
(*   Mored Definitions of Arithmetic Operations  *)
(* ********************************************* *)

(* old definition, which allows `extreal_inv (Normal 0) = Normal 0`:

val extreal_inv_def = Define
  `(extreal_inv NegInf = Normal 0) /\
   (extreal_inv PosInf = Normal 0) /\
   (extreal_inv (Normal x) = Normal (inv x)`;

   new definition, where `extreal_inv 0` is *unspecified*:
 *)
local
  val thm = Q.prove (
     `?f. (f NegInf = Normal 0) /\
          (f PosInf = Normal 0) /\
          (!r. r <> 0 ==> (f (Normal r) = Normal (inv r)))`,
   (* proof *)
      Q.EXISTS_TAC `\x. if (x = PosInf) \/ (x = NegInf) then Normal 0
                        else if x = Normal 0 then ARB
                        else Normal (inv (real x))` \\
      RW_TAC std_ss [extreal_not_infty, real_normal]);
in
  (* |- extreal_inv NegInf = Normal 0 /\
        extreal_inv PosInf = Normal 0 /\
        !r. r <> 0 ==> extreal_inv (Normal r) = Normal (inv r)
   *)
  val extreal_inv_def = new_specification
    ("extreal_inv_def", ["extreal_inv"], thm);
end;

Definition extreal_ainv_def :
   (extreal_ainv NegInf = PosInf) /\
   (extreal_ainv PosInf = NegInf) /\
   (extreal_ainv (Normal x) = Normal (- x))
End

(* old definition, which "deliberately" allows `0 / 0 = 0` [3]
val extreal_div_def = Define
   `extreal_div x y = extreal_mul x (extreal_inv y)`;

   new definition, where `x / 0`, `PosInf / PosInf` and `NegInf / NegInf`
   are all *unspecified*:
 *)
local
  val thm = Q.prove (
     `?f. (!r. f (Normal r) PosInf = Normal 0) /\
          (!r. f (Normal r) NegInf = Normal 0) /\
          (!x r. r <> 0 ==> (f x (Normal r) = extreal_mul x (extreal_inv (Normal r))))`,
   (* proof *)
      Q.EXISTS_TAC `\x y.
        if ((y = PosInf) \/ (y = NegInf)) /\ (?r. x = Normal r) then Normal 0
        else if y = Normal 0 then ARB
        else extreal_mul x (extreal_inv y)` \\
      RW_TAC std_ss [extreal_not_infty, real_normal]);
in
  (* |- (!r. extreal_div (Normal r) PosInf = Normal 0) /\
        (!r. extreal_div (Normal r) NegInf = Normal 0) /\
        !x r. r <> 0 ==> extreal_div x (Normal r) = x * extreal_inv (Normal r)
   *)
  val extreal_div_def = new_specification
    ("extreal_div_def", ["extreal_div"], thm);
end;

val extreal_abs_def = Define
  `(extreal_abs (Normal x) = Normal (abs x)) /\
   (extreal_abs _ = PosInf)`;

(* removed `extreal_logr b NegInf = NegInf` *)
val extreal_logr_def = Define
  `(extreal_logr b (Normal x) = Normal (logr b x)) /\
   (extreal_logr b PosInf = PosInf)`;

val extreal_lg_def = Define
   `extreal_lg x = extreal_logr 2 x`;

(* old definition: (`ln 0` is not defined)
val extreal_ln_def = Define
  `(extreal_ln (Normal x) = Normal (ln x)) /\
   (extreal_ln PosInf = PosInf)`;

   new definition: (ln 0 = NegInf)
 *)
local
  val thm = Q.prove (
     `?f. (!x. 0 < x ==> f (Normal x) = Normal (ln x)) /\
          (f (Normal 0) = NegInf) /\
          (f PosInf = PosInf)`,
      Q.EXISTS_TAC `\y. if (y = Normal 0) then NegInf
                        else if (y = PosInf) then PosInf
                        else if (?r. (y = Normal r) /\ r <> 0) then Normal (ln (real y))
                        else ARB` \\
      RW_TAC std_ss [extreal_not_infty, real_normal, REAL_LT_REFL]);
in
   (* |- (!x. 0 < x ==> extreal_ln (Normal x) = Normal (ln x)) /\
         extreal_ln (Normal 0) = NegInf /\
         extreal_ln PosInf = PosInf
    *)
   val extreal_ln_def = new_specification
     ("extreal_ln_def", ["extreal_ln"], thm);
end;

val extreal_exp_def = Define
  `(extreal_exp (Normal x) = Normal (exp x)) /\
   (extreal_exp PosInf = PosInf) /\
   (extreal_exp NegInf = Normal 0)`;

val extreal_pow_def = Define
  `(extreal_pow (Normal a) n = Normal (a pow n)) /\
   (extreal_pow PosInf n = (if n = 0 then Normal 1 else PosInf)) /\
   (extreal_pow NegInf n =
       (if n = 0 then Normal 1 else (if (EVEN n) then PosInf else NegInf)))`;

val extreal_powr_def = Define
   `extreal_powr x a = extreal_exp (extreal_mul a (extreal_ln x))`;

val extreal_sqrt_def = Define
  `(extreal_sqrt (Normal x) = Normal (sqrt x)) /\
   (extreal_sqrt PosInf = PosInf)`;

val _ = overload_on ("/",    Term `extreal_div`);
val _ = overload_on ("<",    Term `extreal_lt`);
val _ = overload_on ("~",    Term `extreal_ainv`);
val _ = overload_on ("numeric_negate",
                             Term `extreal_ainv`);
val _ = overload_on ("inv",  Term `extreal_inv`);
val _ = overload_on ("abs",  Term `extreal_abs`);
val _ = overload_on ("logr", Term `extreal_logr`);
val _ = overload_on ("lg",   Term `extreal_lg`);
val _ = overload_on ("ln",   Term `extreal_ln`);
val _ = overload_on ("exp",  Term `extreal_exp`);
val _ = overload_on ("pow",  Term `extreal_pow`);
val _ = overload_on ("powr", Term `extreal_powr`);
val _ = overload_on ("sqrt", Term `extreal_sqrt`);

(* to have the Unicode symbol for "inv" *)
val _ = overload_on ("realinv", ``extreal_inv``);

(* special-case squares and cubes for extreals (c.f. arithmeticTheory) *)

(* pow-2 integrals appear in Variances and many other probability lemmas *)
val _ = overload_on (UnicodeChars.sup_2, ``\x :extreal. x pow 2``);

(* pow-3 integrals appear in Liapounov's form of the central limit theorem *)
val _ = overload_on (UnicodeChars.sup_3, ``\x :extreal. x pow 3``);

(* pow-4 integrals appear in Cantelli's Strong Law of Large Numbers *)
val _ = add_rule {fixity = Suffix 2100,
                  term_name = UnicodeChars.sup_4,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK UnicodeChars.sup_4]};

val _ = overload_on (UnicodeChars.sup_4, ``\x :extreal. x pow 4``);
val _ = TeX_notation {hol = UnicodeChars.sup_4, TeX = ("\\HOLTokenSupFour{}", 1)};

(* ********************************************* *)
(*     Properties of Arithmetic Operations       *)
(* ********************************************* *)

Theorem mul_rzero[simp] :
    !x :extreal. x * 0 = 0
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def,extreal_of_num_def,REAL_MUL_RZERO]
QED

Theorem mul_lzero[simp] :
    !x :extreal. 0 * x = 0
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_LZERO]
QED

Theorem mul_rone[simp] :
    !x :extreal. x * 1 = x
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_RID]
QED

Theorem mul_lone[simp] :
    !x :extreal. 1 * x = x
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_LID]
QED

Theorem entire[simp] : (* was: mul2_zero *)
    !x y :extreal. (x * y = 0) <=> (x = 0) \/ (y = 0)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, num_not_infty, extreal_of_num_def,
                   extreal_11, REAL_ENTIRE]
QED

(***************)
(*    Order    *)
(***************)

val extreal_not_lt = store_thm ("extreal_not_lt",
  ``!x y:extreal. ~(x < y) <=> y <= x``,
  REWRITE_TAC [TAUT `(~a <=> b) <=> (a <=> ~b)`] THEN
  SIMP_TAC std_ss [extreal_lt_def]);

Theorem extreal_lt_eq :
    !x y. Normal x < Normal y <=> x < y
Proof
    METIS_TAC [extreal_lt_def, extreal_le_def, real_lt]
QED

Theorem extreal_le_eq :
    !x y. Normal x <= Normal y <=> x <= y
Proof
    METIS_TAC [extreal_le_def]
QED

Theorem le_refl[simp] :
    !x:extreal. x <= x
Proof
    Cases >> RW_TAC std_ss [extreal_le_def, REAL_LE_REFL]
QED

Theorem lt_refl[simp] :
    !x:extreal. ~(x < x)
Proof
    RW_TAC std_ss [extreal_lt_def, le_refl]
QED

val le_infty = store_thm
  ("le_infty", ``(!x. NegInf <= x /\ x <= PosInf) /\
                 (!x. x <= NegInf <=> (x = NegInf)) /\
                 (!x. PosInf <= x <=> (x = PosInf))``,
    RW_TAC std_ss []
 >> Cases_on `x`
 >> RW_TAC std_ss [extreal_le_def]);

val lt_infty = store_thm
  ("lt_infty", ``!x y. NegInf < Normal y /\ Normal y < PosInf /\
                       NegInf < PosInf /\ ~(x < NegInf) /\ ~(PosInf < x) /\
                      (x <> PosInf <=> x < PosInf) /\ (x <> NegInf <=> NegInf < x)``,
    Cases >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, lt_refl]);

val lt_imp_le = store_thm
  ("lt_imp_le", ``!x y :extreal. x < y ==> x <= y``,
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LT_IMP_LE]);

val lt_imp_ne = store_thm
  ("lt_imp_ne", ``!x y :extreal. x < y ==> x <> y``,
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LT_IMP_NE]);

val le_trans = store_thm
  ("le_trans", ``!x y z :extreal. x <= y /\ y <= z ==> x <= z``,
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_le_def,le_refl]
 >> METIS_TAC [REAL_LE_TRANS]);

val lt_trans = store_thm
  ("lt_trans", ``!x y z :extreal. x < y /\ y < z ==> x < z``,
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_lt_def, lt_refl, extreal_le_def, le_refl, GSYM real_lt]
 >> METIS_TAC [REAL_LT_TRANS]);

val let_trans = store_thm
  ("let_trans", ``!x y z:extreal. x <= y /\ y < z ==> x < z``,
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt,REAL_LET_TRANS]);

val le_antisym = store_thm
  ("le_antisym", ``!x y :extreal. (x <= y /\ y <= x) <=> (x = y)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, le_refl, REAL_LE_ANTISYM]);

val lt_antisym = store_thm
  ("lt_antisym", ``!x y. ~(x < y /\ y < x)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_infty, extreal_lt_eq]
 >> METIS_TAC [REAL_LT_ANTISYM, DE_MORGAN_THM]);

val lte_trans = store_thm
  ("lte_trans", ``!x y z:extreal. x < y /\ y <= z ==> x < z``,
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LTE_TRANS]);

val let_antisym = store_thm
  ("let_antisym", ``!x y. ~(x < y /\ y <= x)``,
    rpt GEN_TAC
 >> CCONTR_TAC >> fs []
 >> `x < x` by PROVE_TAC [lte_trans]
 >> PROVE_TAC [lt_refl]);

val le_not_infty = store_thm
  ("le_not_infty", ``!x. (0 <= x ==> x <> NegInf) /\
                         (x <= 0 ==> x <> PosInf)``,
    GEN_TAC >> NTAC 2 STRIP_TAC (* 2 goals here *)
 >> ONCE_REWRITE_TAC [lt_infty]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC (Q.SPECL [`NegInf`, `0`, `x`] lte_trans) \\
      PROVE_TAC [lt_infty, num_not_infty],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC (Q.SPECL [`x`, `0`, `PosInf`] let_trans) \\
      PROVE_TAC [lt_infty, num_not_infty] ]);

(* |- !x. 0 <= x ==> x <> NegInf, very useful in measureTheory *)
val pos_not_neginf = save_thm
  ("pos_not_neginf", GEN_ALL (List.nth (CONJUNCTS (SPEC_ALL le_not_infty), 0)));

(* dual version: |- !x. x <= 0 ==> x <> PosInf *)
val neg_not_posinf = save_thm
  ("neg_not_posinf", GEN_ALL (List.nth (CONJUNCTS (SPEC_ALL le_not_infty), 1)));

val le_total = store_thm
  ("le_total", ``!x y. x <= y \/ y <= x``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, REAL_LE_TOTAL]);

val lt_total = store_thm
  ("lt_total", ``!x y. (x = y) \/ x < y \/ y < x``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, GSYM real_lt, REAL_LT_TOTAL]);

val le_01 = store_thm
  ("le_01[simp]", ``0 <= 1``,
    RW_TAC std_ss [extreal_of_num_def, extreal_le_def, REAL_LE_01]);

val lt_01 = store_thm
  ("lt_01[simp]", ``0 < 1``,
    METIS_TAC [extreal_of_num_def, extreal_lt_def, extreal_le_def,
               REAL_LT_01, real_lt]);

val ne_01 = store_thm
  ("ne_01[simp]", ``0 <> 1``,
    RW_TAC std_ss [extreal_of_num_def, REAL_10]);

val le_02 = store_thm
  ("le_02[simp]", ``0 <= 2``,
    RW_TAC real_ss [extreal_of_num_def, extreal_le_def]);

val lt_02 = store_thm
  ("lt_02[simp]", ``0 < 2``,
    RW_TAC real_ss [extreal_of_num_def, extreal_lt_def, extreal_le_def]);

val lt_10 = store_thm
  ("lt_10[simp]", ``-1 < 0``,
    RW_TAC real_ss [extreal_of_num_def, extreal_lt_def, extreal_le_def, extreal_ainv_def]);

val ne_02 = store_thm
  ("ne_02[simp]", ``0 <> 2``,
    RW_TAC real_ss [extreal_of_num_def]);

val le_num = store_thm
  ("le_num", ``!n:num. 0 <= &n``,
    RW_TAC real_ss [extreal_of_num_def, extreal_le_def]);

val num_lt_infty = store_thm
  ("num_lt_infty[simp]", ``!n:num. &n < PosInf``,
    RW_TAC std_ss [extreal_of_num_def, lt_infty]);

val lt_le = store_thm
  ("lt_le", ``!x y. x < y <=> (x <= y /\ x <> y)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LT_LE]);

val le_lt = store_thm
  ("le_lt", ``!x y. (x <= y) <=> x < y \/ (x = y)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LE_LT]);

val le_neg = store_thm
  ("le_neg", ``!x y. -x <= -y <=> y <= x``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def, lt_infty, le_infty,
                   REAL_LE_NEG]);

val lt_neg = store_thm
  ("lt_neg", ``!x y. -x < -y <=> y < x``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def,  lt_infty,le_infty,
                   REAL_LT_NEG]);

val le_add = store_thm
  ("le_add", ``!x y :extreal. 0 <= x /\ 0 <= y ==> 0 <= x + y``,
    NTAC 2 Cases
  >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_of_num_def, REAL_LE_ADD]);

val lt_add = store_thm
  ("lt_add", ``!x y :extreal. 0 < x /\ 0 < y ==> 0 < x + y``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
  >> METIS_TAC [real_lt,REAL_LT_ADD]);

val let_add = store_thm
  ("let_add", ``!x y:extreal. 0 <= x /\ 0 < y ==> 0 < x + y``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
  >> METIS_TAC [real_lt,REAL_LET_ADD]);

val lte_add = store_thm
  ("lte_add", ``!x y:extreal. 0 < x /\ 0 <= y ==> 0 < x + y``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
  >> METIS_TAC [real_lt,REAL_LTE_ADD]);

val le_add2 = store_thm
  ("le_add2", ``!w x y z. w <= x /\ y <= z ==> w + y <= x + z``,
  NTAC 4 Cases
  >> RW_TAC std_ss [extreal_le_def, extreal_add_def, le_infty, le_refl]
  >> METIS_TAC [REAL_LE_ADD2]);

val lt_add2 = store_thm
  ("lt_add2", ``!w x y z. w < x /\ y < z ==> w + y < x + z``,
   rpt Cases
   >> RW_TAC std_ss [extreal_add_def, extreal_lt_eq, lt_infty, REAL_LT_ADD2]);

val let_add2 = store_thm
  ("let_add2", ``!w x y z. w <> NegInf /\ w <> PosInf /\ w <= x /\ y < z ==> w + y < x + z``,
  NTAC 4 Cases
  >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty,le_refl]
  >> METIS_TAC [real_lt, REAL_LET_ADD2]);

val let_add2_alt = store_thm
  ("let_add2_alt", ``!w x y z. x <> NegInf /\ x <> PosInf /\ w <= x /\ y < z ==> w + y < x + z``,
  NTAC 4 Cases
  >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty, le_refl]
  >> METIS_TAC [real_lt, REAL_LET_ADD2]);

val le_addr = store_thm
  ("le_addr", ``!x y. x <> NegInf /\ x <> PosInf ==> (x <= x + y <=> (0 <= y))``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                    extreal_not_infty, REAL_LE_ADDR]);

val le_addl_imp = store_thm
  ("le_addl_imp", ``!x y. 0 <= x ==> y <= x + y``,
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDL]);

val le_addr_imp = store_thm
  ("le_addr_imp", ``!x y. 0 <= y ==> x <= x + y``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                    extreal_not_infty, REAL_LE_ADDR]);

val le_ladd = store_thm
  ("le_ladd", ``!x y z. x <> NegInf /\ x <> PosInf ==> (x + y <= x + z <=> y <= z)``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD]);

val le_radd = store_thm
  ("le_radd", ``!x y z. x <> NegInf /\ x <> PosInf ==> (y + x <= z + x <=> y <= z)``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD]);

val le_radd_imp = store_thm
  ("le_radd_imp", ``!x y z. y <= z ==> y + x <= z + x``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD, le_infty, le_refl]);

val le_ladd_imp = store_thm
  ("le_ladd_imp", ``!x y z. y <= z ==> x + y <= x + z``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD, le_infty, le_refl]);

val lt_ladd = store_thm
  ("lt_ladd", ``!x y z. x <> NegInf /\ x <> PosInf ==> (x + y < x + z <=> y < z)``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_LADD]);

val lt_radd = store_thm
  ("lt_radd", ``!x y z. x <> NegInf /\ x <> PosInf ==> (y + x < z + x <=> y < z)``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_RADD]);

val lt_addl = store_thm
  ("lt_addl", ``!x y. y <> NegInf /\ y <> PosInf ==> (y < x + y <=> 0 < x)``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_lt_def, extreal_le_def,
                    le_infty, extreal_of_num_def, extreal_not_infty]
  >> METIS_TAC [REAL_ADD_COMM, REAL_LE_SUB_LADD,
                real_sub, REAL_NEG_GE0, REAL_LE_ADDL]);

(* two antecedents were added due to new definitions of ``extreal_add`` *)
val le_lneg = store_thm
  ("le_lneg", ``!x y. ((x <> NegInf /\ y <> NegInf) \/
                      (x <> PosInf /\ y <> PosInf)) ==> (-x <= y <=> 0 <= x + y)``,
  rpt Cases
  >> RW_TAC std_ss [extreal_ainv_def, extreal_le_def, extreal_add_def, extreal_sub_def,
                    le_infty, extreal_of_num_def, extreal_not_infty, REAL_LE_LNEG]);

val le_mul = store_thm
  ("le_mul", ``!x y :extreal. 0 <= x /\ 0 <= y ==> 0 <= x * y``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                    REAL_LE_MUL, GSYM real_lt]
  >> METIS_TAC [REAL_LT_LE, real_lte]);

val let_mul = store_thm
  ("let_mul", ``!x y :extreal. 0 <= x /\ 0 < y ==> 0 <= x * y``,
  rpt Cases
  >> RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq, lt_infty,
                     le_infty, le_refl, extreal_of_num_def]
  >> METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]);

val lte_mul = store_thm
  ("lte_mul", ``!x y :extreal. 0 < x /\ 0 <= y ==> 0 <= x * y``,
  rpt Cases
  >> RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq,
                     lt_infty, le_infty, le_refl, extreal_of_num_def]
  >> METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]);

val le_mul_neg = store_thm
  ("le_mul_neg", ``!x y :extreal. x <= 0 /\ y <= 0 ==> 0 <= x * y``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                    REAL_LE_MUL, GSYM real_lt]
  >> METIS_TAC
  [REAL_LE_NEG, REAL_NEG_0, REAL_NEG_MUL2, REAL_MUL_RZERO, REAL_LE_MUL]);

val mul_le = store_thm
  ("mul_le", ``!x y :extreal. 0 <= x /\ y <= 0 ==> x * y <= 0``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                    REAL_LE_MUL, GSYM real_lt]
  >- METIS_TAC [REAL_LT_LE, real_lt]
  >> `0 <= -r'` by METIS_TAC [REAL_LE_NEG, REAL_NEG_0]
  >> METIS_TAC [REAL_LE_NEG, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG]);

val lt_mul = store_thm
  ("lt_mul", ``!x y:extreal. 0 < x /\ 0 < y ==> 0 < x * y``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                    REAL_LT_MUL, lt_infty]);

val lt_mul_neg = store_thm
  ("lt_mul_neg", ``!x y :extreal. x < 0 /\ y < 0 ==> 0 < x * y``,
  rpt Cases >> RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq, lt_infty, extreal_mul_def]
  >> METIS_TAC [REAL_LT_LE, real_lt, REAL_LT_NEG, REAL_NEG_0, REAL_NEG_MUL2, REAL_LT_MUL]);

val mul_lt = store_thm
  ("mul_lt", ``!x y:extreal. 0 < x /\ y < 0 ==> x * y < 0``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def, REAL_LT_MUL, lt_infty]
  >- METIS_TAC [REAL_LT_LE, real_lt]
  >> `0 < -r'` by METIS_TAC [REAL_LT_NEG, REAL_NEG_0]
  >> METIS_TAC [REAL_MUL_RNEG, REAL_LT_MUL, REAL_LT_NEG, REAL_NEG_0]);

val mul_let = store_thm
  ("mul_let", ``!x y :extreal. 0 <= x /\ y < 0 ==> x * y <= 0``,
  NTAC 2 Cases
  >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def, le_refl, le_infty,
                     lt_infty, extreal_le_def]
  >> METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG, REAL_NEG_NEG,
                REAL_LE_NEG, real_lt, REAL_LT_LE]);

val mul_lte = store_thm
  ("mul_lte", ``!x y :extreal. 0 < x /\ y <= 0 ==> x * y <= 0``,
  NTAC 2 Cases
  >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def, le_refl, le_infty,
                     lt_infty, extreal_le_def]
  >> METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG, REAL_NEG_NEG,
                REAL_LE_NEG, real_lt, REAL_LT_LE]);

val le_lmul_imp = store_thm
  ("le_lmul_imp", ``!x y z :extreal. 0 <= z /\ x <= y ==> z * x <= z * y``,
  RW_TAC std_ss []
  >> Cases_on `z = 0` >- RW_TAC std_ss [mul_lzero,le_refl]
  >> `0 < z` by METIS_TAC [lt_le]
  >> Cases_on `x` >> Cases_on `y` >> Cases_on `z`
  >> RW_TAC real_ss [extreal_le_def,extreal_lt_eq,extreal_mul_def,REAL_LE_REFL,REAL_LT_REFL,
                     le_infty,lt_infty,extreal_of_num_def,REAL_LT_IMP_LE,GSYM real_lte,GSYM real_lt]
  >> METIS_TAC [real_lt,REAL_LT_LE,REAL_LTE_TRANS,lt_infty,extreal_lt_eq,extreal_le_def,
                extreal_of_num_def,REAL_LE_LMUL]);

val lt_rmul = store_thm
  ("lt_rmul", ``!x y z. 0 < z /\ z <> PosInf ==> (x * z < y * z <=> x < y)``,
  rpt Cases
  >> RW_TAC real_ss [extreal_lt_eq,extreal_mul_def,le_infty,lt_infty,extreal_of_num_def,
                     REAL_LT_REFL,REAL_LT_RMUL]);

val lt_lmul = store_thm
  ("lt_lmul", ``!x y z. 0 < x /\ x <> PosInf ==> (x * y < x * z <=> y < z)``,
  rpt Cases
  >> RW_TAC real_ss [extreal_lt_eq,extreal_mul_def,le_infty,lt_infty,extreal_of_num_def,
                     REAL_LT_REFL,REAL_LT_LMUL]);

val lt_mul2 = store_thm
  ("lt_mul2",
  ``!x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\ x1 <> PosInf /\ y1 <> PosInf /\
                  x1 < x2 /\ y1 < y2 ==> x1 * y1 < x2 * y2``,
  RW_TAC std_ss []
  >> `0 < x2 /\ 0 < y2` by METIS_TAC [let_trans]
  >> Cases_on `x1` >> Cases_on `y1`
  >> Cases_on `x2` >> Cases_on `y2`
  >> FULL_SIMP_TAC real_ss [extreal_lt_eq,extreal_le_def,extreal_mul_def,le_infty,lt_infty,
                            extreal_of_num_def,extreal_not_infty,REAL_LT_MUL2,real_lte]
  >> METIS_TAC [extreal_not_infty,lt_infty]);

val abs_0 = store_thm
  ("abs_0", ``extreal_abs 0 = 0``,
    METIS_TAC [extreal_abs_def, extreal_of_num_def, extreal_11, ABS_0]);

val abs_pos = store_thm
  ("abs_pos", ``!x :extreal. 0 <= abs x``,
  Cases >> RW_TAC std_ss [extreal_abs_def,ABS_POS,extreal_le_def,extreal_of_num_def,le_infty]);

val abs_neg = store_thm
  ("abs_neg", ``!x :extreal. x < 0 ==> (abs x = -x)``,
    RW_TAC std_ss [extreal_lt_def]
 >> Cases_on `x`
 >- REWRITE_TAC [extreal_abs_def, extreal_ainv_def]
 >- fs [extreal_of_num_def, le_infty]
 >> fs [extreal_abs_def, extreal_of_num_def, extreal_le_eq, abs, extreal_ainv_def]);

Theorem abs_refl :
    !x :extreal. (abs x = x) <=> (0 <= x)
Proof
    Cases
 >> RW_TAC std_ss [extreal_abs_def,le_infty,extreal_of_num_def,extreal_le_def,ABS_REFL]
QED

Theorem abs_abs[simp]:
    !x :extreal. abs(abs(x)) = abs(x)
Proof
    RW_TAC std_ss [abs_refl, abs_pos]
QED

Theorem let_total :
    !x y :extreal. x <= y \/ y < x
Proof
    rpt GEN_TAC
 >> STRIP_ASSUME_TAC (Q.SPECL [`x`, `y`] lt_total)
 >- (DISJ1_TAC >> REWRITE_TAC [le_lt] >> art [])
 >- (DISJ1_TAC >> MATCH_MP_TAC lt_imp_le >> art [])
 >> DISJ2_TAC >> art []
QED

Theorem lte_total :
    !x y :extreal. x < y \/ y <= x
Proof
    rpt GEN_TAC
 >> STRIP_ASSUME_TAC (Q.SPECL [`x`, `y`] lt_total)
 >- (DISJ2_TAC >> REWRITE_TAC [le_lt] >> art [])
 >- (DISJ1_TAC >> art [])
 >> DISJ2_TAC >> MATCH_MP_TAC lt_imp_le >> art []
QED

val abs_bounds = store_thm
  ("abs_bounds", ``!x k :extreal. abs x <= k <=> -k <= x /\ x <= k``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_abs_def, extreal_le_def, lt_infty,
                    le_infty, extreal_ainv_def, ABS_BOUNDS]);

val abs_bounds_lt = store_thm
  ("abs_bounds_lt", ``!x k :extreal. abs x < k <=> -k < x /\ x < k``,
  NTAC 2 Cases
  >> RW_TAC std_ss [extreal_abs_def,extreal_lt_eq,
                    lt_infty,le_infty,extreal_ainv_def]
  >> REAL_ARITH_TAC);

Theorem lt_abs_bounds :
   !k x :extreal. k < abs x <=> x < -k \/ k < x
Proof
    RW_TAC std_ss [extreal_lt_def]
 >> PROVE_TAC [abs_bounds]
QED

Theorem le_abs_bounds :
   !k x :extreal. k <= abs x <=> x <= -k \/ k <= x
Proof
   METIS_TAC [extreal_lt_def, abs_bounds_lt]
QED

val abs_not_infty = store_thm
  ("abs_not_infty", ``!x. x <> PosInf /\ x <> NegInf ==> abs x <> PosInf /\ abs x <> NegInf``,
    GEN_TAC >> STRIP_TAC
 >> `?c. x = Normal c` by PROVE_TAC [extreal_cases]
 >> ASM_REWRITE_TAC [extreal_abs_def, extreal_not_infty]);

val mul_lposinf = store_thm
  ("mul_lposinf", ``!x. 0 < x ==> (PosInf * x = PosInf)``,
   Cases >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, lt_infty,
                            num_not_infty, extreal_lt_eq]);

val mul_rposinf = store_thm
  ("mul_rposinf", ``!x. 0 < x ==> (x * PosInf = PosInf)``,
   Cases >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, lt_infty,
                            num_not_infty, extreal_lt_eq]);

(* this is proved by REAL_MEAN, SIMP_REAL_ARCH and SIMP_REAL_ARCH_NEG *)
val extreal_mean = store_thm
  ("extreal_mean", ``!x y :extreal. x < y ==> ?z. x < z /\ z < y``,
    rpt STRIP_TAC
 >> Cases_on `y` >- fs [lt_infty]
 >- (Cases_on `x`
     >- (Q.EXISTS_TAC `Normal 0` >> REWRITE_TAC [lt_infty])
     >- fs [lt_infty] \\
     STRIP_ASSUME_TAC (Q.SPEC `r` SIMP_REAL_ARCH) \\
     Q.EXISTS_TAC `&SUC n` >> REWRITE_TAC [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC `&n` >> art [] \\
     SIMP_TAC real_ss [])
 >> Cases_on `x`
 >- (STRIP_ASSUME_TAC (Q.SPEC `r` SIMP_REAL_ARCH_NEG) \\
     Q.EXISTS_TAC `-&SUC n` \\
    `-&SUC n = Normal (-&(SUC n))` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def] \\
     POP_ORW >> REWRITE_TAC [lt_infty, extreal_lt_eq] \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC `-&n` >> art [] \\
     SIMP_TAC real_ss [])
 >- fs [lt_infty]
 >> rename1 `Normal a < Normal b`
 >> `a < b` by PROVE_TAC [extreal_lt_eq]
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP REAL_MEAN))
 >> Q.EXISTS_TAC `Normal z` >> art [extreal_lt_eq]);

(***************)
(*   Addition  *)
(***************)

Theorem extreal_add_eq :
    !x y. Normal x + Normal y = Normal (x + y)
Proof
    rw [extreal_add_def]
QED

(* added two antecedents due to new definition of ``extreal_add``, excluded cases are:
   1. x = NegInf /\ y = PosInf
   2. x = PosInf /\ y = NegInf *)
Theorem add_comm :
    !x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (x + y = y + x)
Proof
    Cases >> Cases_on `y`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_COMM]
QED

val add_comm_normal = store_thm (* new *)
  ("add_comm_normal", ``!x y. Normal x + y = y + Normal x``,
    Strip >> Cases_on `y`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_COMM]);

(* added two antecedents due to new definition of ``extreal_add``, excluded cases are:
   - all mixes of PosInf and NegInf in x, y and z.
 *)
Theorem add_assoc :
    !x y z. (x <> NegInf /\ y <> NegInf /\ z <> NegInf) \/
            (x <> PosInf /\ y <> PosInf /\ z <> PosInf) ==>
            (x + (y + z) = x + y + z)
Proof
    Cases >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_ASSOC]
QED

val add_not_infty = store_thm
  ("add_not_infty",
  ``!x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf) /\
          (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)``,
    NTAC 2 Cases >> RW_TAC std_ss [extreal_add_def]);

Theorem add_rzero[simp] :
    !x :extreal. x + 0 = x
Proof
    Cases >> METIS_TAC [extreal_add_def, extreal_of_num_def, REAL_ADD_RID]
QED

Theorem add_lzero[simp] :
    !x :extreal. 0 + x = x
Proof
    Cases >> METIS_TAC [extreal_add_def, extreal_of_num_def, REAL_ADD_LID]
QED

(* added one ancedent in the first part due to new definition of ``extreal_add`` *)
val add_infty = store_thm
  ("add_infty",
  ``(!x. x <> NegInf ==> ((x + PosInf = PosInf) /\ (PosInf + x = PosInf))) /\
    (!x. x <> PosInf ==> ((x + NegInf = NegInf) /\ (NegInf + x = NegInf)))``,
    RW_TAC std_ss [] >> Cases_on `x`
 >> RW_TAC std_ss [extreal_add_def, extreal_not_infty]);

val EXTREAL_EQ_LADD = store_thm
  ("EXTREAL_EQ_LADD",
  ``!x y z. x <> NegInf /\ x <> PosInf ==> ((x + y = x + z) <=> (y = z))``,
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_add_def,REAL_EQ_LADD]);

val EXTREAL_EQ_RADD = store_thm
  ("EXTREAL_EQ_RADD",
  ``!x y z. z <> NegInf /\ z <> PosInf ==> ((x + z = y + z) <=> (x = y))``,
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_add_def,REAL_EQ_RADD]);

(* |- !x y. x <= 0 /\ y <= 0 ==> x + y <= 0 *)
val le_add_neg = save_thm
  ("le_add_neg",
    Q.GENL [`x`, `y`] (REWRITE_RULE [add_rzero] (Q.SPECL [`x`, `0`, `y`, `0`] le_add2)));

(* |- !x y. x < 0 /\ y < 0 ==> x + y < 0 *)
val lt_add_neg = save_thm
  ("lt_add_neg",
    Q.GENL [`x`, `y`] (REWRITE_RULE [add_rzero] (Q.SPECL [`x`, `0`, `y`, `0`] lt_add2)));

(* |- !x y. x <> NegInf /\ x <> PosInf /\ 0 < y ==> x < x + y *)
val lt_addr_imp = save_thm
  ("lt_addr_imp",
    Q.GENL [`x`, `y`]
      (REWRITE_RULE [le_refl, add_rzero] (Q.SPECL [`x`, `x`, `0`, `y`] let_add2)));

(*********************)
(*   Substraction    *)
(*********************)

Theorem extreal_sub_eq :
    !x y. Normal x - Normal y = Normal (x - y)
Proof
    rw [extreal_sub_def]
QED

Theorem sub_rzero[simp] :
    !x :extreal. x - 0 = x
Proof
    Cases >> METIS_TAC [extreal_sub_def, extreal_of_num_def, REAL_SUB_RZERO]
QED

Theorem sub_lzero[simp] :
    !x :extreal. 0 - x = -x
Proof
    Cases
 >> METIS_TAC [extreal_ainv_def, extreal_sub_def, extreal_of_num_def, REAL_SUB_LZERO]
QED

val sub_le_imp = store_thm
  ("sub_le_imp",
  ``!x y z. x <> NegInf /\ x <> PosInf /\ y <= z + x ==> y - x <= z``,
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_RADD]);

val sub_le_imp2 = store_thm
  ("sub_le_imp2",
  ``!x y z. y <> NegInf /\ y <> PosInf /\ y <= z + x ==> y - x <= z``,
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_RADD]);

val le_sub_imp = store_thm
  ("le_sub_imp", ``!x y z. x <> NegInf /\ x <> PosInf /\ y + x <= z ==> y <= z - x``,
  rpt Cases
  >> RW_TAC std_ss [extreal_le_def,extreal_add_def,extreal_sub_def,REAL_LE_SUB_LADD]);

val le_sub_imp2 = store_thm (* new *)
  ("le_sub_imp2", ``!x y z. z <> NegInf /\ z <> PosInf /\ y + x <= z ==> y <= z - x``,
  rpt Cases
  >> RW_TAC std_ss [extreal_le_def,extreal_add_def,extreal_sub_def,REAL_LE_SUB_LADD]);

val lt_sub_imp = store_thm
  ("lt_sub_imp", ``!x y z. x <> NegInf /\ y <> NegInf /\ y + x < z ==> y < z - x``,
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> METIS_TAC [real_lt, REAL_LT_ADD_SUB]);

Theorem lt_sub_imp' :
    !x y z. x <> PosInf /\ y <> PosInf /\ y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> METIS_TAC [real_lt, REAL_LT_ADD_SUB]
QED

val lt_sub_imp2 = store_thm (* new *)
  ("lt_sub_imp2", ``!x y z. x <> NegInf /\ x <> PosInf /\ y + x < z ==> y < z - x``,
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> METIS_TAC [real_lt, REAL_LT_ADD_SUB]);

val sub_lt_imp = store_thm
  ("sub_lt_imp", ``!x y z. x <> NegInf /\ x <> PosInf /\ y < z + x ==> y - x < z``,
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> METIS_TAC [real_lt, REAL_LT_SUB_RADD]);

Theorem sub_lt_eq :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y - x < z <=> y < z + x)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- PROVE_TAC [sub_lt_imp]
 >> Cases_on `x` >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> METIS_TAC [real_lt, REAL_LT_SUB_RADD]
QED

val sub_lt_imp2 = store_thm
  ("sub_lt_imp2", ``!x y z. z <> NegInf /\ z <> PosInf /\ y < z + x ==> y - x < z``,
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> METIS_TAC [real_lt, REAL_LT_SUB_RADD]);

val sub_zero_lt = store_thm
  ("sub_zero_lt", ``!x y. x < y ==> 0 < y - x``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LT]);

val sub_zero_lt2 = store_thm
  ("sub_zero_lt2", ``!x y. x <> NegInf /\ x <> PosInf /\ 0 < y - x ==> x < y``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LT]);

val sub_lt_zero = store_thm
  ("sub_lt_zero", ``!x y. x < y ==> x - y < 0``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_SUB_RADD]);

val sub_lt_zero2 = store_thm
  ("sub_lt_zero2", ``!x y. y <> NegInf /\ y <> PosInf /\ x - y < 0 ==> x < y``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_SUB_RADD]);

(* more antecedents added *)
val sub_zero_le = store_thm
  ("sub_zero_le", ``!x y. x <> NegInf /\ x <> PosInf ==> (x <= y <=> 0 <= y - x)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LE]);

val sub_le_zero = store_thm
  ("sub_le_zero", ``!x y. y <> NegInf /\ y <> PosInf ==> (x <= y <=> x - y <= 0)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_RADD]);

val le_sub_eq = store_thm
  ("le_sub_eq", ``!x y z. x <> NegInf /\ x <> PosInf ==> (y <= z - x <=> y + x <= z)``,
    METIS_TAC [le_sub_imp, sub_lt_imp, extreal_lt_def]);

val le_sub_eq2 = store_thm
  ("le_sub_eq2",
  ``!x y z. z <> NegInf /\ z <> PosInf /\ x <> NegInf /\ y <> NegInf ==>
           (y <= z - x <=> y + x <= z)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, lt_infty,
                    extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_LADD]);

val sub_le_eq = store_thm
  ("sub_le_eq",
  ``!x y z. x <> NegInf /\ x <> PosInf ==> (y - x <= z <=> y <= z + x)``,
    METIS_TAC [sub_le_imp, lt_sub_imp2, extreal_lt_def]);

val sub_le_eq2 = store_thm
  ("sub_le_eq2",
  ``!x y z. y <> NegInf /\ y <> PosInf /\ x <> NegInf /\ z <> NegInf ==>
           (y - x <= z <=> y <= z + x)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, lt_infty,
                    extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_RADD]);

val sub_le_switch = store_thm
  ("sub_le_switch",
  ``!x y z. x <> NegInf /\ x <> PosInf /\ z <> NegInf /\ z <> PosInf ==>
           (y - x <= z <=> y - z <= x)``,
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_le_def, le_infty, lt_infty]
 >> REAL_ARITH_TAC);

val sub_le_switch2 = store_thm
  ("sub_le_switch2",
  ``!x y z. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
           (y - x <= z <=> y - z <= x)``,
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_le_def, le_infty, lt_infty]
 >> REAL_ARITH_TAC);

(* more antecedents (x <> NegInf /\ y <> NegInf) added *)
val lt_sub = store_thm
  ("lt_sub",
  ``!x y z. x <> NegInf /\ y <> NegInf /\ z <> NegInf /\ z <> PosInf ==>
           (y + x < z <=> y < z - x)``,
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, le_infty]
 >> METIS_TAC [REAL_LE_SUB_RADD]);

Theorem lt_sub' :
    !x y z. x <> PosInf /\ y <> PosInf /\ z <> NegInf /\ z <> PosInf ==>
           (y + x < z <=> y < z - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, le_infty]
 >> METIS_TAC [REAL_LE_SUB_RADD]
QED

val sub_add2 = store_thm
  ("sub_add2", ``!x y. x <> NegInf /\ x <> PosInf ==> (x + (y - x) = y)``,
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def, REAL_SUB_ADD2]);

val add_sub = store_thm
  ("add_sub", ``!x y. y <> NegInf /\ y <> PosInf ==> (x + y - y = x)``,
 rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, REAL_ADD_SUB_ALT]);

val add_sub2 = store_thm
  ("add_sub2", ``!x y. y <> NegInf /\ y <> PosInf ==> (y + x - y = x)``,
   rpt Cases
>> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                  extreal_sub_def, REAL_ADD_SUB]);

val sub_add = store_thm
  ("sub_add", ``!x y. y <> NegInf /\ y <> PosInf ==> (x - y + y = x)``,
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, REAL_SUB_ADD]);

val extreal_sub_add = store_thm
  ("extreal_sub_add",
  ``!x y. (x <> NegInf /\ y <> PosInf) \/ (x <> PosInf /\ y <> NegInf) ==>
          (x - y = x + -y)``,
    rpt Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_sub_def, extreal_add_def, real_sub]);

Theorem sub_0 :
    !x y :extreal. (x - y = 0) ==> (x = y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, num_not_infty, extreal_of_num_def, extreal_11,
                   REAL_SUB_0]
QED

Theorem sub_eq_0 :
    !x y. x <> PosInf /\ x <> NegInf /\ (x = y) ==> (x - y = 0)
Proof
    RW_TAC std_ss []
 >> `?a. x = Normal a` by METIS_TAC [extreal_cases]
 >> ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_sub_def,
                         extreal_11, REAL_SUB_REFL]
QED

Theorem neg_neg[simp] :
    !x. --x = x
Proof
    Cases >> RW_TAC std_ss [extreal_ainv_def, REAL_NEG_NEG]
QED

Theorem neg_0[simp] :
    -0 = 0
Proof
    RW_TAC real_ss [extreal_ainv_def, extreal_of_num_def]
QED

Theorem neg_eq0[simp] :
    !x :extreal. (-x = 0) <=> (x = 0)
Proof
    Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_of_num_def, REAL_NEG_EQ0]
QED

Theorem eq_neg[simp] :
    !x y :extreal. (-x = -y) <=> (x = y)
Proof
    NTAC 2 Cases >> RW_TAC std_ss [extreal_ainv_def, REAL_EQ_NEG]
QED

val neg_minus1 = store_thm
  ("neg_minus1", ``!x. -x = -1 * x``,
    Cases >> RW_TAC real_ss [extreal_ainv_def,extreal_of_num_def,extreal_mul_def]);

(* changed statements (was ``!x y :extreal. x - -y = x + y``) *)
val sub_rneg = store_thm
  ("sub_rneg", ``!c x. Normal c - - x = Normal c + x``,
    GEN_TAC >> Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, REAL_SUB_RNEG]);

val sub_lneg = store_thm
  ("sub_lneg",
  ``!x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (-x - y = -(x + y))``,
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, REAL_SUB_LNEG]);

val neg_add = store_thm
  ("neg_add",
  ``!x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (-(x + y) = -x + -y)``,
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, REAL_NEG_ADD]);

val neg_sub = store_thm
  ("neg_sub",
  ``!x y. (x <> NegInf /\ x <> PosInf) \/ (y <> NegInf /\ y <> PosInf) ==>
          (-(x - y) = y - x)``,
    rpt Cases >> RW_TAC std_ss [extreal_sub_def, extreal_ainv_def, REAL_NEG_SUB]);

val sub_not_infty = store_thm
  ("sub_not_infty",
  ``!x y. (x <> NegInf /\ y <> PosInf ==> x - y <> NegInf) /\
          (x <> PosInf /\ y <> NegInf ==> x - y <> PosInf)``,
    rpt Cases >> RW_TAC std_ss [extreal_sub_def]);

val le_lsub_imp = store_thm
  ("le_lsub_imp", ``!x y z. y <= z ==> x - z <= x - y``,
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl]
 >> METIS_TAC [real_sub, REAL_LE_ADD2, REAL_LE_NEG, REAL_LE_REFL]);

val le_rsub_imp = store_thm
  ("le_rsub_imp", ``!x y z. x <= y ==> x - z <= y - z``,
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl]
 >> METIS_TAC [real_sub, REAL_LE_ADD2, REAL_LE_NEG, REAL_LE_REFL]);

val eq_sub_ladd_normal = store_thm
  ("eq_sub_ladd_normal", ``!x y z. (x = y - Normal z) <=> (x + Normal z = y)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl,
                   extreal_add_def, REAL_EQ_SUB_LADD]);

val eq_sub_radd = store_thm
  ("eq_sub_radd", ``!x y z. y <> NegInf /\ y <> PosInf ==> ((x - y = z) <=> (x = z + y))``,
  rpt Cases
  >> RW_TAC std_ss [extreal_add_def,extreal_sub_def,REAL_EQ_SUB_RADD]);

val eq_sub_ladd = store_thm
  ("eq_sub_ladd", ``!x y z. z <> NegInf /\ z <> PosInf ==> ((x = y - z) <=> (x + z = y))``,
    rpt Cases
  >> RW_TAC std_ss [extreal_add_def, extreal_sub_def, REAL_EQ_SUB_LADD]);

val eq_sub_switch = store_thm
  ("eq_sub_switch", ``!x y z. (x = Normal z - y) <=> (y = Normal z - x)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl, extreal_add_def]
 >> REAL_ARITH_TAC);

val eq_add_sub_switch = store_thm
  ("eq_add_sub_switch",
  ``!a b c d. b <> NegInf /\ b <> PosInf /\ c <> NegInf /\ c <> PosInf ==>
             ((a + b = c + d) <=> (a - c = d - b))``,
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def,extreal_sub_def]
 >> REAL_ARITH_TAC);

val sub_refl = store_thm
  ("sub_refl", ``!x. (x <> NegInf) /\ (x <> PosInf) ==> (x - x = 0)``,
    Cases >> RW_TAC real_ss [extreal_sub_def,extreal_of_num_def]);

val sub_infty = store_thm
  ("sub_infty", ``(!x. x <> NegInf ==> (x - NegInf = PosInf)) /\
                  (!x. x <> PosInf ==> (x - PosInf = NegInf)) /\
                  (!x. x <> PosInf ==> (PosInf - x = PosInf)) /\
                  (!x. x <> NegInf ==> (NegInf - x = NegInf))``,
    RW_TAC std_ss []
 >> Cases_on `x` >> fs [extreal_sub_def]);

val abs_unbounds = store_thm
  ("abs_unbounds", ``!x k :extreal. 0 <= k ==> (k <= abs x <=> x <= -k \/ k <= x)``,
    rpt STRIP_TAC
 >> Cases_on `0 <= x`
 >- (`abs x = x` by PROVE_TAC [abs_refl] >> POP_ORW \\
     EQ_TAC >> RW_TAC std_ss [] \\
     `-k <= 0` by METIS_TAC [le_neg, neg_neg, neg_0] \\
     `x <= 0` by PROVE_TAC [le_trans] \\
     `x = 0` by PROVE_TAC [le_antisym] >> fs [] \\
     METIS_TAC [le_neg, neg_neg, neg_0])
 >> fs [GSYM extreal_lt_def]
 >> `abs x = -x` by PROVE_TAC [abs_neg] >> POP_ORW
 >> EQ_TAC >> RW_TAC std_ss [] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      `x <= -k` by PROVE_TAC [le_neg, neg_neg] >> DISJ1_TAC >> art [],
      (* goal 2 (of 3) *)
      PROVE_TAC [le_neg, neg_neg],
      (* goal 3 (of 3), the impossible case *)
      `k < 0` by PROVE_TAC [let_trans] \\
      PROVE_TAC [let_antisym] ]);

Theorem le_abs :
    !x :extreal. x <= abs x /\ -x <= abs x
Proof
    GEN_TAC
 >> `0 <= x \/ x < 0` by PROVE_TAC [let_total]
 >| [ (* goal 1 (of 2) *)
      `abs x = x` by PROVE_TAC [GSYM abs_refl] >> POP_ORW \\
      rw [le_refl] \\
      MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `0` >> art [] \\
      POP_ASSUM (REWRITE_TAC o wrap o
                  (REWRITE_RULE [Once (GSYM le_neg), neg_0])),
      (* goal 2 (of 2) *)
      IMP_RES_TAC abs_neg >> POP_ORW \\
      rw [le_refl] \\
      MATCH_MP_TAC lt_imp_le \\
      MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC `0` >> art [] \\
      POP_ASSUM (REWRITE_TAC o wrap o
                  (REWRITE_RULE [Once (GSYM lt_neg), neg_0])) ]
QED

Theorem abs_eq_0[simp] :
    !x. (abs x = 0) <=> (x = 0)
Proof
    GEN_TAC
 >> reverse EQ_TAC >- rw [abs_0]
 >> `0 <= abs x` by PROVE_TAC [abs_pos]
 >> rw [Once (GSYM le_antisym)]
 >> fs [REWRITE_RULE [neg_0, le_antisym] (Q.SPECL [`x`, `0`] abs_bounds)]
QED

Theorem abs_le_0[simp] :
    !x. abs x <= 0 <=> (x = 0)
Proof
    METIS_TAC [abs_pos, abs_eq_0, le_antisym]
QED

Theorem abs_gt_0[simp] :
    !x. 0 < abs x <=> x <> 0
Proof
    RW_TAC std_ss [Once (GSYM abs_eq_0)]
 >> STRIP_ASSUME_TAC (REWRITE_RULE [le_lt] (Q.SPEC `x` abs_pos))
 >- fs [lt_le]
 >> FULL_SIMP_TAC std_ss [lt_refl]
QED

Theorem abs_triangle :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x + y) <= abs(x) + abs(y)
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> Cases_on `y`
 >> rw [extreal_abs_def, extreal_add_def, extreal_le_eq, ABS_TRIANGLE]
QED

Theorem abs_triangle_sub :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x) <= abs(y) + abs(x - y)
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> Cases_on `y`
 >> rw [extreal_abs_def, extreal_add_def, extreal_sub_def, extreal_le_eq, ABS_TRIANGLE_SUB]
QED

(*********************)
(*   Multiplication  *)
(*********************)

val mul_comm = store_thm
  ("mul_comm", ``!x y:extreal. x * y = y * x``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_mul_def, REAL_MUL_COMM]);

val mul_assoc = store_thm
  ("mul_assoc", ``!x y z:extreal. x * (y * z) = x * y * z``,
    NTAC 3 Cases
 >> RW_TAC real_ss [extreal_mul_def, REAL_MUL_ASSOC, REAL_MUL_LZERO,
                    REAL_MUL_RZERO, REAL_ENTIRE, REAL_LT_LMUL_0, REAL_POS_NZ,
                    DE_MORGAN_THM]
 >> FULL_SIMP_TAC real_ss [DE_MORGAN_THM, REAL_NOT_LT, REAL_LT_LMUL_0, GSYM REAL_LT_LE]
 >> METIS_TAC [REAL_LT_LMUL_0_NEG, REAL_LT_RMUL_0_NEG, REAL_LT_RMUL_NEG_0,
               REAL_LT_LE, REAL_LT_GT, REAL_ENTIRE, REAL_LT_LMUL_NEG_0,
               REAL_LT_LMUL_NEG_0_NEG, REAL_LT_RMUL_0, REAL_LT_LMUL_0,
               REAL_LT_RMUL_NEG_0_NEG]);

val mul_infty = store_thm (* new *)
  ("mul_infty",
  ``!x. 0 < x ==> (PosInf * x = PosInf) /\ (x * PosInf = PosInf) /\
                  (NegInf * x = NegInf) /\ (x * NegInf = NegInf)``,
    GEN_TAC >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (Cases_on `x = PosInf` >- art [extreal_mul_def] \\
     `x <> NegInf` by PROVE_TAC [lt_imp_le, pos_not_neginf] \\
     `?r. x = Normal r` by PROVE_TAC [extreal_cases] \\
     `0 < r` by PROVE_TAC [extreal_of_num_def, extreal_lt_eq] \\
     `r <> 0` by PROVE_TAC [REAL_LT_IMP_NE] \\
     ASM_SIMP_TAC std_ss [extreal_mul_def]) >> DISCH_TAC
 >> CONJ_TAC >- ASM_REWRITE_TAC [Once mul_comm]
 >> STRONG_CONJ_TAC
 >- (Cases_on `x = PosInf` >- art [extreal_mul_def] \\
     `x <> NegInf` by PROVE_TAC [lt_imp_le, pos_not_neginf] \\
     `?r. x = Normal r` by PROVE_TAC [extreal_cases] \\
     `0 < r` by PROVE_TAC [extreal_of_num_def, extreal_lt_eq] \\
     `r <> 0` by PROVE_TAC [REAL_LT_IMP_NE] \\
     ASM_SIMP_TAC std_ss [extreal_mul_def]) >> DISCH_TAC
 >> ASM_REWRITE_TAC [Once mul_comm]);

val mul_not_infty = store_thm
  ("mul_not_infty",
  ``(!c y. 0 <= c /\ y <> NegInf ==> Normal (c) * y <> NegInf) /\
    (!c y. 0 <= c /\ y <> PosInf ==> Normal (c) * y <> PosInf) /\
    (!c y. c <= 0 /\ y <> NegInf ==> Normal (c) * y <> PosInf) /\
    (!c y. c <= 0 /\ y <> PosInf ==> Normal (c) * y <> NegInf)``,
    RW_TAC std_ss [] >> Cases_on `y`
 >> RW_TAC std_ss [extreal_mul_def, extreal_le_def]
 >> METIS_TAC [real_lte, REAL_LE_ANTISYM]);

val mul_not_infty2 = store_thm
  ("mul_not_infty2",
  ``!x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
         (x * y <> NegInf) /\ (x * y <> PosInf)``,
    rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, extreal_not_infty]);

(* two variants of mul_lt and mul_le *)
val mul_lt2 = store_thm
  ("mul_lt2", ``!x y :extreal. x < 0 /\ 0 < y ==> x * y < 0``,
    METIS_TAC [mul_comm, mul_lt]);

val mul_le2 = store_thm
  ("mul_le2", ``!x y :extreal. x <= 0 /\ 0 <= y ==> x * y <= 0``,
    METIS_TAC [mul_comm, mul_le]);

val add_ldistrib_pos = store_thm
  ("add_ldistrib_pos",
  ``!x y z. 0 <= y /\ 0 <= z ==> (x * (y + z) = x * y + x * z)``,
    NTAC 3 Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_mul_def, extreal_le_def,
                    extreal_of_num_def, real_lt, REAL_LT_ANTISYM,
                    REAL_LE_ANTISYM, REAL_ADD_LID, REAL_ADD_RID, REAL_LT_LE]
 >> FULL_SIMP_TAC real_ss [GSYM real_lt, GSYM real_lte]
 >> METIS_TAC [REAL_LE_ANTISYM, REAL_LT_ADD, REAL_LT_IMP_LE, REAL_LT_IMP_NE,
               REAL_LT_LE, REAL_ADD_LDISTRIB]);

val add_ldistrib_neg = store_thm
  ("add_ldistrib_neg",
  ``!x y z. y <= 0 /\ z <= 0 ==> (x * (y + z) = x * y + x * z)``,
    NTAC 3 Cases (* 27 sub-goals here *)
 >> RW_TAC real_ss [extreal_add_def, extreal_mul_def, extreal_le_def,
                    extreal_of_num_def, real_lt, REAL_LT_ANTISYM,
                    REAL_LE_ANTISYM, REAL_ADD_LID, REAL_ADD_RID, REAL_LT_LE] (* 17 goals *)
 >> FULL_SIMP_TAC real_ss [GSYM real_lt, GSYM real_lte, REAL_ADD_LDISTRIB]   (*  4 goals *)
 >> (Cases_on `0 < r` >- RW_TAC std_ss [] \\
     Cases_on `0 < r'` >- RW_TAC std_ss [] \\
     `r < 0 /\ r' < 0` by METIS_TAC [real_lte, REAL_LT_LE] \\
     METIS_TAC [REAL_LT_ADD2, REAL_ADD_LID, REAL_LT_IMP_NE, REAL_LT_ANTISYM]));

(* changed var name from `x` to `r` *)
val add_ldistrib_normal = store_thm
  ("add_ldistrib_normal",
  ``!r y z. (y <> PosInf /\ z <> PosInf) \/ (y <> NegInf /\ z <> NegInf)
        ==> (Normal r * (y + z) = Normal r * y + Normal r * z)``,
    RW_TAC std_ss [] >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_add_def] (* 8 sub-goals here, same tacticals *)
 >> (Cases_on `r = 0`
     >- METIS_TAC [extreal_of_num_def, mul_lzero, add_lzero] \\
     RW_TAC std_ss [extreal_mul_def, extreal_add_def, REAL_ADD_LDISTRIB]));

val add_ldistrib_normal2 = save_thm (* for backward compatibility *)
  ("add_ldistrib_normal2", add_ldistrib_normal);

val add_rdistrib_normal = store_thm
  ("add_rdistrib_normal",
  ``!x y z. (y <> PosInf /\ z <> PosInf) \/ (y <> NegInf /\ z <> NegInf) ==>
            ((y + z) * Normal x = y * Normal x + z * Normal x)``,
    RW_TAC std_ss []
 >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_add_def]
 >> (Cases_on `x = 0`
     >- METIS_TAC [extreal_of_num_def, mul_rzero, add_rzero] \\
     RW_TAC std_ss [extreal_mul_def, extreal_add_def, REAL_ADD_RDISTRIB]));

val add_rdistrib_normal2 = save_thm (* for backward compatibility *)
  ("add_rdistrib_normal2", add_rdistrib_normal);

Theorem add_ldistrib :
    !x y z. (0 <= y /\ 0 <= z) \/ (y <= 0 /\ z <= 0) ==>
            (x * (y + z) = x * y + x * z)
Proof
    METIS_TAC [add_ldistrib_pos, add_ldistrib_neg]
QED

Theorem add_rdistrib :
    !x y z. (0 <= y /\ 0 <= z) \/ (y <= 0 /\ z <= 0) ==>
            ((y + z) * x = y * x + z * x)
Proof
    METIS_TAC [add_ldistrib, mul_comm]
QED

val mul_lneg = store_thm
  ("mul_lneg", ``!x y. -x * y = -(x * y)``,
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_ainv_def, extreal_mul_def, REAL_MUL_LNEG, REAL_NEG_EQ0]
 >> METIS_TAC [REAL_NEG_GT0, REAL_LT_REFL, REAL_LT_TRANS, real_lte, REAL_LE_ANTISYM]);

val mul_rneg = store_thm
  ("mul_rneg", ``!x y. x * -y = -(x * y)``,
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_ainv_def, extreal_mul_def, REAL_MUL_RNEG, REAL_NEG_EQ0]
 >> METIS_TAC [REAL_NEG_GT0, REAL_LT_REFL, REAL_LT_TRANS, real_lte, REAL_LE_ANTISYM]);

val neg_mul2 = store_thm
  ("neg_mul2", ``!x y. -x * -y = x * y``,
    rpt Cases >> RW_TAC real_ss [extreal_mul_def, extreal_ainv_def, REAL_NEG_EQ0]
 >> METIS_TAC [REAL_LT_NEG, REAL_NEG_0, REAL_LT_ANTISYM, real_lt, REAL_LE_ANTISYM]);

(* NOTE: basically all involves values are normal reals *)
val add2_sub2 = store_thm
  ("add2_sub2",
  ``!a b c d. a <> PosInf /\ b <> PosInf /\ c <> PosInf /\ d <> PosInf /\
              a <> NegInf /\ b <> NegInf /\ c <> NegInf /\ d <> NegInf
         ==> (a - b + (c - d) = (a + c - (b + d)))``,
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_sub_def]
 >> REWRITE_TAC [REAL_ADD2_SUB2]);

val sub_ldistrib = store_thm
  ("sub_ldistrib",
  ``!x y z. x <> NegInf /\ x <> PosInf /\
            y <> NegInf /\ y <> PosInf /\
            z <> NegInf /\ z <> PosInf ==> (x * (y - z) = x * y - x * z)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_sub_def, extreal_mul_def,
                    REAL_SUB_LDISTRIB]);

val sub_rdistrib = store_thm
  ("sub_rdistrib",
  ``!x y z. x <> NegInf /\ x <> PosInf /\
            y <> NegInf /\ y <> PosInf /\
            z <> NegInf /\ z <> PosInf ==> ((x - y) * z = x * z - y * z)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_sub_def, extreal_mul_def,
                    REAL_SUB_RDISTRIB]);

val mul_linv = store_thm
  ("mul_linv", ``!x. x <> 0 /\ x <> PosInf /\ x <> NegInf ==> (inv x * x = 1)``,
    Cases
 >> RW_TAC real_ss [extreal_div_def, extreal_mul_def, extreal_inv_def,
                    extreal_not_infty, extreal_of_num_def, REAL_MUL_LINV]);

val mul_linv_pos = store_thm
  ("mul_linv_pos", ``!x. 0 < x /\ x <> PosInf ==> (inv x * x = 1)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC mul_linv >> fs [lt_le]
 >> MATCH_MP_TAC pos_not_neginf >> art []);

(* changed `0 < z` to `0 <= z` *)
val le_rmul_imp = store_thm
  ("le_rmul_imp", ``!x y z :extreal. 0 <= z /\ x <= y ==> x * z <= y * z``,
    rpt STRIP_TAC
 >> `x * z = z * x` by PROVE_TAC [mul_comm] >> POP_ORW
 >> `y * z = z * y` by PROVE_TAC [mul_comm] >> POP_ORW
 >> MATCH_MP_TAC le_lmul_imp >> art []);

Theorem abs_mul :
    !x y :extreal. abs (x * y) = abs x * abs y
Proof
    rpt STRIP_TAC
 >> Cases_on `x` >> Cases_on `y`
 >> RW_TAC std_ss [extreal_abs_def, extreal_mul_def]
 >> fs []
 >> REWRITE_TAC [ABS_MUL]
QED

(*********************)
(*   Division        *)
(*********************)

(* added antecedent `y <> 0` *)
val extreal_div_eq = store_thm
  ("extreal_div_eq", ``!x y. y <> 0 ==> (Normal x / Normal y = Normal (x / y))``,
    rpt Cases
 >> RW_TAC std_ss [extreal_div_def, extreal_inv_def, extreal_mul_def, real_div]);

val extreal_inv_eq = store_thm
  ("extreal_inv_eq", ``!x. x <> 0 ==> (inv (Normal x) = Normal (inv x))``,
    METIS_TAC [extreal_inv_def]);

val normal_inv_eq = store_thm
  ("normal_inv_eq", ``!x. x <> 0 ==> (Normal (inv x) = inv (Normal x))``,
    METIS_TAC [extreal_inv_def]);

Theorem inv_one[simp] :
    extreal_inv 1 = 1
Proof
    RW_TAC std_ss [extreal_inv_def, extreal_of_num_def, REAL_10, REAL_INV1]
QED

val inv_1over = store_thm
  ("inv_1over", ``!x. x <> 0 ==> (inv x = 1 / x)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_inv_def, extreal_div_def, extreal_mul_def,
                    extreal_of_num_def, REAL_10, REAL_INV1]);

Theorem div_one[simp] :
    !x :extreal. x / 1 = x
Proof
    RW_TAC real_ss [extreal_div_def, extreal_of_num_def, extreal_inv_def]
 >> REWRITE_TAC [REAL_INV1, GSYM extreal_of_num_def, mul_rone]
QED

val div_refl = store_thm
  ("div_refl",
  ``!x :extreal. x <> 0 /\ x <> PosInf /\ x <> NegInf ==> (x / x = 1)``,
    Cases
 >> RW_TAC real_ss [extreal_div_def, extreal_mul_def, extreal_inv_def,
                    extreal_not_infty, extreal_of_num_def, REAL_MUL_RINV]);

val div_refl_pos = store_thm
  ("div_refl_pos",
  ``!x :extreal. 0 < x /\ x <> PosInf ==> (x / x = 1)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC div_refl >> fs [lt_le]
 >> MATCH_MP_TAC pos_not_neginf >> art []);

val inv_pos = store_thm
  ("inv_pos", ``!x. 0 < x /\ x <> PosInf ==> 0 < 1 / x``,
    Cases
 >> RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_lt_def,
                    extreal_mul_def, extreal_le_def, lt_infty, le_infty]
 >> FULL_SIMP_TAC real_ss [Once real_lte, Once REAL_LT_LE, extreal_div_eq,
                           extreal_le_def]
 >> METIS_TAC [REAL_LE_DIV, REAL_LE_01, REAL_INV_NZ, REAL_INV_1OVER]);

val inv_pos' = store_thm
  ("inv_pos'", ``!x. 0 < x /\ x <> PosInf ==> 0 < inv x``,
    RW_TAC std_ss []
 >> `x <> 0` by PROVE_TAC [lt_le]
 >> ASM_SIMP_TAC std_ss [inv_1over]
 >> MATCH_MP_TAC inv_pos >> art []);

(* due to new definition of extreal_inv, `0 <= x` is changed to `0 < x`,
   `x <> 0` is added as an antecedent.
 *)
Theorem inv_pos_eq : (* was: ereal_0_gt_inverse *)
    !x. x <> 0 ==> (0 < inv x <=> x <> PosInf /\ 0 <= x)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> RW_TAC std_ss [] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      CCONTR_TAC \\
      fs [extreal_inv_def, lt_refl, GSYM extreal_of_num_def],
      (* goal 2 (of 3) *)
      Know `x <> PosInf /\ x <> NegInf`
      >- (CONJ_TAC \\
          CCONTR_TAC >> fs [extreal_inv_def, lt_refl, GSYM extreal_of_num_def]) \\
      STRIP_TAC \\
     `?r. x = Normal r` by METIS_TAC [extreal_cases] \\
     `Normal r <> 0` by METIS_TAC [extreal_of_num_def] \\
      fs [real_normal, extreal_of_num_def, extreal_le_eq, extreal_lt_eq,
          extreal_inv_def, REAL_LT_INV_EQ] \\
      MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC inv_pos' >> art [] \\
      METIS_TAC [le_lt] ]
QED

val rinv_uniq = store_thm
  ("rinv_uniq", ``!x y. (x * y = 1) ==> (y = inv x)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_inv_def, extreal_mul_def, extreal_of_num_def]
 >> Know `r <> 0`
 >- (CCONTR_TAC >> fs [])
 >> IMP_RES_TAC REAL_RINV_UNIQ >> POP_ORW
 >> METIS_TAC [extreal_inv_def]);

val linv_uniq = store_thm
  ("linv_uniq", ``!x y. (x * y = 1) ==> (x = inv y)``,
    RW_TAC std_ss [rinv_uniq, mul_comm]);

val le_rdiv = store_thm
  ("le_rdiv", ``!x y z. 0 < x ==> (y * Normal x <= z <=> y <= z / Normal x)``,
    STRIP_TAC >> rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, extreal_div_def, extreal_inv_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_REFL,
                   REAL_INV_EQ_0, REAL_INV_POS, REAL_LT_IMP_NE]
 >> METIS_TAC [REAL_NEG_NZ, REAL_LE_RDIV_EQ, real_div]);

val le_ldiv = store_thm
  ("le_ldiv", ``!x y z. 0 < x ==> (y <= z * Normal x <=> y / Normal x <= z)``,
    STRIP_TAC >> rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, extreal_div_def, extreal_inv_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_REFL,
                   REAL_INV_EQ_0, REAL_INV_POS, REAL_LT_IMP_NE]
 >> METIS_TAC [REAL_NEG_NZ, REAL_LE_LDIV_EQ, real_div]);

val lt_rdiv = store_thm
  ("lt_rdiv", ``!x y z. 0 < z ==> (x < y / Normal z <=> x * Normal z < y)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [REAL_INV_EQ_0, REAL_INV_POS, extreal_lt_eq, REAL_LT_RDIV_EQ, GSYM real_div,
                   REAL_LT_REFL, lt_refl, lt_infty, le_infty, extreal_div_def, extreal_inv_def,
                   extreal_div_eq, extreal_mul_def, REAL_LT_IMP_NE]);

Theorem lt_div : (* cf. REAL_LT_DIV *)
    !y z. 0 < y /\ 0 < z ==> 0 < y / Normal z
Proof
    rpt STRIP_TAC
 >> MP_TAC (REWRITE_RULE [mul_lzero] (Q.SPECL [`0`, `y`, `z`] lt_rdiv))
 >> RW_TAC std_ss []
QED

Theorem le_div : (* cf. REAL_LE_DIV *)
    !y z. 0 <= y /\ 0 < z ==> 0 <= y / Normal z
Proof
    rpt STRIP_TAC
 >> MP_TAC (GSYM (Q.SPECL [`z`, `0`, `y`] le_rdiv))
 >> RW_TAC std_ss [mul_lzero]
QED

val lt_ldiv = store_thm
  ("lt_ldiv", ``!x y z. 0 < z ==> (x / Normal z < y <=> x < y * Normal z)``,
    NTAC 2 Cases
 >> RW_TAC std_ss [REAL_INV_EQ_0, REAL_INV_POS, extreal_lt_eq, REAL_LT_LDIV_EQ, GSYM real_div,
                   REAL_LT_REFL, lt_refl, lt_infty, le_infty, extreal_div_def, extreal_inv_def,
                   extreal_div_eq, extreal_mul_def, REAL_LT_IMP_NE]);

val lt_rdiv_neg = store_thm
  ("lt_rdiv_neg", ``!x y z. z < 0 ==> (y / Normal z < x <=> x * Normal z < y)``,
    NTAC 2 Cases >> RW_TAC std_ss []
 >> RW_TAC std_ss [REAL_INV_POS, REAL_LE_LT, GSYM real_lte, REAL_INV_EQ_0, REAL_INV_POS,
                   extreal_lt_eq, REAL_LT_RDIV_EQ_NEG, GSYM real_div, REAL_LT_REFL, lt_refl,
                   lt_infty, le_infty, extreal_div_def, extreal_inv_def, extreal_div_eq,
                   extreal_mul_def, REAL_LT_REFL, REAL_LT_IMP_NE]
 >> METIS_TAC [REAL_LT_ANTISYM, real_lte, REAL_NEG_NZ, REAL_LT_INV_EQ, lt_refl, lt_infty]);

(* `x, y` must be reals, `z <> 0` *)
val div_add = store_thm
  ("div_add",
  ``!x y z. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf /\ z <> 0 ==>
           (x / z + y / z = (x + y) / z)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_div_def, extreal_mul_def, extreal_inv_def,
                    extreal_of_num_def]
 >> RW_TAC real_ss [extreal_add_def, REAL_RDISTRIB]);

(* `z` must be non-zero normal reals, `x + y` must be defined *)
val div_add2 = store_thm
  ("div_add2",
  ``!x y z. ((x <> PosInf /\ y <> PosInf) \/ (x <> NegInf /\ y <> NegInf)) /\
             z <> 0 /\ z <> PosInf /\ z <> NegInf ==>
            (x / z + y / z = (x + y) / z)``,
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_div_def, extreal_mul_def, extreal_inv_def,
                    extreal_of_num_def]
 >> RW_TAC real_ss [extreal_add_def, REAL_RDISTRIB]);

(* NOTE: `0 <= x` is changed to `0 < x` otherwise `inv x` is not defined *)
val le_inv = store_thm
  ("le_inv", ``!x. 0 < x ==> 0 <= inv x``,
    Cases >> RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_le_def,
                             le_infty, lt_refl, extreal_lt_eq, REAL_LT_IMP_NE]
 >> MATCH_MP_TAC REAL_LE_INV
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []);

val div_infty = store_thm
  ("div_infty", ``!x. x <> PosInf /\ x <> NegInf ==> (x / PosInf = 0) /\ (x / NegInf = 0)``,
    Cases
 >> RW_TAC std_ss [extreal_div_def, extreal_inv_def, GSYM extreal_of_num_def, mul_rzero]);

val infty_div = store_thm
  ("infty_div",
  ``!r. 0 < r ==> (PosInf / Normal r = PosInf) /\ (NegInf / Normal r = NegInf)``,
    GEN_TAC >> DISCH_TAC
 >> IMP_RES_TAC REAL_LT_IMP_NE
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, GSYM extreal_of_num_def,
                    extreal_mul_def, mul_rzero, REAL_INV_POS, REAL_INV_EQ_0]);

val zero_div = store_thm (* cf. REAL_DIV_LZERO *)
  ("zero_div", ``!x :extreal. x <> 0 ==> (0 / x = 0)``,
    Cases
 >> RW_TAC std_ss [extreal_div_def, mul_lzero, extreal_of_num_def]);

val ldiv_eq = store_thm (* REAL_EQ_LDIV_EQ *)
  ("ldiv_eq", ``!x y z. 0 < z /\ z < PosInf ==> ((x / z = y) <=> (x = y * z))``,
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_infty, extreal_of_num_def, extreal_lt_eq, extreal_not_infty,
                   extreal_mul_def, infty_div, REAL_LT_REFL, extreal_div_def,
                   extreal_inv_def, extreal_mul_def, GSYM real_div, REAL_LT_IMP_NE]
 >> MATCH_MP_TAC REAL_EQ_LDIV_EQ >> art []);

val rdiv_eq = store_thm (* REAL_EQ_RDIV_EQ *)
  ("rdiv_eq", ``!x y z. 0 < z /\ z < PosInf ==> ((x = y / z) <=> (x * z = y))``,
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_infty, extreal_of_num_def, extreal_lt_eq, extreal_not_infty,
                   extreal_mul_def, infty_div, REAL_LT_REFL, extreal_div_def,
                   extreal_inv_def, extreal_mul_def, GSYM real_div, REAL_POS_NZ]
 >> MATCH_MP_TAC REAL_EQ_RDIV_EQ >> art []);

val div_eq_mul_linv = store_thm
  ("div_eq_mul_linv",
  ``!x y. x <> PosInf /\ x <> NegInf /\ 0 < y ==> (x / y = (inv y) * x)``,
    RW_TAC std_ss []
 >> Cases_on `y = PosInf`
 >- ASM_SIMP_TAC std_ss [div_infty, extreal_inv_def, GSYM extreal_of_num_def, mul_lzero]
 >> Know `0 < y /\ y < PosInf` >- art [GSYM lt_infty]
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP ldiv_eq))
 >> REWRITE_TAC [GSYM mul_assoc, Once mul_comm]
 >> `y * inv y = 1` by PROVE_TAC [mul_comm, mul_linv_pos]
 >> ASM_REWRITE_TAC [mul_rone]);

Theorem inv_lt_antimono: (* new *)
  !x y :extreal. 0 < x /\ 0 < y ==> (inv x < inv y <=> y < x)
Proof
    rpt strip_tac
 >> `x <> 0 /\ y <> 0` by PROVE_TAC [lt_le]
 >> Cases_on `x`
 >> fs [lt_infty, extreal_inv_def, extreal_of_num_def, lt_refl, extreal_11,
        extreal_lt_eq]
 >- (fs [GSYM extreal_of_num_def] \\
     reverse EQ_TAC >> DISCH_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC inv_pos' >> art [lt_infty],
       (* goal 2 (of 2) *)
       REWRITE_TAC [GSYM lt_infty] \\
       CCONTR_TAC >> fs [extreal_inv_def] \\
       fs [GSYM extreal_of_num_def, lt_refl] ])
 >> Cases_on `y`
 >> fs [lt_infty, extreal_inv_def, extreal_of_num_def, lt_refl, extreal_11,
        extreal_lt_eq]
 >> ASM_REWRITE_TAC [real_lt, REAL_LE_LT]
QED

Theorem inv_inj: (* new *)
  !x y :extreal. 0 < x /\ 0 < y ==> ((inv x = inv y) <=> (x = y))
Proof
    rpt STRIP_TAC
 >> `x <> 0 /\ y <> 0` by PROVE_TAC [lt_le]
 >> Cases_on `x` >> Cases_on `y`
 >> fs [extreal_inv_def, extreal_of_num_def, extreal_11, extreal_not_infty,
        lt_infty, extreal_lt_eq]
QED

val inv_le_antimono = store_thm
  ("inv_le_antimono", ``!x y :extreal. 0 < x /\ 0 < y ==> (inv x <= inv y <=> y <= x)``,
    rpt STRIP_TAC
 >> REWRITE_TAC [le_lt]
 >> EQ_TAC >> STRIP_TAC
 >| [ DISJ1_TAC >> PROVE_TAC [inv_lt_antimono],
      DISJ2_TAC >> PROVE_TAC [inv_inj],
      DISJ1_TAC >> PROVE_TAC [inv_lt_antimono],
      DISJ2_TAC >> PROVE_TAC [inv_inj] ]);

Theorem inv_not_infty :
    !x :extreal. x <> 0 ==> inv x <> PosInf /\ inv x <> NegInf
Proof
    GEN_TAC
 >> Cases_on `x`
 >> RW_TAC std_ss [extreal_inv_def, extreal_not_infty,
                   extreal_of_num_def, extreal_11]
QED

Theorem div_not_infty :
    !x y:extreal. y <> 0 ==> Normal x / y <> PosInf /\ Normal x / y <> NegInf
Proof
    rpt GEN_TAC
 >> Cases_on `y`
 >> RW_TAC std_ss [extreal_div_def, extreal_inv_def, extreal_not_infty,
                   extreal_of_num_def, extreal_11]
 >> METIS_TAC [mul_not_infty2, extreal_not_infty]
QED

Theorem div_mul_refl :
    !(x :extreal) r. r <> 0 ==> x = x / (Normal r) * (Normal r)
Proof
    RW_TAC std_ss [extreal_div_def, extreal_inv_def, GSYM mul_assoc, extreal_mul_def]
 >> RW_TAC real_ss [REAL_MUL_LINV, GSYM extreal_of_num_def, mul_rone]
QED

Theorem mul_div_refl :
    !(x :extreal) r. x <> PosInf /\ x <> NegInf /\ 0 < r ==>
                    (x = x * (Normal r) / (Normal r))
Proof
    rpt STRIP_TAC
 >> Know `x * (Normal r) / (Normal r) = (inv (Normal r)) * (x * (Normal r))`
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    `?a. x = Normal a` by METIS_TAC [extreal_cases] \\
     RW_TAC std_ss [extreal_not_infty, extreal_mul_def, extreal_of_num_def,
                    extreal_lt_eq]) >> Rewr'
 >> ONCE_REWRITE_TAC [mul_comm]
 >> ONCE_REWRITE_TAC [GSYM mul_assoc]
 >> `Normal r * inv (Normal r) = inv (Normal r) * Normal r`
      by PROVE_TAC [mul_comm] >> POP_ORW
 >> Know `inv (Normal r) * Normal r = 1`
 >- (MATCH_MP_TAC mul_linv_pos \\
     RW_TAC std_ss [extreal_of_num_def, extreal_lt_eq, extreal_not_infty])
 >> Rewr' >> REWRITE_TAC [mul_rone]
QED

Theorem ldiv_le_imp :
    !x y (z :extreal). 0 < z /\ z <> PosInf /\ x <= y ==> x / z <= y / z
Proof
    RW_TAC std_ss []
 >> `z <> NegInf` by METIS_TAC [lt_imp_le, pos_not_neginf]
 >> `?r. z = Normal r` by METIS_TAC [extreal_cases]
 >> `0 < r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
 >> `r <> 0` by METIS_TAC [REAL_LT_LE]
 >> Cases_on `x` >> Cases_on `y`
 >> fs [le_infty, extreal_div_eq, infty_div, le_refl, extreal_le_eq]
 >> fs [REAL_LE_LT] >> DISJ1_TAC >> rw [REAL_LT_RDIV]
QED

val extreal_distinct = DB.fetch "extreal" "extreal_distinct";

(* cf. REAL_EQ_MUL_LCANCEL *)
Theorem mul_lcancel :
    !x y (z :extreal). x <> PosInf /\ x <> NegInf ==>
                     ((x * y = x * z) <=> (x = 0) \/ (y = z))
Proof
    rpt STRIP_TAC
 >> `?r. x = Normal r` by METIS_TAC [extreal_cases]
 >> POP_ORW >> KILL_TAC
 >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_mul_def, extreal_not_infty, extreal_of_num_def,
                   extreal_11, extreal_distinct,
                   REAL_MUL_LZERO, REAL_MUL_RZERO]
 >> REWRITE_TAC [REAL_EQ_MUL_LCANCEL]
QED

Theorem inv_mul :
    !x y. x <> 0 /\ y <> 0 ==> (inv (x * y) = inv x * inv y)
Proof
    rpt STRIP_TAC
 >> Cases_on `x` >> Cases_on `y`
 >> FULL_SIMP_TAC real_ss [extreal_mul_def, extreal_inv_def, extreal_not_infty,
                           extreal_of_num_def, extreal_11]
 >> TRY (Cases_on `0 < r` >> rw [extreal_inv_def])
 >> `r * r' <> 0` by METIS_TAC [REAL_ENTIRE]
 >> ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_11]
 >> MATCH_MP_TAC REAL_INV_MUL >> art []
QED

Theorem abs_div :
    !x y :extreal. x <> PosInf /\ x <> NegInf /\ y <> 0 ==>
                  (abs (x / y) = abs x / abs y)
Proof
    rpt STRIP_TAC
 >> Cases_on `x` >> Cases_on `y`
 >> FULL_SIMP_TAC real_ss [extreal_div_def, extreal_inv_def, extreal_not_infty,
                           extreal_of_num_def, extreal_11, extreal_abs_def,
                           extreal_mul_def]
 >> rename1 `s <> 0`
 >> `abs s <> 0` by PROVE_TAC [ABS_ZERO]
 >> ASM_SIMP_TAC real_ss [extreal_div_eq, ABS_MUL, extreal_11, real_div, ABS_INV]
QED

(***************************)
(*         x pow n         *)
(***************************)

val pow_0 = store_thm
  ("pow_0[simp]", ``!x. x pow 0 = 1``,
  Cases >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, pow]);

val zero_pow = store_thm (* POW_0 *)
  ("zero_pow", ``!n. 0 < n ==> (extreal_pow 0 n = 0)``,
    RW_TAC real_ss [extreal_of_num_def, extreal_pow_def, extreal_11]
 >> Cases_on `n` >- fs [LESS_REFL]
 >> REWRITE_TAC [POW_0]);

val pow_1 = store_thm
  ("pow_1[simp]", ``!x. x pow 1 = x``,
  Cases >> RW_TAC std_ss [extreal_pow_def, POW_1]);

val one_pow = store_thm (* POW_ONE *)
  ("one_pow[simp]", ``!n. extreal_pow 1 n = 1``,
    RW_TAC real_ss [extreal_of_num_def, extreal_pow_def, extreal_11, POW_ONE]);

val pow_2 = store_thm
  ("pow_2", ``!x. x pow 2 = x * x``,
    Cases >> RW_TAC std_ss [extreal_pow_def, extreal_mul_def, POW_2]);

Theorem pow_zero[simp] :
    !n x :extreal. (x pow (SUC n) = 0) <=> (x = 0)
Proof
    STRIP_TAC >> Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, POW_ZERO_EQ]
QED

val pow_zero_imp = store_thm
  ("pow_zero_imp[simp]", ``!n x. (x pow n = 0) ==> (x = 0)``,
    STRIP_TAC >> Cases
 >> RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,REAL_LT_01,REAL_LT_IMP_NE]
 >> METIS_TAC [POW_ZERO]);

val le_pow2 = store_thm
  ("le_pow2", ``!x. 0 <= x pow 2``,
    Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, REAL_LE_POW2]);

val abs_pow2 = store_thm
  ("abs_pow2[simp]", ``!x. (abs x) pow 2 = x pow 2``,
    GEN_TAC
 >> Cases_on `0 <= x` >- fs [GSYM abs_refl]
 >> fs [GSYM extreal_lt_def, abs_neg, pow_2, neg_mul2]);

val pow_pos_le = store_thm
  ("pow_pos_le", ``!x. 0 <= x ==> !n. 0 <= x pow n``,
    Cases >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, POW_POS]
 >> METIS_TAC [le_infty, le_01, extreal_of_num_def]);

val pow_pos_lt = store_thm
  ("pow_pos_lt", ``!x n. 0 < x ==> 0 < x pow n``,
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, extreal_lt_eq,
                   POW_POS_LT, REAL_LT_01, lt_infty, extreal_not_infty]
 >> METIS_TAC [pow, REAL_LT_01]);

val pow_le = store_thm
  ("pow_le", ``!n x y. 0 <= x /\ x <= y ==> x pow n <= y pow n``,
    STRIP_TAC >> NTAC 2 Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, POW_LE,
                   lt_infty, le_infty, extreal_not_infty, REAL_LE_REFL, pow]);

val pow_lt = store_thm
  ("pow_lt", ``!n x y. 0 <= x /\ x < y ==> x pow SUC n < y pow SUC n``,
    STRIP_TAC >> NTAC 2 Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, REAL_POW_LT2,
                   lt_infty, le_infty, extreal_not_infty, extreal_lt_eq]);

val pow_lt2 = store_thm
  ("pow_lt2", ``!n x y. n <> 0 /\ 0 <= x /\ x < y ==> x pow n < y pow n``,
    STRIP_TAC >> NTAC 2 Cases
  >> RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,REAL_POW_LT2,
                    lt_infty,le_infty,extreal_not_infty,extreal_lt_eq]);

Theorem pow_le_full :
    !n x y :extreal. n <> 0 /\ 0 <= x /\ 0 <= y ==>
                    (x <= y <=> x pow n <= y pow n)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> DISCH_TAC
 >- (MATCH_MP_TAC pow_le >> art [])
 >> SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM extreal_lt_def]))
 >> `y pow n < x pow n` by PROVE_TAC [pow_lt2]
 >> METIS_TAC [let_antisym]
QED

val pow_le_mono = store_thm
  ("pow_le_mono", ``!x n m. 1 <= x /\ n <= m ==> x pow n <= x pow m``,
  Cases
  >> RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,extreal_le_def,
                    lt_infty,le_infty,extreal_not_infty,REAL_LE_REFL]
  >> Cases_on `n = m` >- RW_TAC std_ss [REAL_LE_REFL]
  >> `n < m` by METIS_TAC [LESS_OR_EQ]
  >> `?p. m = p + n` by METIS_TAC [LESS_ADD]
  >> FULL_SIMP_TAC std_ss []
  >> NTAC 3 (POP_ASSUM (K ALL_TAC))
  >> Induct_on `p` >- RW_TAC real_ss [REAL_LE_REFL]
  >> RW_TAC real_ss [GSYM ADD_SUC,pow]
  >> `0 <= r` by METIS_TAC [REAL_LE_01,REAL_LE_TRANS]
  >> `0 <= r pow n` by METIS_TAC [POW_POS]
  >> ONCE_REWRITE_TAC [ADD_COMM]
  >> (MP_TAC o Q.SPECL [`1:real`,`r`,`r pow n`,`r pow (p + n)`]) REAL_LE_MUL2
  >> RW_TAC real_ss []);

val pow_pos_even = store_thm
  ("pow_pos_even", ``!x. x < 0 ==> ((0 < x pow n) <=> (EVEN n))``,
    Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_not_infty,
                   le_infty, lt_infty, extreal_lt_eq, REAL_LT_01, POW_POS_EVEN]);

val pow_neg_odd = store_thm
  ("pow_neg_odd", ``!x. x < 0 ==> ((x pow n < 0) <=> (ODD n))``,
    Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_not_infty,
                   le_infty, lt_infty, extreal_lt_eq, extreal_le_def,
                   REAL_LT_01, EVEN_ODD, extreal_lt_def, extreal_le_def,
                   REAL_LE_01, POW_NEG_ODD, GSYM real_lt]);

(* antecedents added due to new definition of `extreal_add` *)
val add_pow2 = store_thm
  ("add_pow2",
  ``!x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
          ((x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y)``,
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_pow_def, extreal_mul_def, extreal_add_def,
                    extreal_of_num_def, pow_2]
 >> RW_TAC real_ss [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB, REAL_ADD_ASSOC, POW_2,
                    GSYM REAL_DOUBLE]
 >> REAL_ARITH_TAC);

val REAL_MUL_POS_LT = prove ((* from intergrationTheory *)
 ``!x y:real. &0 < x * y <=> &0 < x /\ &0 < y \/ x < &0 /\ y < &0``,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC(SPEC ``x:real`` REAL_LT_NEGTOTAL) THEN
  STRIP_ASSUME_TAC(SPEC ``y:real`` REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL] THEN
  ASSUM_LIST(MP_TAC o MATCH_MP REAL_LT_MUL o end_itlist CONJ) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);

Theorem add_pow2_pos : (* was: add_pow02 *)
    !x y. 0 < x /\ x <> PosInf /\ 0 <= y ==>
         ((x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y)
Proof
  RW_TAC std_ss [] THEN
  `x <> NegInf` by METIS_TAC [lt_trans, lt_infty, num_not_infty] THEN
  `y <> NegInf` by METIS_TAC [lte_trans, lt_infty, num_not_infty] THEN
  ASM_CASES_TAC ``y = PosInf`` THENL [ALL_TAC, METIS_TAC [add_pow2]] THEN
  ASM_SIMP_TAC std_ss [] THEN
  `x = Normal (real x)` by METIS_TAC [normal_real] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  SIMP_TAC std_ss [extreal_add_def, extreal_mul_def, extreal_of_num_def] THEN
  Q_TAC SUFF_TAC `PosInf pow 2 = PosInf` THENL
  [DISCH_TAC, REWRITE_TAC [pow_2, extreal_mul_def]] THEN
  ONCE_ASM_REWRITE_TAC [] THEN REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [extreal_pow_def, extreal_add_def] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
  RW_TAC std_ss [real_normal, REAL_MUL_POS_LT] THEN DISJ1_TAC THEN
  ASM_SIMP_TAC real_ss [GSYM extreal_lt_eq, normal_real, GSYM extreal_of_num_def]
QED

val sub_pow2 = store_thm
  ("sub_pow2",
  ``!x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
        ((x - y) pow 2 = x pow 2 + y pow 2 - 2 * x * y)``,
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_pow_def, extreal_mul_def, extreal_add_def,
                    extreal_of_num_def, pow_2, extreal_ainv_def, extreal_sub_def]
 >> RW_TAC real_ss [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_ADD_ASSOC, POW_2,
                    GSYM REAL_DOUBLE]
 >> REAL_ARITH_TAC);

val pow_add = store_thm
  ("pow_add", ``!x n m. x pow (n + m) = x pow n * x pow m``,
    Cases
 >> RW_TAC real_ss [extreal_pow_def, POW_ADD, extreal_of_num_def,
                    extreal_mul_def, mul_rone, mul_lone]
 >> METIS_TAC [ADD_CLAUSES, EVEN_ADD]);

val pow_mul = store_thm
  ("pow_mul", ``!n x y. (x * y) pow n = x pow n * y pow n``,
    Cases >- RW_TAC std_ss [pow_0,mul_lone]
 >> NTAC 2 Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_pow_def, pow_zero, POW_ZERO_EQ,
                    POW_POS_LT, POW_MUL]
 >> FULL_SIMP_TAC real_ss [GSYM real_lte]
 >> METIS_TAC [POW_POS_EVEN, POW_NEG_ODD, REAL_LT_LE, POW_POS_LT, real_lt,
               POW_ZERO_EQ, EVEN_ODD]);

val pow_minus1 = store_thm
  ("pow_minus1[simp]", ``!n. -1 pow (2 * n) = 1``,
    RW_TAC std_ss [extreal_of_num_def, extreal_ainv_def, extreal_pow_def, POW_MINUS1]);

val pow_not_infty = store_thm
  ("pow_not_infty",
  ``!n x. x <> NegInf /\ x <> PosInf ==> x pow n <> NegInf /\ x pow n <> PosInf``,
    Cases
 >> METIS_TAC [extreal_pow_def, extreal_not_infty, extreal_cases]);

Theorem pow_inv : (* cf. REAL_POW_INV *)
    !n y. y <> 0 ==> inv (y pow n) = (inv y) pow n
Proof
    rpt STRIP_TAC
 >> Cases_on `n = 0` >- rw [pow_0, inv_one]
 >> `0 < n` by RW_TAC arith_ss []
 >> `0 pow n = (0 :real)` by (Cases_on `n` >> rw [POW_0])
 >> Cases_on `y` >> RW_TAC std_ss [extreal_pow_def, extreal_inv_def]
 >> `r <> 0` by METIS_TAC [extreal_of_num_def, extreal_11]
 >> `r pow n <> 0` by PROVE_TAC [POW_NZ]
 >> ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_pow_def, extreal_11]
 >> REWRITE_TAC [REAL_POW_INV]
QED

Theorem pow_div : (* cf. REAL_POW_DIV *)
    !n x y. x <> PosInf /\ x <> NegInf /\ 0 < y ==>
           ((x / y) pow n = x pow n / y pow n)
Proof
    rpt STRIP_TAC
 >> `x pow n <> PosInf /\ x pow n <> NegInf` by METIS_TAC [pow_not_infty]
 >> `0 < y pow n` by METIS_TAC [pow_pos_lt]
 >> ASM_SIMP_TAC std_ss [div_eq_mul_linv, pow_mul]
 >> Suff `inv (y pow n) = (inv y) pow n` >- RW_TAC std_ss []
 >> MATCH_MP_TAC pow_inv
 >> FULL_SIMP_TAC std_ss [lt_le]
QED

val abs_le_square_plus1 = store_thm
  ("abs_le_square_plus1", ``!(x :extreal). abs x <= x pow 2 + 1``,
    GEN_TAC
 >> Cases_on `0 <= x`
 >- (fs [GSYM abs_refl] \\
     Cases_on `1 <= x`
     >- (MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `x pow 2 + 0` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC le_add2 >> REWRITE_TAC [le_refl, le_01]) \\
         REWRITE_TAC [add_rzero, pow_2] \\
        `x = 1 * x` by PROVE_TAC [mul_lone] \\
         POP_ASSUM ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
         MATCH_MP_TAC le_rmul_imp >> art [] \\
         MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `1` >> art [le_01]) \\
    fs [GSYM extreal_lt_def] \\
    Know `x <= x pow 2 + 1 <=> x - 1 <= x pow 2`
    >- (MATCH_MP_TAC EQ_SYM \\
        MATCH_MP_TAC sub_le_eq >> REWRITE_TAC [extreal_of_num_def, extreal_not_infty]) \\
    Rewr' \\
   `x - 1 < 0` by PROVE_TAC [sub_lt_zero] \\
   `0 <= x pow 2` by PROVE_TAC [le_pow2] \\
    MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `0` >> art [] \\
    IMP_RES_TAC lt_imp_le)
 >> fs [GSYM extreal_lt_def]
 >> `abs x = -x` by PROVE_TAC [abs_neg] >> POP_ORW
 >> Cases_on `-1 < x`
 >- (`-x < 1` by PROVE_TAC [neg_neg, GSYM lt_neg] \\
     Know `-x <= x pow 2 + 1 <=> -x - 1 <= x pow 2`
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC sub_le_eq >> REWRITE_TAC [extreal_of_num_def, extreal_not_infty]) \\
     Rewr' \\
    `-x - 1 < 0` by PROVE_TAC [sub_lt_zero] \\
    `0 <= x pow 2` by PROVE_TAC [le_pow2] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `0` >> art [] \\
     IMP_RES_TAC lt_imp_le)
 >> fs [extreal_lt_def]
 >> `1 <= -x` by PROVE_TAC [le_neg, neg_neg]
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `x pow 2 + 0`
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC le_add2 >> REWRITE_TAC [le_refl, le_01])
 >> REWRITE_TAC [add_rzero]
 >> `x pow 2 = -x * -x` by REWRITE_TAC [pow_2, neg_mul2] >> POP_ORW
 >> `-x = 1 * -x` by PROVE_TAC [mul_lone]
 >> POP_ASSUM ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap)
 >> MATCH_MP_TAC le_rmul_imp >> art []
 >> MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `1` >> art [le_01]);

val abs_pow_le_mono = store_thm
  ("abs_pow_le_mono", ``!x n m. n <= m ==> (abs x) pow n <= 1 + (abs x) pow m``,
    rpt STRIP_TAC
 >> Cases_on `1 <= x`
 >- (MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `0 + (abs x) pow m` \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC le_add2 >> REWRITE_TAC [le_01, le_refl]) \\
     REWRITE_TAC [add_lzero] \\
     MATCH_MP_TAC pow_le_mono >> art [] \\
     Suff `abs x = x` >- RW_TAC std_ss [] \\
     REWRITE_TAC [abs_refl] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `1` >> art [le_01])
 >> fs [GSYM extreal_lt_def]
 >> Cases_on `x <= -1`
 >- (MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `0 + (abs x) pow m` \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC le_add2 >> REWRITE_TAC [le_01, le_refl]) \\
     REWRITE_TAC [add_lzero] \\
     MATCH_MP_TAC pow_le_mono >> art [] \\
     Suff `abs x = -x` >- (Rewr' >> METIS_TAC [le_neg, neg_neg]) \\
     MATCH_MP_TAC abs_neg \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `-1` >> art [lt_10])
 >> fs [GSYM extreal_lt_def]
 >> MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `1 + 0`
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC le_add2 >> art [le_refl] \\
     MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos])
 >> REWRITE_TAC [add_rzero, Once (GSYM (Q.SPEC `n` one_pow))]
 >> MATCH_MP_TAC pow_le
 >> REWRITE_TAC [abs_pos, abs_bounds]
 >> CONJ_TAC >> MATCH_MP_TAC lt_imp_le >> art []);

(* |- !x y. x <= y <=> 0 <= y - x *)
val REAL_LE_RSUB_GE0 = save_thm
  ("REAL_LE_RSUB_GE0",
    Q.GENL [`x`, `y`] (REWRITE_RULE [GSYM real_sub, REAL_SUB_RNEG, REAL_ADD_LID]
                                    (Q.SPECL [`0`, `-x`, `y`] REAL_LE_SUB_RADD)));

Theorem ABS_LE_HALF_POW2:
  !x y :real. abs (x * y) <= 1/2 * (x pow 2 + y pow 2)
Proof
    rpt GEN_TAC
 >> Cases_on `0 <= x * y`
 >- (ASM_SIMP_TAC real_ss [abs] \\
     Know `x * y = (1 / 2) * 2 * x * y`
     >- (Suff `1 / 2 * 2 = 1r`
         >- (Rewr' >> REWRITE_TAC [GSYM REAL_MUL_ASSOC, REAL_MUL_LID]) \\
         MATCH_MP_TAC REAL_DIV_RMUL >> SIMP_TAC real_ss []) >> Rewr' \\
     REWRITE_TAC [GSYM REAL_MUL_ASSOC] \\
     MATCH_MP_TAC REAL_LE_MUL2 >> SIMP_TAC real_ss [REAL_LE_REFL] \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LT_LE_MUL >> ASM_SIMP_TAC real_ss []) \\
     ONCE_REWRITE_TAC [REAL_LE_RSUB_GE0] \\
     Suff `x pow 2 + y pow 2 - 2 * (x * y) = (x - y) pow 2`
     >- (Rewr' >> REWRITE_TAC [REAL_LE_POW2]) \\
     SIMP_TAC real_ss [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB,
                       REAL_ADD_RDISTRIB, REAL_ADD_ASSOC, POW_2,
                       GSYM REAL_DOUBLE] \\
     REAL_ARITH_TAC)
 >> ASM_SIMP_TAC real_ss [abs]
 >> fs [GSYM real_lt]
 >> REWRITE_TAC [Once REAL_LE_RSUB_GE0, REAL_SUB_RNEG, REAL_MUL_RNEG]
 >> Suff `x pow 2 + y pow 2 + 2 * (x * y) = (x + y) pow 2`
 >- (Rewr' >> REWRITE_TAC [REAL_LE_POW2])
 >> SIMP_TAC real_ss [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB,
                      REAL_ADD_RDISTRIB, REAL_ADD_ASSOC, POW_2,
                      GSYM REAL_DOUBLE]
 >> REAL_ARITH_TAC
QED

(* this result is needed for proving Cauchy-Schwarz inequality *)
val abs_le_half_pow2 = store_thm
  ("abs_le_half_pow2", ``!x y :extreal. abs (x * y) <= Normal (1 / 2) * (x pow 2 + y pow 2)``,
    NTAC 2 Cases
 >> ASM_SIMP_TAC real_ss [extreal_abs_def, extreal_mul_def, pow_2, extreal_add_def,
                          le_refl, le_infty, extreal_le_eq]
 >> REWRITE_TAC [GSYM POW_2, ABS_LE_HALF_POW2]);

(***************************)
(*         SQRT            *)
(***************************)

val sqrt_pos_le = store_thm
  ("sqrt_pos_le", ``!x. 0 <= x ==> 0 <= sqrt x``,
    Cases
 >> RW_TAC std_ss [extreal_sqrt_def, extreal_of_num_def, extreal_le_def, SQRT_POS_LE]);

val sqrt_pos_lt = store_thm
  ("sqrt_pos_lt", ``!x. 0 < x ==> 0 < sqrt x``,
    Cases
 >> RW_TAC std_ss [extreal_sqrt_def, extreal_of_num_def, extreal_le_def,
                   extreal_lt_eq, lt_infty, SQRT_POS_LT]);

val pow2_sqrt = store_thm
  ("pow2_sqrt", ``!x. 0 <= x ==> (sqrt (x pow 2) = x)``,
    Cases
 >> RW_TAC real_ss [extreal_sqrt_def, extreal_pow_def, POW_2_SQRT, extreal_of_num_def,
                    extreal_le_def]);

val sqrt_pow2 = store_thm
  ("sqrt_pow2", ``!x. (sqrt x pow 2 = x) <=> 0 <= x``,
    Cases
 >> RW_TAC real_ss [extreal_sqrt_def, extreal_pow_def, SQRT_POW2,
                    extreal_of_num_def, extreal_le_def]
 >> METIS_TAC [le_pow2,lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans]);

val sqrt_mono_le = store_thm
  ("sqrt_mono_le", ``!x y. 0 <= x /\ x <= y ==> sqrt x <= sqrt y``,
    NTAC 2 Cases
 >> RW_TAC real_ss [SQRT_MONO_LE, extreal_sqrt_def, extreal_pow_def, POW_2_SQRT,
                    extreal_of_num_def, extreal_le_def, le_infty, extreal_not_infty]);

val pow2_le_eq = store_thm
  ("pow2_le_eq", ``!x y. 0 <= x /\ 0 <= y ==> (x <= y <=> x pow 2 <= y pow 2)``,
    rpt STRIP_TAC
 >> EQ_TAC >> DISCH_TAC >- (MATCH_MP_TAC pow_le >> art [])
 >> `0 <= x pow 2` by PROVE_TAC [le_pow2]
 >> `sqrt (x pow 2) <= sqrt (y pow 2)` by PROVE_TAC [sqrt_mono_le]
 >> METIS_TAC [GSYM pow2_sqrt]);

(***************************)
(*         Log             *)
(***************************)

val logr_not_infty = store_thm
  ("logr_not_infty",
  ``!x b. (x <> NegInf /\ x <> PosInf) ==> logr b x <> NegInf /\ logr b x <> PosInf``,
    Cases >> RW_TAC std_ss [extreal_logr_def, extreal_not_infty]);

(***************************)
(*      Exp and powr       *)
(***************************)

Theorem exp_pos :
    !x :extreal. 0 <= exp x
Proof
    GEN_TAC >> Cases_on `x`
 >> RW_TAC real_ss [extreal_exp_def, le_infty, extreal_of_num_def,
                    extreal_le_eq, EXP_POS_LE]
QED

Theorem powr_pos :
    !x a :extreal. 0 <= x powr a
Proof
    RW_TAC std_ss [extreal_powr_def, exp_pos]
QED

Theorem normal_exp :
    !r. exp (Normal r) = Normal (exp r)
Proof
    RW_TAC std_ss [extreal_exp_def]
QED

(* `0 rpow a` is not defined in transcTheory (cf. rpow_def) *)
Theorem normal_powr :
    !r a. 0 < r /\ 0 < a ==> (Normal r) powr (Normal a) = Normal (r powr a)
Proof
    RW_TAC real_ss [extreal_exp_def, extreal_mul_def, extreal_powr_def,
                    extreal_ln_def, rpow_def]
QED

Theorem exp_0[simp] :
    exp 0 = (1 :extreal)
Proof
    rw [extreal_of_num_def, normal_exp, extreal_11, EXP_0]
QED

Theorem powr_0[simp] :
    !x. x powr 0 = (1 :extreal)
Proof
    rw [extreal_powr_def, exp_0]
QED

(* only possible after the new definition of `ln` *)
Theorem zero_rpow :
    !x :extreal. 0 < x ==> 0 powr x = 0
Proof
    RW_TAC std_ss [extreal_of_num_def, extreal_powr_def, extreal_ln_def]
 >> Cases_on `x`
 >- METIS_TAC [lt_infty]
 >- RW_TAC std_ss [extreal_mul_def, extreal_exp_def]
 >> FULL_SIMP_TAC std_ss [extreal_mul_def, extreal_lt_eq]
 >> `r <> 0` by PROVE_TAC [REAL_LT_LE]
 >> ASM_SIMP_TAC std_ss [extreal_exp_def]
QED

(* only possible after the new definition of `ln`, cf. GEN_RPOW *)
Theorem gen_powr :
    !a n. 0 <= a ==> (a pow n = a powr (&n :extreal))
Proof
    rpt STRIP_TAC
 >> Cases_on `n = 0` >- rw []
 >> Cases_on `a`
 >- METIS_TAC [lt_imp_le, le_not_infty]
 >- (`(0 :real) < &n` by RW_TAC real_ss [] \\
     `(0 :extreal) < &n` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
     ASM_SIMP_TAC std_ss [extreal_pow_def, extreal_powr_def, extreal_ln_def,
                          mul_infty, extreal_exp_def])
 >> `(0 :real) < &n` by RW_TAC real_ss []
 >> `(0 :extreal) < &n` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
 >> FULL_SIMP_TAC std_ss [le_lt]
 >- (`?b. &n = Normal (&n)`
       by METIS_TAC [num_not_infty, extreal_cases, extreal_of_num_def] \\
     POP_ORW \\
     FULL_SIMP_TAC std_ss [extreal_pow_def, normal_powr, extreal_lt_eq,
                           extreal_11, extreal_of_num_def] \\
     MATCH_MP_TAC GEN_RPOW >> art [])
 >> Q.PAT_X_ASSUM `0 = Normal r` (ONCE_REWRITE_TAC o wrap o SYM)
 >> ASM_SIMP_TAC std_ss [zero_rpow]
 >> MATCH_MP_TAC zero_pow
 >> RW_TAC arith_ss []
QED

(* an extended version of EXP_LE_X, needed by Borel_Cantelli_lemma2 (direct proof):
val EXP_LE_X_FULL = store_thm
  ("EXP_LE_X_FULL", ``!x :real. &1 + x <= exp x``,
    GEN_TAC
 >> Cases_on `0 <= x` (* existing case *)
 >- (MATCH_MP_TAC EXP_LE_X >> art [])
 >> fs [GSYM real_lt]
 >> Cases_on `x <= -1` (* easy case *)
 >- (MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `0` >> REWRITE_TAC [EXP_POS_LE] \\
    `0r = 1 + -1` by RW_TAC real_ss [] >> POP_ORW >> art [REAL_LE_LADD])
 >> fs [GSYM real_lt]
 >> ONCE_REWRITE_TAC [GSYM REAL_SUB_LE]
 >> Q.ABBREV_TAC `f = \x :real. exp x - (1 + x)`
 >> `exp x - (1 + x) = f x` by METIS_TAC [] >> POP_ORW
 >> Q.ABBREV_TAC `g = \x :real. exp x - 1`
 >> Know `!x. (f diffl (g x)) x` (* diffl *)
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` \\
     Q.UNABBREV_TAC `g` >> BETA_TAC \\
     MATCH_MP_TAC (REWRITE_RULE [REAL_ADD_LID] (DIFF_CONV ``\x :real. exp x - (1 + x)``)) \\
     REWRITE_TAC [ETA_AX, DIFF_EXP]) >> DISCH_TAC
 >> Know `!x :real. x <= 0 ==> g x <= 0`
 >- (Q.UNABBREV_TAC `g` >> RW_TAC std_ss [] \\
     REWRITE_TAC [REAL_LE_SUB_RADD, REAL_ADD_LID] \\
    `1 :real = exp 0` by REWRITE_TAC [EXP_0] >> POP_ORW \\
     art [EXP_MONO_LE]) >> DISCH_TAC
 >> Know `f 0 = 0`
 >- (Q.UNABBREV_TAC `f` >> BETA_TAC \\
     RW_TAC real_ss [EXP_0, REAL_ADD_RID]) >> DISCH_TAC
 >>
    cheat);

val exp_le_x = store_thm
  ("exp_le_x", ``!x :extreal. &1 + x <= exp x``,
    cheat);

val exp_le_x_neg = store_thm
  ("exp_le_x_neg", ``!x :extreal. &1 - x <= exp (-x)``,
    cheat);

 *)

(***************************)
(*         Various         *)
(***************************)

val half_between = store_thm
  ("half_between", ``(0 < 1/2 /\ 1/2 < 1) /\ (0 <= 1/2 /\ 1/2 <= 1)``,
    MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
 >> CONJ_TAC >- PROVE_TAC [lt_imp_le]
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, mul_lone, extreal_lt_def,
                    extreal_le_def, extreal_of_num_def, extreal_not_infty,
                    GSYM real_lt, REAL_INV_1OVER, extreal_mul_def]);

Theorem half_not_infty :
    1/2 <> PosInf /\ 1/2 <> NegInf
Proof
    rw [lt_infty]
 >- (MATCH_MP_TAC lt_trans \\
     Q.EXISTS_TAC `1` >> rw [half_between] \\
     rw [extreal_of_num_def, lt_infty])
 >> MATCH_MP_TAC lt_trans
 >> Q.EXISTS_TAC `0` >> rw [half_between]
 >> rw [extreal_of_num_def, lt_infty]
QED

val thirds_between = store_thm
  ("thirds_between", ``((0 < 1/3 /\ 1/3 < 1) /\ (0 < 2/3 /\ 2/3 < 1)) /\
                       ((0 <= 1/3 /\ 1/3 <= 1) /\ (0 <= 2/3 /\ 2/3 <= 1))``,
    MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
 >> CONJ_TAC >- PROVE_TAC [lt_imp_le]
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, mul_lone, extreal_lt_def,
                    extreal_le_def, extreal_of_num_def, extreal_not_infty,
                    GSYM real_lt, extreal_mul_def, REAL_INV_1OVER]);

val fourths_between = store_thm
  ("fourths_between", ``((0 < 1/4 /\ 1/4 < 1) /\ (0 < 3/4 /\ 3/4 < 1)) /\
                        ((0 <= 1/4 /\ 1/4 <= 1) /\ (0 <= 3/4 /\ 3/4 <= 1))``,
    MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
 >> CONJ_TAC >- PROVE_TAC [lt_imp_le]
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, mul_lone, extreal_lt_def,
                    extreal_le_def, extreal_of_num_def, extreal_not_infty,
                    GSYM real_lt, extreal_mul_def, REAL_INV_1OVER]);

val half_cancel = store_thm
  ("half_cancel", ``2 * (1 / 2) = 1``,
    RW_TAC real_ss [extreal_of_num_def, extreal_mul_def, extreal_div_eq,
                    EVAL ``2 <> 0:real``, REAL_MUL_RINV, real_div]);

val third_cancel = store_thm
  ("third_cancel", ``3 * (1 / 3) = 1``,
    RW_TAC real_ss [extreal_of_num_def, extreal_mul_def, extreal_div_eq,
                    EVAL ``3 <> 0:real``, REAL_MUL_RINV, real_div]);

val fourth_cancel = store_thm
  ("fourth_cancel", ``4 * (1 / 4) = 1``,
    RW_TAC real_ss [extreal_of_num_def, extreal_mul_def, extreal_div_eq,
                    EVAL ``4 <> 0:real``, REAL_MUL_RINV, real_div]);

(* added antecedent ``m <> 0`` *)
val quotient_normal = store_thm
  ("quotient_normal", ``!n m. m <> 0 ==> (&n / &m = Normal (&n / &m))``,
    RW_TAC std_ss [extreal_div_eq, extreal_of_num_def, REAL_OF_NUM_EQ]);

val ext_mono_increasing_def = Define
   `ext_mono_increasing f = (!m n:num. m <= n ==> f m <= f n)`;

val ext_mono_increasing_suc = store_thm
  ("ext_mono_increasing_suc", ``!f. ext_mono_increasing f <=> !n. f n <= f (SUC n)``,
    RW_TAC std_ss [ext_mono_increasing_def]
 >> EQ_TAC >> RW_TAC real_ss []
 >> Know `?d. n = m + d` >- PROVE_TAC [LESS_EQ_EXISTS]
 >> RW_TAC std_ss []
 >> Induct_on `d` >- RW_TAC std_ss [add_rzero, le_refl]
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `m + d`)
 >> METIS_TAC [le_trans, ADD_CLAUSES, LESS_EQ_ADD]);

val ext_mono_decreasing_def = Define
   `ext_mono_decreasing f = (!m n:num. m <= n ==> f n <= f m)`;

val ext_mono_decreasing_suc = store_thm
  ("ext_mono_decreasing_suc", ``!f. ext_mono_decreasing f <=> !n. f (SUC n) <= f n``,
    RW_TAC std_ss [ext_mono_decreasing_def]
 >> EQ_TAC >> RW_TAC real_ss []
 >> Know `?d. n = m + d` >- PROVE_TAC [LESS_EQ_EXISTS]
 >> RW_TAC std_ss []
 >> Induct_on `d` >- RW_TAC std_ss [add_rzero,le_refl]
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n. f (SUC n) <= f n` (MP_TAC o Q.SPEC `m + d`)
 >> METIS_TAC [le_trans, ADD_CLAUSES, LESS_EQ_ADD]);

val _ = overload_on ("mono_increasing", Term `ext_mono_increasing`);
val _ = overload_on ("mono_decreasing", Term `ext_mono_decreasing`);

val EXTREAL_ARCH = store_thm
  ("EXTREAL_ARCH", ``!x. 0 < x ==> !y. y <> PosInf ==> ?n. y < &n * x``,
    Cases
 >| [ (* goal 1 (of 3) *)
      RW_TAC std_ss [lt_infty],
      (* goal 2 (of 3) *)
      RW_TAC std_ss [lt_infty] \\
      Q.EXISTS_TAC `1` >> RW_TAC std_ss [mul_lone, lt_infty],
      (* goal 3 (of 3) *)
      RW_TAC std_ss [lt_infty] \\
      Cases_on `y = NegInf`
      >- (Q.EXISTS_TAC `1` >> RW_TAC std_ss [mul_lone, lt_infty]) \\
     `?z. y = Normal z` by METIS_TAC [extreal_cases, lt_infty] \\
     `0 < r` by METIS_TAC [extreal_lt_eq, extreal_of_num_def] \\
     `?n. z < &n * r` by METIS_TAC [REAL_ARCH] \\
      Q.EXISTS_TAC `n` \\
      RW_TAC real_ss [extreal_lt_eq, REAL_LE_MUL, extreal_of_num_def, extreal_mul_def] ]);

val SIMP_EXTREAL_ARCH = store_thm
  ("SIMP_EXTREAL_ARCH", ``!x. x <> PosInf ==> ?n. x <= &n``,
    Cases
 >> RW_TAC std_ss [le_infty]
 >> `?n. r <= &n` by RW_TAC std_ss [SIMP_REAL_ARCH]
 >> Q.EXISTS_TAC `n`
 >> RW_TAC real_ss [extreal_of_num_def,extreal_le_def]);

val SIMP_EXTREAL_ARCH_NEG = store_thm
  ("SIMP_EXTREAL_ARCH_NEG", ``!x. x <> NegInf ==> ?n. - &n <= x``,
    Cases
 >> RW_TAC std_ss [le_infty]
 >> `?n. - &n <= r` by RW_TAC std_ss [SIMP_REAL_ARCH_NEG]
 >> Q.EXISTS_TAC `n`
 >> RW_TAC real_ss [extreal_of_num_def, extreal_le_eq, extreal_ainv_def]);

val EXTREAL_ARCH_POW = store_thm
  ("EXTREAL_ARCH_POW", ``!x. x <> PosInf ==> ?n. x < (2 pow n)``,
    Cases
 >> RW_TAC std_ss [lt_infty, extreal_lt_eq, REAL_ARCH_POW, extreal_pow_def,
                   extreal_of_num_def]);

val EXTREAL_ARCH_POW_INV = store_thm
  ("EXTREAL_ARCH_POW_INV", ``!e. 0 < e ==> ?n. Normal ((1 / 2) pow n) < e``,
    Cases >- RW_TAC std_ss [lt_infty]
 >- METIS_TAC [lt_infty,extreal_not_infty]
 >> RW_TAC std_ss [extreal_of_num_def,extreal_lt_eq]
 >> MP_TAC (Q.SPEC `1 / 2` SEQ_POWER)
 >> RW_TAC std_ss [abs, REAL_HALF_BETWEEN, REAL_LT_IMP_LE, SEQ]
 >> POP_ASSUM (MP_TAC o Q.SPEC `r`)
 >> RW_TAC std_ss [REAL_SUB_RZERO, REAL_POW_LT,
                   REAL_HALF_BETWEEN,REAL_LT_IMP_LE,GREATER_EQ]
 >> PROVE_TAC [LESS_EQ_REFL]);

val REAL_LE_MUL_EPSILON = store_thm
  ("REAL_LE_MUL_EPSILON",
  ``!x y:real. (!z. 0 < z /\ z < 1 ==> z * x <= y) ==> x <= y``,
    rpt STRIP_TAC
 >> Cases_on `x = 0`
 >- (Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `1/2`)
     >> RW_TAC real_ss [REAL_HALF_BETWEEN])
 >> Cases_on `0 < x`
 >- (MATCH_MP_TAC REAL_LE_EPSILON \\
     RW_TAC std_ss [GSYM REAL_LE_SUB_RADD] \\
     Cases_on `e < x`
     >- (MATCH_MP_TAC REAL_LE_TRANS \\
         Q.EXISTS_TAC `(1 - e/x) * x` \\
         CONJ_TAC
         >- (RW_TAC real_ss [REAL_SUB_RDISTRIB] \\
             METIS_TAC [REAL_DIV_RMUL, REAL_LE_REFL]) \\
         Q.PAT_X_ASSUM `!z. P z` MATCH_MP_TAC \\
         RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_DIV, REAL_LT_SUB_LADD,
                         REAL_LT_1, REAL_LT_IMP_LE]) \\
     FULL_SIMP_TAC std_ss [REAL_NOT_LT] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `0` \\
     RW_TAC real_ss [REAL_LE_SUB_RADD] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `(1 / 2) * x` \\
     RW_TAC real_ss [REAL_LE_MUL, REAL_LT_IMP_LE])
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC `(1/2)*x`
 >> RW_TAC real_ss []
 >> RW_TAC std_ss [Once (GSYM REAL_LE_NEG), GSYM REAL_MUL_RNEG]
 >> Suff `1/2 * ~x <= 1 * ~x` >- RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_LT_TOTAL, REAL_LE_REFL, REAL_HALF_BETWEEN, REAL_LE_RMUL]);

val le_epsilon = store_thm
  ("le_epsilon", ``!x y. (!e. 0 < e /\ e <> PosInf ==> x <= y + e) ==> x <= y``,
    NTAC 2 Cases
 >> RW_TAC std_ss [le_infty]
 >| [ (* goal 1 *)
      Q.EXISTS_TAC `1` \\
      RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def],
      (* goal 2 *)
      Q.EXISTS_TAC `1` \\
      RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def],
      (* goal 3 *)
      Q.EXISTS_TAC `1` \\
      RW_TAC std_ss [lt_01, extreal_of_num_def, extreal_not_infty, extreal_add_def,
                     extreal_le_def],
      (* goal 4 *)
     `!e. 0 < e  ==> Normal r <= Normal r' + Normal e`
         by (RW_TAC std_ss [] \\
             Q.PAT_X_ASSUM `!e. P e` MATCH_MP_TAC \\
             METIS_TAC [extreal_not_infty, extreal_of_num_def, extreal_lt_eq]) \\
     `!e. 0 < e ==> Normal r <= Normal (r' + e)`
         by (RW_TAC real_ss [extreal_le_def, REAL_LT_IMP_LE, REAL_LE_ADD] \\
            `Normal r <= Normal r' + Normal e` by METIS_TAC [REAL_LT_IMP_LE] \\
            `Normal r' + Normal e = Normal (r' + e)`
                  by METIS_TAC [extreal_add_def, REAL_LT_IMP_LE] \\
             FULL_SIMP_TAC std_ss [] \\
             METIS_TAC [REAL_LE_ADD, extreal_le_def, REAL_LT_IMP_LE]) \\
     `!e. 0 < e ==>  r <= r' + e`
       by METIS_TAC [extreal_le_def, REAL_LT_IMP_LE, REAL_LE_ADD, extreal_add_def, REAL_LE_ADD] \\
     `!e. 0 < e ==>  r <= r' + e` by METIS_TAC [extreal_le_def] \\
      METIS_TAC [REAL_LE_EPSILON, extreal_le_def] ]);

val le_mul_epsilon = store_thm
  ("le_mul_epsilon",
  ``!x y:extreal. (!z. 0 <= z /\ z < 1 ==> z * x <= y) ==> x <= y``,
    ASSUME_TAC half_between
 >> `1 / 2 <> 0` by METIS_TAC [lt_imp_ne]
 >> rpt Cases >> RW_TAC std_ss [le_infty]
 >| [ (* goal 1 (of 4) *)
      Q.EXISTS_TAC `1 / 2` \\
      RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases],
      (* goal 2 (of 4) *)
      Q.EXISTS_TAC `1 / 2` \\
      RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases,
                      le_infty, extreal_not_infty],
      (* goal 3 (of 4) *)
      Q.EXISTS_TAC `1 / 2` \\
      RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, extreal_div_eq, extreal_cases,
                      le_infty, extreal_not_infty],
      (* goal 4 (of 4) *)
     `!z. 0 <= z /\ z < 1 <=> ?z1. 0 <= z1 /\ z1 < 1 /\ (z = Normal z1)`
         by (RW_TAC std_ss [] \\
             EQ_TAC
             >- (RW_TAC std_ss [] \\
                 Cases_on `z` >|
                 [ METIS_TAC [extreal_of_num_def, le_infty, extreal_not_infty],
                   METIS_TAC [extreal_of_num_def, lt_infty, extreal_not_infty],
                   METIS_TAC [extreal_le_def, extreal_lt_eq, extreal_of_num_def] ]) \\
             METIS_TAC [extreal_lt_eq, extreal_le_def, extreal_of_num_def]) \\
      RW_TAC std_ss [] \\
     `!z1. 0 <= z1 /\ z1 < 1 ==> Normal (z1) * Normal r <= Normal r'`
         by METIS_TAC [extreal_lt_eq, extreal_le_def, extreal_of_num_def] \\
     `!z1. 0 <= z1 /\ z1 < 1 ==> Normal (z1 * r) <= Normal r'`
         by METIS_TAC [extreal_mul_def] \\
      Suff `r <= r'` >- METIS_TAC [extreal_le_def] \\
      MATCH_MP_TAC REAL_LE_MUL_EPSILON \\
      METIS_TAC [extreal_le_def, REAL_LT_LE] ]);

(***************************************************)
(*   SUM over Finite Set (reworked by Chun Tian)   *)
(***************************************************)

(* Some lemmas about ITSET, (\e acc. f e + acc) and b:extreal *)

val absorption =         #1 (EQ_IMP_RULE (SPEC_ALL ABSORPTION));
val delete_non_element = #1 (EQ_IMP_RULE (SPEC_ALL DELETE_NON_ELEMENT));

local
val tactics =
   GEN_TAC >> DISCH_TAC >> rpt GEN_TAC >> DISCH_TAC
 >> completeInduct_on `CARD s`
 >> POP_ASSUM (ASSUME_TAC o (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]))
 >> GEN_TAC >> SIMP_TAC bool_ss [ITSET_INSERT]
 >> rpt STRIP_TAC
 >> Q.ABBREV_TAC `t = REST (x INSERT s)`
 >> Q.ABBREV_TAC `y = CHOICE (x INSERT s)`
 >> `~(y IN t)` by PROVE_TAC [CHOICE_NOT_IN_REST]
 >> Cases_on `x IN s` >| (* 2 sub-goals here *)
  [ (* goal 1 (of 2) *)
    FULL_SIMP_TAC bool_ss [absorption] \\
    Cases_on `x = y` >| (* 2 sub-goals here *)
    [ (* goal 1.1 (of 2), x = y, no extreal property used *)
      POP_ASSUM SUBST_ALL_TAC \\ (* all `x` disappeared *)
      Suff `t = s DELETE y` >- SRW_TAC [][] \\
     `s = y INSERT t` by PROVE_TAC [NOT_IN_EMPTY, CHOICE_INSERT_REST] \\
      SRW_TAC [][DELETE_INSERT, delete_non_element],
      (* goal 1.2 (of 2), x <> y *)
     `s = y INSERT t` by PROVE_TAC [NOT_IN_EMPTY, CHOICE_INSERT_REST] \\
     `x IN t` by PROVE_TAC [IN_INSERT] \\
      Q.ABBREV_TAC `u = t DELETE x` \\
     `t = x INSERT u` by SRW_TAC [][INSERT_DELETE, Abbr`u`] \\
     `~(x IN u)` by PROVE_TAC [IN_DELETE] \\
     `s = x INSERT (y INSERT u)` by simp[INSERT_COMM] \\
      POP_ASSUM SUBST_ALL_TAC \\ (* all `s` disappeared *)
      FULL_SIMP_TAC bool_ss [FINITE_INSERT, CARD_INSERT, DELETE_INSERT,IN_INSERT] \\
      (* now we start using properties of extreal *)
     `f x + b <> limit /\ f y + b <> limit` by METIS_TAC [add_not_infty] \\
      Q.PAT_X_ASSUM `!s' x' b'. (CARD s' < SUC (SUC (CARD u)) /\ FINITE s') /\ X ==> Y`
        (ASSUME_TAC o (Q.SPEC `u`)) \\
      FULL_SIMP_TAC arith_ss [] \\
     `!z. (z = x) \/ z IN u ==> f z <> limit` by METIS_TAC [] \\
     `!z. (z = y) \/ z IN u ==> f z <> limit` by METIS_TAC [] \\
      rpt STRIP_TAC \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`x`, `f y + b`])) \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`y`, `f x + b`])) \\
      Q.PAT_X_ASSUM `!x' b'. FINITE u /\ X ==> Y` K_TAC \\
      rpt STRIP_TAC >> RES_TAC \\
      ASM_SIMP_TAC std_ss [delete_non_element] \\
      METIS_TAC [add_assoc, add_comm, add_not_infty] ],
    (* goal 2 (of 2), ~(x IN s) *)
    ASM_SIMP_TAC bool_ss [delete_non_element] \\
   `x INSERT s = y INSERT t` by PROVE_TAC [NOT_EMPTY_INSERT, CHOICE_INSERT_REST] \\
    Cases_on `x = y` >| (* 2 sub-goals here *)
    [ (* goal 2.1 (of 2), no extreal property used *)
      POP_ASSUM SUBST_ALL_TAC \\ (* all `x` disappeared *)
      Suff `t = s` THEN1 SRW_TAC [][] \\
      FULL_SIMP_TAC bool_ss [EXTENSION, IN_INSERT] >> PROVE_TAC [],
      (* goal 2.2 (of 2), ~(x = y) *)
     `x IN t /\ y IN s` by PROVE_TAC [IN_INSERT] \\
      Q.ABBREV_TAC `u = s DELETE y` \\
     `~(y IN u)` by PROVE_TAC [IN_DELETE] \\
     `s = y INSERT u` by SRW_TAC [][INSERT_DELETE, Abbr`u`] \\
      POP_ASSUM SUBST_ALL_TAC \\ (* all `s` disappeared *)
      FULL_SIMP_TAC bool_ss [IN_INSERT, FINITE_INSERT, CARD_INSERT,
                             DELETE_INSERT, delete_non_element] \\
     `t = x INSERT u` by
          (FULL_SIMP_TAC bool_ss [EXTENSION, IN_INSERT] THEN PROVE_TAC []) \\
      ASM_REWRITE_TAC [] \\
      (* now we start using properties of extreal *)
     `f x + b <> limit /\ f y + b <> limit` by METIS_TAC [add_not_infty] \\
      Q.PAT_X_ASSUM `!s x' b'. (CARD s < SUC (CARD u) /\ FINITE s') /\ X ==> Y`
        (ASSUME_TAC o (Q.SPEC `u`)) \\
      FULL_SIMP_TAC arith_ss [] \\
     `!z. (z = x) \/ z IN u ==> f z <> limit` by METIS_TAC [] \\
     `!z. (z = y) \/ z IN u ==> f z <> limit` by METIS_TAC [] \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`x`, `f y + b`])) \\
      Q.PAT_ASSUM `!x' b'. FINITE u /\ X ==> Y` (MP_TAC o (Q.SPECL [`y`, `f x + b`])) \\
      Q.PAT_X_ASSUM `!x' b'. FINITE u /\ X ==> Y` K_TAC \\
      rpt STRIP_TAC >> RES_TAC \\
      ASM_SIMP_TAC std_ss [delete_non_element] \\
      METIS_TAC [add_assoc, add_comm, add_not_infty] ] ];

Triviality lem:
  !limit.
     limit = PosInf ==>
     !f s. FINITE s ==>
           !x b. (!z. z IN (x INSERT s) ==> f z <> limit) /\ b <> limit ==>
                 ITSET (\e acc. f e + acc) (x INSERT s) b =
                 ITSET (\e acc. f e + acc) (s DELETE x)
                       ((\e acc. f e + acc) x b)
Proof tactics
QED

val lem' = Q.prove (
   `!limit. (limit = NegInf) ==>
        !f s. FINITE s ==>
              !x b. (!z. z IN (x INSERT s) ==> f z <> limit) /\ b <> limit ==>
                    (ITSET (\e acc. f e + acc) (x INSERT s) b =
                     ITSET (\e acc. f e + acc) (s DELETE x) ((\e acc. f e + acc) x b))`,
    tactics);

in
  (* |- !f s.
         FINITE s ==>
         !x b.
             (!z. z IN x INSERT s ==> f z <> PosInf) /\ b <> PosInf ==>
             (ITSET (\e acc. f e + acc) (x INSERT s) b =
              ITSET (\e acc. f e + acc) (s DELETE x)
                ((\e acc. f e + acc) x b))
   *)
  val lemma1  = REWRITE_RULE [] (Q.SPEC `PosInf` lem);

  (* |- !f s.
         FINITE s ==>
         !x b.
             (!z. z IN x INSERT s ==> f z <> NegInf) /\ b <> NegInf ==>
             (ITSET (\e acc. f e + acc) (x INSERT s) b =
              ITSET (\e acc. f e + acc) (s DELETE x)
                ((\e acc. f e + acc) x b))
   *)
  val lemma1' = REWRITE_RULE [] (Q.SPEC `NegInf` lem');
end;

(* lemma2 is independent of lemma1 *)
local val tactics =
   (rpt GEN_TAC >> STRIP_TAC
 >> Induct_on `CARD s`
 >- METIS_TAC [CARD_EQ_0, ITSET_EMPTY]
 >> POP_ASSUM (ASSUME_TAC o
               (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]))
 >> RW_TAC std_ss []
 >> `0 < CARD s` by METIS_TAC [prim_recTheory.LESS_0]
 >> `CARD s <> 0` by RW_TAC real_ss [REAL_LT_NZ]
 >> `s <> {}` by METIS_TAC [CARD_EQ_0]
 >> `?x t. (s = x INSERT t) /\ x NOTIN t` by METIS_TAC [SET_CASES]
 >> FULL_SIMP_TAC std_ss [ITSET_INSERT, FINITE_INSERT]
 >> RW_TAC std_ss [REST_DEF]
 >> Q.ABBREV_TAC `y = CHOICE (x INSERT t)`
 >> Q.ABBREV_TAC `u = x INSERT t`
 >> `y IN u` by PROVE_TAC [CHOICE_DEF]
 >> `CARD (u DELETE y) = v` by METIS_TAC [CARD_DELETE, FINITE_INSERT, SUC_SUB1]
 >> METIS_TAC [add_not_infty, FINITE_INSERT, FINITE_DELETE, IN_DELETE])
in
  val lemma2  = Q.prove (
     `!f s. (!x. x IN s ==> f x <> PosInf) /\ FINITE s ==>
            !b. b <> PosInf ==> ITSET (\e acc. f e + acc) s b <> PosInf`, tactics);

  val lemma2' = Q.prove (
     `!f s. (!x. x IN s ==> f x <> NegInf) /\ FINITE s ==>
            !b. b <> NegInf ==> ITSET (\e acc. f e + acc) s b <> NegInf`, tactics);
end;

(** lemma3 depends on both lemma1 and lemma2 *)
val lemma3 = Q.prove (
   `!b f x s. (!y. y IN (x INSERT s) ==> f y <> PosInf) /\ b <> PosInf /\ FINITE s ==>
              (ITSET (\e acc. f e + acc) (x INSERT s) b =
               (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))`,
  (* proof *)
    Suff `!f s. FINITE s ==>
                !x b. (!y. y IN (x INSERT s) ==> f y <> PosInf) /\ b <> PosInf ==>
                      (ITSET (\e acc. f e + acc) (x INSERT s) b =
                       (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> IMP_RES_TAC lemma1 >> ASM_REWRITE_TAC []
 >> Suff `!s. FINITE s ==>
              !x b. (!y. y IN (x INSERT s) ==> f y <> PosInf) /\ b <> PosInf ==>
                   (ITSET (\e acc. f e + acc) s (f x + b) =
                    f x + (ITSET (\e acc. f e + acc) s b))`
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC `t = s DELETE x` \\
     `FINITE t` by METIS_TAC [FINITE_DELETE] \\
     BETA_TAC \\
     Q.PAT_X_ASSUM `!s. FINITE s ==> X` (MP_TAC o Q.SPEC `t`) >> RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o SPEC_ALL) >> RW_TAC std_ss [] \\
     Suff `!y. y IN (x INSERT t) ==> f y <> PosInf` >- PROVE_TAC [] \\
     GEN_TAC >> STRIP_TAC \\
     Q.UNABBREV_TAC `t` \\
     Cases_on `y = x` >- (POP_ASSUM SUBST_ALL_TAC >> PROVE_TAC [IN_INSERT]) \\
     FULL_SIMP_TAC std_ss [IN_INSERT] \\
     PROVE_TAC [DELETE_SUBSET, SUBSET_DEF])
 >> KILL_TAC (* remove all assumptions *)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- SIMP_TAC bool_ss [ITSET_THM, FINITE_EMPTY]
 >> rpt STRIP_TAC
 >> `f x + b <> PosInf` by PROVE_TAC [IN_INSERT, add_not_infty]
 >> `!z. z IN (e INSERT s) ==> f z <> PosInf` by PROVE_TAC [IN_INSERT]
 >> `!x. x IN s ==> f x <> PosInf` by PROVE_TAC [IN_INSERT]
 >> `!y. y IN (x INSERT s) ==> f y <> PosInf` by PROVE_TAC [IN_INSERT, INSERT_COMM]
 >> ASM_SIMP_TAC bool_ss [lemma1, delete_non_element]
 >> `ITSET (\e acc. f e + acc) s b <> PosInf` by METIS_TAC [lemma2]
 >> Q.ABBREV_TAC `t = ITSET (\e acc. f e + acc) s b`
 >> Q.PAT_X_ASSUM `!x b. b <> PosInf => X` K_TAC
 >> METIS_TAC [add_assoc, add_comm, IN_INSERT]);

(** lemma3' depends on lemma1' and lemma2' (proof is the same as lemma3) *)
val lemma3' = Q.prove (
   `!b f x s. (!y. y IN (x INSERT s) ==> f y <> NegInf) /\ b <> NegInf /\ FINITE s ==>
              (ITSET (\e acc. f e + acc) (x INSERT s) b =
               (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))`,
 (* proof *)
    Suff `!f s. FINITE s ==>
                !x b. (!y. y IN (x INSERT s) ==> f y <> NegInf) /\ b <> NegInf ==>
                      (ITSET (\e acc. f e + acc) (x INSERT s) b =
                       (\e acc. f e + acc) x (ITSET (\e acc. f e + acc) (s DELETE x) b))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> IMP_RES_TAC lemma1' >> ASM_REWRITE_TAC []
 >> Suff `!s. FINITE s ==>
              !x b. (!y. y IN (x INSERT s) ==> f y <> NegInf) /\ b <> NegInf ==>
                   (ITSET (\e acc. f e + acc) s (f x + b) =
                    f x + (ITSET (\e acc. f e + acc) s b))`
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC `t = s DELETE x` \\
     `FINITE t` by METIS_TAC [FINITE_DELETE] \\
     BETA_TAC \\
     Q.PAT_X_ASSUM `!s. FINITE s ==> X` (MP_TAC o Q.SPEC `t`) >> RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o SPEC_ALL) >> RW_TAC std_ss [] \\
     Suff `!y. y IN (x INSERT t) ==> f y <> NegInf` >- PROVE_TAC [] \\
     GEN_TAC >> STRIP_TAC \\
     Q.UNABBREV_TAC `t` \\
     Cases_on `y = x` >- (POP_ASSUM SUBST_ALL_TAC >> PROVE_TAC [IN_INSERT]) \\
     FULL_SIMP_TAC std_ss [IN_INSERT] \\
     PROVE_TAC [DELETE_SUBSET, SUBSET_DEF])
 >> KILL_TAC (* remove all assumptions *)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- SIMP_TAC bool_ss [ITSET_THM, FINITE_EMPTY]
 >> rpt STRIP_TAC
 >> `f x + b <> NegInf` by PROVE_TAC [IN_INSERT, add_not_infty]
 >> `!z. z IN (e INSERT s) ==> f z <> NegInf` by PROVE_TAC [IN_INSERT]
 >> `!x. x IN s ==> f x <> NegInf` by PROVE_TAC [IN_INSERT]
 >> `!y. y IN (x INSERT s) ==> f y <> NegInf` by PROVE_TAC [IN_INSERT, INSERT_COMM]
 >> ASM_SIMP_TAC bool_ss [lemma1', delete_non_element]
 >> `ITSET (\e acc. f e + acc) s b <> NegInf` by METIS_TAC [lemma2']
 >> Q.ABBREV_TAC `t = ITSET (\e acc. f e + acc) s b`
 >> Q.PAT_X_ASSUM `!x b. b <> NegInf => X` K_TAC
 >> METIS_TAC [add_assoc, add_comm, IN_INSERT]);

(* NOTE: EXTREAL_SUM_IMAGE is not defined if there're mixing of PosInfs and NegInfs
   in the summation, since ``PosInf + NegInf`` is not defined. *)

val EXTREAL_SUM_IMAGE_DEF = new_definition
  ("EXTREAL_SUM_IMAGE_DEF",
  ``EXTREAL_SUM_IMAGE f s = ITSET (\e acc. f e + acc) s (0 :extreal)``);

(* Now theorems about EXTREAL_SUM_IMAGE itself *)
val EXTREAL_SUM_IMAGE_EMPTY = store_thm
  ("EXTREAL_SUM_IMAGE_EMPTY", ``!f. EXTREAL_SUM_IMAGE f {} = 0``,
    SIMP_TAC (srw_ss()) [ITSET_THM, EXTREAL_SUM_IMAGE_DEF]);

(* this is provable by (old) EXTREAL_SUM_IMAGE_THM but using original definition is much
   easier, because CHOICE and REST from singleton can be easily eliminated. *)
val EXTREAL_SUM_IMAGE_SING = store_thm
  ("EXTREAL_SUM_IMAGE_SING", ``!f e. EXTREAL_SUM_IMAGE f {e} = f e``,
    SRW_TAC [][EXTREAL_SUM_IMAGE_DEF, ITSET_THM, add_rzero]);

(* This new theorem provides a "complete" picture for EXTREAL_SUM_IMAGE. *)
val EXTREAL_SUM_IMAGE_THM = store_thm
  ("EXTREAL_SUM_IMAGE_THM",
  ``!f. (EXTREAL_SUM_IMAGE f {} = 0) /\
        (!e. EXTREAL_SUM_IMAGE f {e} = f e) /\
        (!e s. FINITE s /\ ((!x. x IN (e INSERT s) ==> f x <> PosInf) \/
                            (!x. x IN (e INSERT s) ==> f x <> NegInf)) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) =
               f e + EXTREAL_SUM_IMAGE f (s DELETE e)))``,
  let val thm  = SIMP_RULE std_ss [num_not_infty] (Q.SPEC `0` lemma3);
      val thm' = SIMP_RULE std_ss [num_not_infty] (Q.SPEC `0` lemma3');
  in
    rpt STRIP_TAC >- REWRITE_TAC [EXTREAL_SUM_IMAGE_EMPTY]
                  >- REWRITE_TAC [EXTREAL_SUM_IMAGE_SING]
    >> SIMP_TAC (srw_ss()) [EXTREAL_SUM_IMAGE_DEF]
    >| [ METIS_TAC [thm], METIS_TAC [thm'] ]
  end);

(* A weaker but practical version in which all values from function f is restricted *)
val EXTREAL_SUM_IMAGE_INSERT = store_thm
  ("EXTREAL_SUM_IMAGE_INSERT",
  ``!f. (!x. f x <> PosInf) \/ (!x. f x <> NegInf) ==>
        !e s. FINITE s ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) =
               f e + EXTREAL_SUM_IMAGE f (s DELETE e))``,
    PROVE_TAC [EXTREAL_SUM_IMAGE_THM]);

val EXTREAL_SUM_IMAGE_NOT_NEGINF = store_thm
  ("EXTREAL_SUM_IMAGE_NOT_NEGINF",
  ``!f s. FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==> EXTREAL_SUM_IMAGE f s <> NegInf``,
  let val thm = ((SIMP_RULE std_ss [num_not_infty])
                 o (Q.SPECL [`f`, `s`, `0`])
                 o (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO])) lemma2';
  in
    rpt GEN_TAC >> STRIP_TAC \\
    REWRITE_TAC [EXTREAL_SUM_IMAGE_DEF] \\
    MATCH_MP_TAC thm >> ASM_REWRITE_TAC []
  end);

val EXTREAL_SUM_IMAGE_NOT_POSINF = store_thm (* re-worked *)
  ("EXTREAL_SUM_IMAGE_NOT_POSINF",
  ``!f s. FINITE s /\ (!x. x IN s ==> f x <> PosInf) ==> EXTREAL_SUM_IMAGE f s <> PosInf``,
  let val thm = ((SIMP_RULE std_ss [num_not_infty])
                 o (Q.SPECL [`f`, `s`, `0`])
                 o (SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO])) lemma2;
  in
    rpt GEN_TAC >> STRIP_TAC \\
    REWRITE_TAC [EXTREAL_SUM_IMAGE_DEF] \\
    MATCH_MP_TAC thm >> ASM_REWRITE_TAC []
  end);

val EXTREAL_SUM_IMAGE_NOT_INFTY = store_thm
  ("EXTREAL_SUM_IMAGE_NOT_INFTY",
  ``!f s. (FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==> EXTREAL_SUM_IMAGE f s <> NegInf) /\
          (FINITE s /\ (!x. x IN s ==> f x <> PosInf) ==> EXTREAL_SUM_IMAGE f s <> PosInf)``,
  RW_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_NEGINF,
                 EXTREAL_SUM_IMAGE_NOT_POSINF]);

val EXTREAL_SUM_IMAGE_PROPERTY_NEG = store_thm
  ("EXTREAL_SUM_IMAGE_PROPERTY_NEG",
  ``!f s. FINITE s ==>
          !e. (!x. x IN e INSERT s ==> f x <> NegInf) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) = f e + EXTREAL_SUM_IMAGE f (s DELETE e))``,
  RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM]);

val EXTREAL_SUM_IMAGE_PROPERTY_POS = store_thm
  ("EXTREAL_SUM_IMAGE_PROPERTY_POS",
  ``!f s. FINITE s ==>
          !e. (!x. x IN e INSERT s ==> f x <> PosInf) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) = f e + EXTREAL_SUM_IMAGE f (s DELETE e))``,
  RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM]);

val EXTREAL_SUM_IMAGE_PROPERTY = store_thm
  ("EXTREAL_SUM_IMAGE_PROPERTY",
  ``!f s. FINITE s  ==>
          !e. (!x. x IN e INSERT s ==> f x <> NegInf) \/
              (!x. x IN e INSERT s ==> f x <> PosInf) ==>
              (EXTREAL_SUM_IMAGE f (e INSERT s) = f e + EXTREAL_SUM_IMAGE f (s DELETE e))``,
  PROVE_TAC [EXTREAL_SUM_IMAGE_PROPERTY_NEG,
             EXTREAL_SUM_IMAGE_PROPERTY_POS]);

val EXTREAL_SUM_IMAGE_POS = store_thm
  ("EXTREAL_SUM_IMAGE_POS",
   ``!f s. FINITE s /\ (!x. x IN s ==> 0 <= f x) ==>
           0 <= EXTREAL_SUM_IMAGE f s``,
  Suff `!s. FINITE s ==> (\s. !f. (!x. x IN s ==> 0 <= f x) ==>
            0 <= EXTREAL_SUM_IMAGE f s) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,le_refl]
  >> `!x. x IN e INSERT s ==> f x <> NegInf`
        by METIS_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans]
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,delete_non_element]
  >> METIS_TAC [le_add,IN_INSERT]);

val EXTREAL_SUM_IMAGE_NEG = store_thm
  ("EXTREAL_SUM_IMAGE_NEG",
  ``!f s. FINITE s /\ (!x. x IN s ==> f x <= 0) ==> EXTREAL_SUM_IMAGE f s <= 0``,
    Suff `!s. FINITE s ==>
              (\s. !f. (!x. x IN s ==> f x <= 0) ==>
                   EXTREAL_SUM_IMAGE f s <= 0) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, le_refl]
 >> `!x. x IN e INSERT s ==> f x <> PosInf`
        by METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, let_trans]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, delete_non_element]
 >> METIS_TAC [le_add_neg, IN_INSERT]);

val EXTREAL_SUM_IMAGE_SPOS = store_thm
  ("EXTREAL_SUM_IMAGE_SPOS",
  ``!f s. FINITE s /\ (~(s = {})) /\ (!x. x IN s ==> 0 < f x) ==>
          0 < EXTREAL_SUM_IMAGE f s``,
    Suff `!s. FINITE s ==> (\s. !f. s <> {} /\ (!x. x IN s ==> 0 < f x) ==>
                                    0 < EXTREAL_SUM_IMAGE f s) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> `!x. x IN e INSERT s ==> f x <> NegInf`
        by METIS_TAC [IN_INSERT, lt_infty, lt_trans, lt_imp_le, extreal_of_num_def]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, delete_non_element]
 >> Cases_on `s = {}`
 >- METIS_TAC [EXTREAL_SUM_IMAGE_EMPTY, add_rzero, IN_INSERT]
 >> METIS_TAC [lt_add, IN_INSERT]);

val EXTREAL_SUM_IMAGE_SNEG = store_thm
  ("EXTREAL_SUM_IMAGE_SNEG",
  ``!f s. FINITE s /\ (~(s = {})) /\ (!x. x IN s ==> f x < 0) ==>
          EXTREAL_SUM_IMAGE f s < 0``,
    Suff `!s. FINITE s ==> (\s. !f. s <> {} /\ (!x. x IN s ==> f x < 0) ==>
                                    EXTREAL_SUM_IMAGE f s < 0) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> `!x. x IN e INSERT s ==> f x <> PosInf`
        by METIS_TAC [IN_INSERT, lt_infty, lt_trans, lt_imp_le, extreal_of_num_def]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, delete_non_element]
 >> Cases_on `s = {}`
 >- METIS_TAC [EXTREAL_SUM_IMAGE_EMPTY, add_rzero, IN_INSERT]
 >> METIS_TAC [lt_add_neg, IN_INSERT]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_IF_ELIM = store_thm
  ("EXTREAL_SUM_IMAGE_IF_ELIM",
  ``!s P f. FINITE s /\ (!x. x IN s ==> P x) /\
            ((!x. x IN s ==> f x <> NegInf) \/ !x. x IN s ==> f x <> PosInf)
        ==> (EXTREAL_SUM_IMAGE (\x. if P x then f x else 0) s = EXTREAL_SUM_IMAGE f s)``,
    Suff `!s. FINITE s ==>
             (\s. !P f. (!x. x IN s ==> P x) /\
                        ((!x. x IN s ==> f x <> NegInf) \/ !x. x IN s ==> f x <> PosInf) ==>
                        (EXTREAL_SUM_IMAGE (\x. if P x then f x else 0) s =
                         EXTREAL_SUM_IMAGE f s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY]
 >- (`!x. x IN e INSERT s ==> (\x. if P x then f x else 0) x <> NegInf`
        by METIS_TAC [extreal_of_num_def, lt_infty, lt_imp_ne] \\
     RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY] \\
     METIS_TAC [IN_INSERT, DELETE_NON_ELEMENT, lt_infty] )
 >> `!x. x IN (e INSERT s) ==> ((\x. if P x then f x else 0) x <> PosInf)`
        by METIS_TAC[extreal_of_num_def,lt_infty,lt_imp_ne]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >- METIS_TAC [IN_INSERT, DELETE_NON_ELEMENT]
 >> METIS_TAC [IN_INSERT]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_FINITE_SAME = store_thm
  ("EXTREAL_SUM_IMAGE_FINITE_SAME",
  ``!s. FINITE s ==>
        !f p. p IN s /\ (!q. q IN s ==> (f p = f q)) /\
             ((!x. x IN s ==> f x <> NegInf) \/ !x. x IN s ==> f x <> PosInf)
         ==> (EXTREAL_SUM_IMAGE f s = (&(CARD s)) * f p)``,
    Suff `!s. FINITE s ==>
             (\s. !f p. p IN s /\ (!q. q IN s ==> (f p = f q)) /\
                  ((!x. x IN s ==> f x <> NegInf) \/ !x. x IN s ==> f x <> PosInf)
              ==> (EXTREAL_SUM_IMAGE f s = (&(CARD s)) * f p)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, CARD_EMPTY, mul_lzero, DELETE_NON_ELEMENT] (* 2 goals *)
 >> (* it must be right-associative, thus the next steps solve both goals *)
 (RW_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
  >> `f p = f e` by FULL_SIMP_TAC std_ss [IN_INSERT]
  >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT] >> POP_ASSUM (K ALL_TAC)
  >> RW_TAC std_ss [CARD_INSERT, ADD1, extreal_of_num_def, GSYM REAL_ADD, GSYM extreal_add_def]
  >> RW_TAC std_ss [GSYM extreal_of_num_def]
  >> `(&CARD s) <> NegInf /\ 1 <> NegInf /\ (&CARD s) <> PosInf /\ 1 <> PosInf /\ 0 <= (&CARD s) /\ 0 <= 1`
       by METIS_TAC [extreal_not_infty, extreal_of_num_def, le_num, le_01]
  >> RW_TAC std_ss [add_rdistrib, mul_lone]
  >> Suff `EXTREAL_SUM_IMAGE f s = & (CARD s) * f e`
  >- METIS_TAC [add_comm, EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT]
  >> (MP_TAC o Q.SPECL [`s`]) SET_CASES >> RW_TAC std_ss []
  >- RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, CARD_EMPTY, mul_lzero]
  >> `f e = f x` by FULL_SIMP_TAC std_ss [IN_INSERT]
  >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
  >> Q.PAT_X_ASSUM `!f p. b` MATCH_MP_TAC >> METIS_TAC [IN_INSERT]));

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_FINITE_CONST = store_thm
  ("EXTREAL_SUM_IMAGE_FINITE_CONST",
  ``!P. FINITE P ==>
        !f x. (!y. f y = x) /\ (x <> NegInf \/ x <> PosInf) ==>
              (EXTREAL_SUM_IMAGE f P = (&(CARD P)) * x)``,
    rpt STRIP_TAC (* 2 sub-goals here *)
 >> (* right-associative here *)
  ((MP_TAC o Q.SPECL [`P`]) EXTREAL_SUM_IMAGE_FINITE_SAME
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
 >> RW_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`P`]) SET_CASES
 >> RW_TAC std_ss []
 >- (ONCE_REWRITE_TAC [EXTREAL_SUM_IMAGE_THM] THEN RW_TAC real_ss [CARD_EMPTY,mul_lzero])
 >> POP_ASSUM (K ALL_TAC)
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `x'`
 >> RW_TAC std_ss [IN_INSERT] ));

val EXTREAL_SUM_IMAGE_ZERO = store_thm
  ("EXTREAL_SUM_IMAGE_ZERO", ``!s. FINITE s ==> (EXTREAL_SUM_IMAGE (\x. 0) s = 0)``,
    RW_TAC std_ss []
 >> Suff `EXTREAL_SUM_IMAGE (\x. 0) s = &CARD s * 0`
 >- METIS_TAC [mul_rzero]
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_FINITE_CONST
 >> RW_TAC std_ss [num_not_infty]);

val EXTREAL_SUM_IMAGE_0 = store_thm
  ("EXTREAL_SUM_IMAGE_0",
  ``!f s. FINITE s /\ (!x. x IN s ==> (f x = 0)) ==> (EXTREAL_SUM_IMAGE f s = 0)``,
    Suff `!s. FINITE s ==>
             (\s. !f. (!x. x IN s ==> (f x = 0)) ==> (EXTREAL_SUM_IMAGE f s = 0)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, DELETE_NON_ELEMENT]
 >> `!x. x IN (e INSERT s) ==> f x <> PosInf` by PROVE_TAC [num_not_infty]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> METIS_TAC [IN_INSERT, add_lzero]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_IN_IF = store_thm
  ("EXTREAL_SUM_IMAGE_IN_IF",
  ``!s. FINITE s ==>
        !f. ((!x. x IN s ==> f x <> NegInf) \/
             (!x. x IN s ==> f x <> PosInf)) ==>
            (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s)``,
    Suff `!s. FINITE s ==>
              (\s. !f. ((!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf)) ==>
                       (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s)) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY]
 >- (`!x. (\x. if x IN e INSERT s then f x else 0) x <> NegInf`
         by RW_TAC std_ss [extreal_not_infty, extreal_of_num_def]
     >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY]
     >> `s DELETE e = s` by rw[GSYM DELETE_NON_ELEMENT]
     >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s`
         by METIS_TAC [IN_INSERT]
     >> Q.PAT_X_ASSUM `!x:'a. x IN e INSERT s ==> f x <> NegInf` K_TAC
     >> FULL_SIMP_TAC real_ss [IN_INSERT])
 >> `!x. (\x. if x IN e INSERT s then f x else 0) x <> PosInf`
         by RW_TAC std_ss [extreal_not_infty, extreal_of_num_def]
 >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> `s DELETE e = s` by rw [GSYM DELETE_NON_ELEMENT]
 >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else 0) s`
         by METIS_TAC [IN_INSERT]
 >> Q.PAT_X_ASSUM `!x:'a. x IN e INSERT s ==> f x <> PosInf` K_TAC
 >> FULL_SIMP_TAC std_ss [IN_INSERT]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_CMUL = store_thm
  ("EXTREAL_SUM_IMAGE_CMUL",
  ``!s. FINITE s ==>
        !f c. (!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf) ==>
              (EXTREAL_SUM_IMAGE (\x. Normal (c) * f x) s = Normal (c) * (EXTREAL_SUM_IMAGE f s))``,
    Suff `!f c s.
             FINITE s ==>
             (\s. (!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf) ==>
                  (EXTREAL_SUM_IMAGE (\x. Normal (c) * f x) s = Normal (c) * (EXTREAL_SUM_IMAGE f s))) s`
 >- METIS_TAC []
 >> STRIP_TAC >> STRIP_TAC >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,mul_rzero]
 >- ( Cases_on `0 <= c`
      >- (`!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> NegInf` by METIS_TAC [mul_not_infty,IN_INSERT]
          >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
          >> METIS_TAC [add_ldistrib_normal,EXTREAL_SUM_IMAGE_NOT_INFTY,IN_INSERT])
      >> `!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> PosInf`
                by METIS_TAC [mul_not_infty,real_lt,REAL_LT_IMP_LE]
      >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
      >> METIS_TAC [add_ldistrib_normal,EXTREAL_SUM_IMAGE_NOT_INFTY,IN_INSERT] )
 >> Cases_on `0 <= c`
 >- (`!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> PosInf` by METIS_TAC [mul_not_infty] \\
     FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT] \\
     METIS_TAC [add_ldistrib_normal, EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT])
 >> `!x. x IN e INSERT s ==> (\x. Normal c * f x) x <> NegInf`
                by METIS_TAC [mul_not_infty, real_lt, REAL_LT_IMP_LE]
 >> FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
 >> METIS_TAC [add_ldistrib_normal, EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT]);

(* this is not true any more: (but how to fix it?)
val EXTREAL_SUM_IMAGE_CMUL2 = store_thm
  ("EXTREAL_SUM_IMAGE_CMUL2",
  ``!s f c. FINITE s /\ (!x. x IN s ==> f x <> NegInf) ==>
           (EXTREAL_SUM_IMAGE (\x. Normal c * f x) s = Normal c * (EXTREAL_SUM_IMAGE f s))``,
    Suff `!s. FINITE s ==>
             (\s. !f c. (!x. x IN s ==> f x <> NegInf) ==>
                        (EXTREAL_SUM_IMAGE (\x. Normal c * f x) s =
                         Normal c * (EXTREAL_SUM_IMAGE f s))) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_THM, mul_rzero, DELETE_NON_ELEMENT]
 >> Cases_on `c = 0` >- RW_TAC std_ss [GSYM extreal_of_num_def, mul_lzero, add_lzero,
                                       EXTREAL_SUM_IMAGE_0]
 >> Cases_on `0 < c`
 >- METIS_TAC [extreal_le_def, add_ldistrib_normal2, REAL_LT_IMP_LE, IN_INSERT]
 >> `c < 0` by METIS_TAC [REAL_LT_TOTAL]
 >> `EXTREAL_SUM_IMAGE f s <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT]
 >> METIS_TAC [extreal_le_def, add_ldistrib_normal, REAL_LT_IMP_LE, IN_INSERT]);
 *)

(* more antecedents added, cf. SUM_IMAGE_INJ_o *)
Theorem EXTREAL_SUM_IMAGE_IMAGE :
    !s. FINITE s ==>
        !f'. INJ f' s (IMAGE f' s) ==>
             !f. (!x. x IN (IMAGE f' s) ==> f x <> NegInf) \/
                 (!x. x IN (IMAGE f' s) ==> f x <> PosInf)
             ==> (EXTREAL_SUM_IMAGE f (IMAGE f' s) = EXTREAL_SUM_IMAGE (f o f') s)
Proof
     Suff `!s. FINITE s ==>
               (\s. !f'. INJ f' s (IMAGE f' s) ==>
                         !f. (!x. x IN (IMAGE f' s) ==> f x <> NegInf) \/
                             (!x. x IN (IMAGE f' s) ==> f x <> PosInf) ==>
                             (EXTREAL_SUM_IMAGE f (IMAGE f' s) =
                              EXTREAL_SUM_IMAGE (f o f') s)) s`
  >- METIS_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,IMAGE_EMPTY,IMAGE_INSERT,INJ_DEF]
  >- (`FINITE (IMAGE f' s)` by METIS_TAC [IMAGE_FINITE]
      >> `!x. x IN e INSERT s ==> (f o f') x <> NegInf` by METIS_TAC [o_DEF]
      >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
      >> `~ (f' e IN IMAGE f' s)`
        by (RW_TAC std_ss [IN_IMAGE] >> reverse (Cases_on `x IN s`)
            >- ASM_REWRITE_TAC [] >> METIS_TAC [IN_INSERT])
      >> `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
      >> `(IMAGE f' s) DELETE f' e = IMAGE f' s` by METIS_TAC [DELETE_NON_ELEMENT]
      >> ASM_REWRITE_TAC []
      >> `(!x. x IN s ==> f' x IN IMAGE f' s)` by METIS_TAC [IN_IMAGE]
      >> `(!x y. x IN s /\ y IN s ==> (f' x = f' y) ==> (x = y))` by METIS_TAC [IN_INSERT]
      >> `(!x. x IN IMAGE f' s ==> f x <> NegInf)` by METIS_TAC [IN_INSERT]
      >> FULL_SIMP_TAC std_ss [])
  >> `FINITE (IMAGE f' s)` by METIS_TAC [IMAGE_FINITE]
  >> `!x. x IN e INSERT s ==> (f o f') x <> PosInf` by METIS_TAC [o_DEF]
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
  >> `f' e NOTIN IMAGE f' s`
        by (RW_TAC std_ss [IN_IMAGE] >> reverse (Cases_on `x IN s`)
            >- ASM_REWRITE_TAC [] >> METIS_TAC [IN_INSERT])
  >> `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
  >> `(IMAGE f' s) DELETE f' e = IMAGE f' s` by METIS_TAC [DELETE_NON_ELEMENT]
  >> ASM_REWRITE_TAC []
  >> `(!x. x IN s ==> f' x IN IMAGE f' s)` by METIS_TAC [IN_IMAGE]
  >> `(!x y. x IN s /\ y IN s ==> (f' x = f' y) ==> (x = y))` by METIS_TAC [IN_INSERT]
  >> `(!x. x IN IMAGE f' s ==> f x <> PosInf)` by METIS_TAC [IN_INSERT]
  >> FULL_SIMP_TAC std_ss []
QED

Theorem EXTREAL_SUM_IMAGE_PERMUTES :
    !s. FINITE s ==> !g. g PERMUTES s ==>
        !f. (!x. x IN (IMAGE g s) ==> f x <> NegInf) \/
            (!x. x IN (IMAGE g s) ==> f x <> PosInf) ==>
            (EXTREAL_SUM_IMAGE (f o g) s = EXTREAL_SUM_IMAGE f s)
Proof
    NTAC 5 STRIP_TAC >> DISCH_TAC
 >> `INJ g s s /\ SURJ g s s` by METIS_TAC [BIJ_DEF]
 >> `IMAGE g s = s` by SRW_TAC[][GSYM IMAGE_SURJ]
 >> `s SUBSET univ(:'a)` by SRW_TAC[][SUBSET_UNIV]
 >> `INJ g s univ(:'a)` by METIS_TAC[INJ_SUBSET, SUBSET_REFL]
 >> Know `EXTREAL_SUM_IMAGE (f o g) s = EXTREAL_SUM_IMAGE f (IMAGE g s)`
 >- (MATCH_MP_TAC EQ_SYM \\
     irule EXTREAL_SUM_IMAGE_IMAGE >> rw [])
 >> SRW_TAC[][]
QED

Theorem EXTREAL_SUM_IMAGE_DISJOINT_UNION : (* more antecedents added *)
    !s s'. FINITE s /\ FINITE s' /\ DISJOINT s s' ==>
           !f. (!x. x IN s UNION s' ==> f x <> NegInf) \/
               (!x. x IN s UNION s' ==> f x <> PosInf) ==>
               (EXTREAL_SUM_IMAGE f (s UNION s') =
                EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')
Proof
  Suff `!s. FINITE s ==> (\s. !s'. FINITE s' ==>
            (\s'. DISJOINT s s' ==>
                  (!f. (!x. x IN s UNION s' ==> f x <> NegInf) \/
                       (!x. x IN s UNION s' ==> f x <> PosInf) ==>
                       (EXTREAL_SUM_IMAGE f (s UNION s') =
                        EXTREAL_SUM_IMAGE f s +
                        EXTREAL_SUM_IMAGE f s'))) s') s`
  >- METIS_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> CONJ_TAC
  >- RW_TAC std_ss [DISJOINT_EMPTY, UNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY,add_lzero]
  >> rpt STRIP_TAC
  >> CONV_TAC (BETA_CONV) >> MATCH_MP_TAC FINITE_INDUCT
  >> CONJ_TAC
  >- RW_TAC std_ss [DISJOINT_EMPTY, UNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY,add_rzero]
  >> FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
  >> ONCE_REWRITE_TAC [DISJOINT_SYM]
  >> RW_TAC std_ss [INSERT_UNION, DISJOINT_INSERT, IN_INSERT]
  >- ( FULL_SIMP_TAC std_ss [DISJOINT_SYM]
       >> ONCE_REWRITE_TAC [UNION_COMM] >> RW_TAC std_ss [INSERT_UNION]
       >> ONCE_REWRITE_TAC [UNION_COMM] >> ONCE_REWRITE_TAC [INSERT_COMM]
       >> `FINITE (e INSERT s UNION s')` by RW_TAC std_ss [FINITE_INSERT, FINITE_UNION]
       >> Q.ABBREV_TAC `Q = e INSERT s UNION s'`
       >> `!x. x IN e INSERT s ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> `!x. x IN e' INSERT s' ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> `!x. x IN e' INSERT Q ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
       >> Q.UNABBREV_TAC `Q`
       >> `~ (e' IN (e INSERT s UNION s'))`
              by (RW_TAC std_ss[IN_INSERT, IN_UNION] \\
                FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT])
       >> `!x. x IN e INSERT (s UNION s') ==> f x <> NegInf` by METIS_TAC [IN_UNION,IN_INSERT]
       >> `~(e IN (s UNION s'))` by METIS_TAC [IN_UNION,DELETE_NON_ELEMENT]
       >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT,EXTREAL_SUM_IMAGE_PROPERTY,FINITE_UNION]
       >> `EXTREAL_SUM_IMAGE f s <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION]
       >> `EXTREAL_SUM_IMAGE f s' <> NegInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION,IN_INSERT]
       >> FULL_SIMP_TAC std_ss [IN_INSERT]
       >> RW_TAC std_ss [add_assoc]
       >> `f e' + (f e + EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s') =
          (f e + (EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')) + f e'`
              by METIS_TAC [add_comm,add_not_infty,add_assoc,IN_INSERT]
       >> POP_ORW
       >> RW_TAC std_ss [add_assoc]
       >> METIS_TAC [add_not_infty,add_comm,add_assoc] )
  >> FULL_SIMP_TAC std_ss [DISJOINT_SYM]
  >> ONCE_REWRITE_TAC [UNION_COMM] >> RW_TAC std_ss [INSERT_UNION]
  >> ONCE_REWRITE_TAC [UNION_COMM] >> ONCE_REWRITE_TAC [INSERT_COMM]
  >> `FINITE (e INSERT s UNION s')` by RW_TAC std_ss [FINITE_INSERT, FINITE_UNION]
  >> Q.ABBREV_TAC `Q = e INSERT s UNION s'`
  >> `!x. x IN e INSERT s ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> `!x. x IN e' INSERT s' ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> `!x. x IN e' INSERT Q ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> Q.UNABBREV_TAC `Q`
  >> `~ (e' IN (e INSERT s UNION s'))`
      by (RW_TAC std_ss [IN_INSERT, IN_UNION] \\
          FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT])
  >> `!x. x IN e INSERT (s UNION s') ==> f x <> PosInf` by METIS_TAC [IN_UNION,IN_INSERT]
  >> `~(e IN (s UNION s'))` by METIS_TAC [IN_UNION,DELETE_NON_ELEMENT]
  >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT,EXTREAL_SUM_IMAGE_PROPERTY,FINITE_UNION]
  >> `EXTREAL_SUM_IMAGE f s <> PosInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION]
  >> `EXTREAL_SUM_IMAGE f s' <> PosInf` by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_UNION,IN_INSERT]
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >> RW_TAC std_ss [add_assoc]
  >> `f e' + (f e + EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s') =
       (f e + (EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f s')) + f e'`
              by METIS_TAC [add_comm,add_not_infty,add_assoc,IN_INSERT]
  >> POP_ORW
  >> RW_TAC std_ss [add_assoc]
  >> METIS_TAC [add_not_infty, add_comm, add_assoc]
QED

Theorem EXTREAL_SUM_IMAGE_EQ_CARD :
    !s. FINITE s ==>
       (EXTREAL_SUM_IMAGE (\x. if x IN s then 1 else 0) s = &(CARD s))
Proof
    Suff `!s. FINITE s ==>
             (\s. EXTREAL_SUM_IMAGE (\x. if x IN s then 1 else 0) s = (&(CARD s))) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, CARD_EMPTY, IN_INSERT]
 >> `!x. (\x. if (x = e) \/ x IN s then 1 else 0) x <> NegInf`
      by RW_TAC real_ss [extreal_of_num_def,extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
 >> (MP_TAC o Q.SPECL [`s`]) CARD_INSERT
 >> `~(e IN s)` by METIS_TAC [DELETE_NON_ELEMENT]
 >> RW_TAC std_ss [ADD1,extreal_of_num_def, GSYM REAL_ADD, GSYM extreal_add_eq]
 >> RW_TAC std_ss [GSYM extreal_of_num_def]
 >> Suff `EXTREAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) s =
          EXTREAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s`
 >- METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, add_comm, extreal_not_infty,
               extreal_of_num_def]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_IN_IF]
QED

val EXTREAL_SUM_IMAGE_INV_CARD_EQ_1 = store_thm
  ("EXTREAL_SUM_IMAGE_INV_CARD_EQ_1",
  ``!s. s <> {} /\ FINITE s ==>
        (EXTREAL_SUM_IMAGE (\x. if x IN s then inv (&(CARD s)) else 0) s = 1)``,
    rpt STRIP_TAC
 >> `(\x. if x IN s then inv (& (CARD s)) else 0) =
     (\x. inv (& (CARD s)) * (\x. if x IN s then 1 else 0) x)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [mul_rzero, mul_rone])
 >> POP_ORW
 >> `CARD s <> 0` by METIS_TAC [CARD_EQ_0]
 >> `inv (&CARD s) = Normal (inv (&CARD s))`
    by FULL_SIMP_TAC real_ss [extreal_inv_def, extreal_of_num_def]
 >> POP_ORW
 >> `!x. (\x. if x IN s then 1 else 0) x <> NegInf`
    by METIS_TAC [extreal_not_infty, extreal_of_num_def]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_CMUL, EXTREAL_SUM_IMAGE_EQ_CARD]
 >> RW_TAC std_ss [extreal_of_num_def,extreal_mul_def]
 >> `&CARD s <> 0r` by FULL_SIMP_TAC real_ss [extreal_inv_def, extreal_of_num_def]
 >> METIS_TAC [REAL_MUL_LINV]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_INTER_NONZERO = store_thm
  ("EXTREAL_SUM_IMAGE_INTER_NONZERO",
  ``!s. FINITE s ==>
        !f. (!x. x IN s ==> f x <> NegInf) \/
            (!x. x IN s ==> f x <> PosInf) ==>
           (EXTREAL_SUM_IMAGE f (s INTER (\p. ~(f p = 0))) =
            EXTREAL_SUM_IMAGE f s)``,
 (* proof *)
    Suff `!s. FINITE s ==>
             (\s. !f. (!x. x IN s ==> f x <> NegInf) \/
                      (!x. x IN s ==> f x <> PosInf) ==>
                      (EXTREAL_SUM_IMAGE f (s INTER (\p. ~(f p = 0))) =
                       EXTREAL_SUM_IMAGE f s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, INTER_EMPTY, INSERT_INTER]
 >- ( Cases_on `e IN (\p. f p <> 0)`
      >- (RW_TAC std_ss []
          >> `~(e IN (s INTER (\p. ~(f p = 0))))` by RW_TAC std_ss [IN_INTER]
          >> `!x. x IN (e INSERT s INTER (\p. f p <> 0)) ==> f x <> NegInf`
                by METIS_TAC [IN_INTER,IN_INSERT]
          >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT,INTER_FINITE]
          >> FULL_SIMP_TAC std_ss [IN_INSERT])
      >> RW_TAC std_ss []
      >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT,add_lzero,IN_ABS] )
 >> Cases_on `e IN (\p. f p <> 0)`
 >- ( RW_TAC std_ss []
      >> `~(e IN (s INTER (\p. ~(f p = 0))))` by RW_TAC std_ss [IN_INTER]
      >> `!x. x IN (e INSERT s INTER (\p. f p <> 0)) ==> f x <> PosInf`
            by METIS_TAC [IN_INTER,IN_INSERT]
      >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT,INTER_FINITE]
      >> FULL_SIMP_TAC std_ss [IN_INSERT] )
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
 >> FULL_SIMP_TAC std_ss [IN_INSERT]
 >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, add_lzero, IN_ABS]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_INTER_ELIM = store_thm
  ("EXTREAL_SUM_IMAGE_INTER_ELIM",
   ``!s. FINITE s ==>
         !f s'. ((!x. x IN s ==> f x <> NegInf) \/
                 (!x. x IN s ==> f x <> PosInf)) /\
                (!x. (~(x IN s')) ==> (f x = 0)) ==>
                (EXTREAL_SUM_IMAGE f (s INTER s') =
                 EXTREAL_SUM_IMAGE f s)``,
  Suff `!s. FINITE s ==>
        (\s. !f s'. ((!x. x IN s ==> f x <> NegInf) \/
                     (!x. x IN s ==> f x <> PosInf)) /\
                    (!x. (~(x IN s')) ==> (f x = 0)) ==>
                    (EXTREAL_SUM_IMAGE f (s INTER s') =
                     EXTREAL_SUM_IMAGE f s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [INTER_EMPTY,INSERT_INTER]
  >- (FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
      >> Cases_on `e IN s'`
      >- (`~ (e IN (s INTER s'))` by (rw[IN_INTER] >> fs[DELETE_NON_ELEMENT])
          >> `!x. x IN e INSERT (s INTER s') ==> f x <> NegInf` by METIS_TAC [IN_INTER,IN_INSERT]
          >> FULL_SIMP_TAC std_ss [INTER_FINITE, EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
          >> FULL_SIMP_TAC std_ss [IN_INSERT]
          >> METIS_TAC [IN_INTER,DELETE_NON_ELEMENT])
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> METIS_TAC [DELETE_NON_ELEMENT,add_lzero])
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> Cases_on `e IN s'`
  >- (`~ (e IN (s INTER s'))` by (rw[IN_INTER] >> fs[DELETE_NON_ELEMENT])
      >> `!x. x IN e INSERT (s INTER s') ==> f x <> PosInf` by METIS_TAC [IN_INTER,IN_INSERT]
      >> FULL_SIMP_TAC std_ss [INTER_FINITE, EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> METIS_TAC [IN_INTER,DELETE_NON_ELEMENT])
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >> METIS_TAC [DELETE_NON_ELEMENT,add_lzero]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_ZERO_DIFF = store_thm
  ("EXTREAL_SUM_IMAGE_ZERO_DIFF",
  ``!s. FINITE s ==> !f t. ((!x. x IN s ==> f x <> NegInf) \/
                             (!x. x IN s ==> f x <> PosInf)) /\
                           (!x. x IN t ==> (f x = 0)) ==>
                           (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f (s DIFF t))``,
  RW_TAC std_ss []
  >> `s = (s DIFF t) UNION (s INTER t)` by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
                                            >> METIS_TAC [])
  >> `FINITE (s DIFF t) /\ FINITE (s INTER t)` by METIS_TAC [INTER_FINITE, FINITE_DIFF]
  >> `DISJOINT (s DIFF t) (s INTER t)` by (RW_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY,
                                           EXTENSION, IN_DIFF] >> METIS_TAC [])
  >> `EXTREAL_SUM_IMAGE f (s INTER t) = 0` by METIS_TAC [EXTREAL_SUM_IMAGE_0, IN_INTER]
  >> METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION, add_rzero]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_MONO = store_thm
  ("EXTREAL_SUM_IMAGE_MONO",
   ``!s. FINITE s ==>
           !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\
                  (!x. x IN s ==> f x <= f' x) ==>
                  EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f' s``,
   Suff `!s. FINITE s ==>
             (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                          (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\
                         (!x. x IN s ==> f x <= f' x) ==>
                         EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f' s) s`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,le_refl]
   >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT, IN_INSERT,
                      DISJ_IMP_THM, FORALL_AND_THM]
   >> METIS_TAC [le_add2,EXTREAL_SUM_IMAGE_NOT_INFTY]);

val EXTREAL_SUM_IMAGE_MONO_SET = store_thm
  ("EXTREAL_SUM_IMAGE_MONO_SET",
   ``!f s t. (FINITE s /\ FINITE t /\ s SUBSET t /\ (!x. x IN t ==> 0 <= f x)) ==>
             EXTREAL_SUM_IMAGE f s <= EXTREAL_SUM_IMAGE f t``,
  RW_TAC std_ss []
  >> `t = s UNION (t DIFF s)` by RW_TAC std_ss [UNION_DIFF]
  >> `FINITE (t DIFF s)` by RW_TAC std_ss [FINITE_DIFF]
  >> `DISJOINT s (t DIFF s)`
        by (`DISJOINT s (t DIFF s)`
                by (rw [DISJOINT_DEF,IN_DIFF,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER] \\
                    metis_tac[]) \\
            metis_tac[])
  >> `!x. x IN (s UNION (t DIFF s)) ==> f x <> NegInf`
        by METIS_TAC [extreal_of_num_def,extreal_not_infty,lt_infty,lte_trans]
  >> `EXTREAL_SUM_IMAGE f t = EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f (t DIFF s)`
        by METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
  >> POP_ORW
  >> METIS_TAC [le_add2,le_refl,add_rzero,EXTREAL_SUM_IMAGE_POS,IN_DIFF]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_EQ = store_thm
  ("EXTREAL_SUM_IMAGE_EQ",
   ``!s. FINITE s ==>
           !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\
                   (!x. x IN s ==> (f x = f' x)) ==>
                (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f' s)``,
  Suff `!s. FINITE s ==>
                (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) /\ (!x. x IN s ==> (f x = f' x)) ==>
                (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE f' s)) s`
  >- PROVE_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT, IN_INSERT,
                           DISJ_IMP_THM, FORALL_AND_THM]
  >> METIS_TAC []);

val EXTREAL_SUM_IMAGE_POS_MEM_LE = store_thm
  ("EXTREAL_SUM_IMAGE_POS_MEM_LE",
   ``!f s. FINITE s  /\ (!x. x IN s ==> 0 <= f x) ==>
            (!x. x IN s ==> f x <= EXTREAL_SUM_IMAGE f s)``,
  Suff `!s. FINITE s ==>
        (\s. !f. (!x. x IN s ==> 0 <= f x) ==>
            (!x. x IN s ==> f x <= EXTREAL_SUM_IMAGE f s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [NOT_IN_EMPTY]
  >> `!x. x IN e INSERT s ==> f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >- METIS_TAC [EXTREAL_SUM_IMAGE_POS,le_add2,add_rzero,extreal_of_num_def,extreal_not_infty,le_refl]
  >> `f x <= EXTREAL_SUM_IMAGE f s` by FULL_SIMP_TAC std_ss [IN_INSERT]
  >> METIS_TAC [le_add2,add_lzero,extreal_of_num_def,extreal_not_infty]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_ADD = store_thm
  ("EXTREAL_SUM_IMAGE_ADD",
  ``!s. FINITE s ==>
        !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) ==>
               (EXTREAL_SUM_IMAGE (\x. f x + f' x) s =
                EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f' s)``,
  Suff `!s. FINITE s ==>
        (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> NegInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> PosInf)) ==>
                (EXTREAL_SUM_IMAGE (\x. f x + f' x) s =
                 EXTREAL_SUM_IMAGE f s + EXTREAL_SUM_IMAGE f' s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,add_lzero]
  >- (`!x. x IN e INSERT s ==> (\x. f x + f' x) x <> NegInf` by METIS_TAC [add_not_infty]
      >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
      >> `EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
          f' e + (EXTREAL_SUM_IMAGE f' s + EXTREAL_SUM_IMAGE f s)`
           by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
      >> `f e + EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
          f e + (EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s))`
           by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
      >> POP_ORW >> POP_ORW
      >> FULL_SIMP_TAC std_ss [IN_INSERT]
      >> METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty,IN_INSERT])
  >> `!x. x IN e INSERT s ==> (\x. f x + f' x) x <> PosInf` by METIS_TAC [add_not_infty]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY,DELETE_NON_ELEMENT]
  >> `EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
      f' e + (EXTREAL_SUM_IMAGE f' s + EXTREAL_SUM_IMAGE f s)`
         by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
  >> `f e + EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s) =
      f e + (EXTREAL_SUM_IMAGE f s + (f' e + EXTREAL_SUM_IMAGE f' s))`
         by METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty, IN_INSERT]
  >> POP_ORW >> POP_ORW
  >> FULL_SIMP_TAC std_ss [IN_INSERT]
  >> METIS_TAC [add_comm,add_assoc,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty,IN_INSERT]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_SUB = store_thm
  ("EXTREAL_SUM_IMAGE_SUB",
  ``!s. FINITE s ==>
        !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> PosInf) \/
                (!x. x IN s ==> f x <> PosInf /\ f' x <> NegInf)) ==>
               (EXTREAL_SUM_IMAGE (\x. f x - f' x) s =
                EXTREAL_SUM_IMAGE f s - EXTREAL_SUM_IMAGE f' s)``,
  Suff `!s. FINITE s ==>
        (\s. !f f'. ((!x. x IN s ==> f x <> NegInf /\ f' x <> PosInf) \/
                   (!x. x IN s ==> f x <> PosInf /\ f' x <> NegInf)) ==>
                (EXTREAL_SUM_IMAGE (\x. f x - f' x) s =
                 EXTREAL_SUM_IMAGE f s - EXTREAL_SUM_IMAGE f' s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY,sub_rzero]
  >- (`FINITE (e INSERT s)` by FULL_SIMP_TAC std_ss [FINITE_INSERT]
      >> (MP_TAC o Q.SPEC `(\x. f x - f' x)` o UNDISCH o Q.SPEC `e INSERT  s`) EXTREAL_SUM_IMAGE_IN_IF
      >> `!x. x IN e INSERT s ==> (\x. f x - f' x) x <> NegInf`
          by RW_TAC std_ss [sub_not_infty]
      >> `EXTREAL_SUM_IMAGE f (e INSERT s) <> NegInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
      >> `EXTREAL_SUM_IMAGE f' (e INSERT s) <> PosInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
      >> RW_TAC std_ss [extreal_sub_add]
      >> `-EXTREAL_SUM_IMAGE f' (e INSERT s) = Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s)`
            by METIS_TAC [neg_minus1,extreal_of_num_def,extreal_ainv_def]
      >> POP_ORW
      >> `Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s) =
          EXTREAL_SUM_IMAGE (\x. Normal (-1) * f' x) (e INSERT s)` by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL]
      >> RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def,GSYM neg_minus1]
      >> `(\x. if x IN e INSERT s then f x + -f' x else 0) =
          (\x. if x IN e INSERT s then (\x. f x + -f' x) x else 0)` by METIS_TAC []
      >> POP_ORW
      >> (MP_TAC o Q.SPEC `(\x. f x + -f' x)` o UNDISCH o Q.SPEC `e INSERT s ` o GSYM)
           EXTREAL_SUM_IMAGE_IN_IF
      >> RW_TAC std_ss []
      >> `!x. x IN e INSERT s ==> NegInf <> f x + -f' x` by METIS_TAC [extreal_sub_add]
      >> FULL_SIMP_TAC std_ss []
      >> `(\x. f x + -f' x) = (\x. f x + (\x. -f' x) x)` by METIS_TAC []
      >> POP_ORW
      >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `e INSERT s`) EXTREAL_SUM_IMAGE_ADD
      >> DISJ1_TAC
      >> RW_TAC std_ss []
      >> Cases_on `f' x`
      >> METIS_TAC [extreal_ainv_def,extreal_not_infty])
  >> `FINITE (e INSERT s)` by FULL_SIMP_TAC std_ss [FINITE_INSERT]
  >> (MP_TAC o Q.SPEC `(\x. f x - f' x)` o UNDISCH o Q.SPEC `e INSERT  s`) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x. x IN e INSERT s ==> (\x. f x - f' x) x <> PosInf`
        by RW_TAC std_ss [sub_not_infty]
  >> `EXTREAL_SUM_IMAGE f (e INSERT s) <> PosInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
  >> `EXTREAL_SUM_IMAGE f' (e INSERT s) <> NegInf` by METIS_TAC [IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY]
  >> RW_TAC std_ss [extreal_sub_add]
  >> `-EXTREAL_SUM_IMAGE f' (e INSERT s) = Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s)`
        by METIS_TAC [neg_minus1,extreal_of_num_def,extreal_ainv_def]
  >> POP_ORW
  >> `Normal (-1) * EXTREAL_SUM_IMAGE f' (e INSERT s) =
      EXTREAL_SUM_IMAGE (\x. Normal (-1) * f' x) (e INSERT s)` by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL]
  >> RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def,GSYM neg_minus1]
  >> `(\x. if x IN e INSERT s then f x + -f' x else 0) =
      (\x. if x IN e INSERT s then (\x. f x + -f' x) x else 0)` by METIS_TAC []
  >> POP_ORW
  >> (MP_TAC o Q.SPEC `(\x. f x + -f' x)` o UNDISCH o Q.SPEC `e INSERT s ` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
  >> RW_TAC std_ss []
  >> `!x. x IN e INSERT s ==> PosInf <> f x + -f' x` by METIS_TAC [extreal_sub_add]
  >> FULL_SIMP_TAC std_ss []
  >> `(\x. f x + -f' x) = (\x. f x + (\x. -f' x) x)` by METIS_TAC []
  >> POP_ORW
  >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `e INSERT s`) EXTREAL_SUM_IMAGE_ADD
  >> DISJ2_TAC
  >> RW_TAC std_ss []
  >> Cases_on `f' x`
  >> METIS_TAC [extreal_ainv_def,extreal_not_infty]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_SUM_IMAGE = store_thm
  ("EXTREAL_SUM_IMAGE_SUM_IMAGE",
  ``!s s' f. FINITE s /\ FINITE s' /\
             ((!x. x IN s CROSS s' ==> f (FST x) (SND x) <> NegInf) \/
              (!x. x IN s CROSS s' ==> f (FST x) (SND x) <> PosInf)) ==>
             (EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
              EXTREAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))``,
    Suff `!s. FINITE s ==>
             (\s. !s' f. FINITE s' /\
                       ((!x. x IN s CROSS s' ==> f (FST x) (SND x) <> NegInf) \/
                        (!x. x IN s CROSS s' ==> f (FST x) (SND x) <> PosInf)) ==>
                 (EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
                  EXTREAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [CROSS_EMPTY, EXTREAL_SUM_IMAGE_EMPTY, DELETE_NON_ELEMENT] (* 2 subgoals *)
 >> `((e INSERT s) CROSS s') = (IMAGE (\x. (e,x)) s') UNION (s CROSS s')`
        by (RW_TAC std_ss [Once EXTENSION, IN_INSERT, IN_SING, IN_CROSS, IN_UNION, IN_IMAGE]
            >> Cases_on `x`
            >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [FST,SND, GSYM DELETE_NON_ELEMENT]
            >> METIS_TAC []) >> POP_ORW
 >> `DISJOINT (IMAGE (\x. (e,x)) s') (s CROSS s')`
        by (FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, Once EXTENSION,
                                  NOT_IN_EMPTY, IN_INTER, IN_CROSS, IN_SING, IN_IMAGE]
            >> STRIP_TAC >> Cases_on `x`
            >> RW_TAC std_ss [FST, SND]
            >> METIS_TAC [])
 >> `FINITE (IMAGE (\x. (e,x)) s')` by RW_TAC std_ss [IMAGE_FINITE]
 >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
 >> (MP_TAC o Q.SPEC `(\x. f (FST x) (SND x))` o UNDISCH o UNDISCH o UNDISCH o
       REWRITE_RULE [GSYM AND_IMP_INTRO] o
       Q.ISPECL [`IMAGE (\x. (e:'a,x)) (s':'b->bool)`,
                 `(s:'a->bool) CROSS (s':'b->bool)`]) EXTREAL_SUM_IMAGE_DISJOINT_UNION
 >| [ `(!x. x IN IMAGE (\x. (e,x)) s' UNION s CROSS s' ==> f (FST x) (SND x) <> NegInf)`
          by (FULL_SIMP_TAC std_ss [IN_IMAGE,IN_UNION, IN_INSERT, IN_CROSS]
              >> METIS_TAC [FST, SND]),
      `(!x. x IN IMAGE (\x. (e,x)) s' UNION s CROSS s' ==> f (FST x) (SND x) <> PosInf)`
          by (FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNION, IN_INSERT, IN_CROSS]
              >> METIS_TAC [FST, SND]) ]
 >> RW_TAC std_ss []
 >> `INJ (\x. (e,x)) s' (IMAGE (\x. (e,x)) s')` by RW_TAC std_ss [INJ_DEF, IN_IMAGE]
 >> (MP_TAC o Q.SPEC `(\x. f (FST x) (SND x))` o UNDISCH o Q.SPEC `(\x. (e,x))` o
       UNDISCH o Q.SPEC `s'` o
       INST_TYPE [``:'c``|->``:'a # 'b``] o INST_TYPE [``:'a``|->``:'b``] o
       INST_TYPE [``:'b``|->``:'c``]) EXTREAL_SUM_IMAGE_IMAGE
 >| [ `!x. x IN IMAGE (\x. (e,x)) s' ==> (\x. f (FST x) (SND x)) x <> NegInf`
          by FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNION, IN_INSERT, IN_CROSS],
      `!x. x IN IMAGE (\x. (e,x)) s' ==> (\x. f (FST x) (SND x)) x <> PosInf`
          by FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNION, IN_INSERT, IN_CROSS] ]
 >> RW_TAC std_ss [o_DEF]
 >| [ `!x. x IN e INSERT s ==> (\x. EXTREAL_SUM_IMAGE (f x) s') x <> NegInf`
        by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT, IN_CROSS, FST, SND],
      `!x. x IN e INSERT s ==> (\x. EXTREAL_SUM_IMAGE (f x) s') x <> PosInf`
        by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, IN_INSERT, IN_CROSS, FST, SND] ]
 >> (MP_TAC o Q.SPEC `e` o UNDISCH o
       Q.SPECL [`(\x. EXTREAL_SUM_IMAGE (f x) s')`,`s`]) EXTREAL_SUM_IMAGE_PROPERTY
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [IN_INSERT, IN_IMAGE, IN_UNION]
 >> METIS_TAC [FUN_EQ_THM]);

val EXTREAL_SUM_IMAGE_NORMAL = store_thm
  ("EXTREAL_SUM_IMAGE_NORMAL",
  ``!f s. FINITE s ==> (EXTREAL_SUM_IMAGE (\x. Normal (f x)) s = Normal (SIGMA f s))``,
    Suff `!s. FINITE s ==>
             (\s. !f. EXTREAL_SUM_IMAGE (\x. Normal (f x)) s = Normal (SIGMA f s) ) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, REAL_SUM_IMAGE_THM, extreal_of_num_def,
                   REAL_SUM_IMAGE_THM, GSYM extreal_add_def]
 >> (MP_TAC o UNDISCH o Q.SPECL [`(\x. Normal (f x))`,`s`]) EXTREAL_SUM_IMAGE_PROPERTY
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT, extreal_not_infty]);

(* more antecedents added *)
val EXTREAL_SUM_IMAGE_IN_IF_ALT = store_thm
  ("EXTREAL_SUM_IMAGE_IN_IF_ALT",
  ``!s f z. FINITE s /\ ((!x. x IN s ==> f x <> NegInf) \/
                         (!x. x IN s ==> f x <> PosInf)) ==>
           (EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s)``,
    Suff `!s. FINITE s ==>
             (\s. !f z. ((!x. x IN s ==> f x <> NegInf) \/ (!x. x IN s ==> f x <> PosInf)) ==>
                        (EXTREAL_SUM_IMAGE f s =
                         EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY]
 >- (`!i. i IN e INSERT s ==> (\x. if x IN e INSERT s then f x else z) i <> NegInf`
       by RW_TAC std_ss []
     >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]) (* 2 sub-goals here *)
     >> FULL_SIMP_TAC std_ss [IN_INSERT]                     (* 1 remains *)
     >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
     >> Suff `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN e INSERT s then f x else z) s`
     >- RW_TAC std_ss [IN_INSERT]
     >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s`
          by METIS_TAC [IN_INSERT]
     >> POP_ORW
     >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_EQ
     >> RW_TAC std_ss [IN_INSERT])
 >> `!i. i IN e INSERT s ==> (\x. if x IN e INSERT s then f x else z) i <> PosInf` by RW_TAC std_ss []
 >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY])
 >- FULL_SIMP_TAC std_ss [IN_INSERT]
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
 >> Suff `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN e INSERT s then f x else z) s`
 >- RW_TAC std_ss []
 >> `EXTREAL_SUM_IMAGE f s = EXTREAL_SUM_IMAGE (\x. if x IN s then f x else z) s`
       by METIS_TAC [IN_INSERT]
 >> POP_ORW
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_EQ
 >> RW_TAC std_ss [IN_INSERT]);

(* TODO
val EXTREAL_SUM_IMAGE_CROSS_SYM = store_thm
  ("EXTREAL_SUM_IMAGE_CROSS_SYM",
  ``!f s1 s2. FINITE s1 /\ FINITE s2 /\
             ((!s. s IN (s1 CROSS s2) ==> f s <> NegInf) \/
              (!s. s IN (s1 CROSS s2) ==> f s <> PosInf)) ==>
             (EXTREAL_SUM_IMAGE (\(x,y). f (x,y)) (s1 CROSS s2) =
              EXTREAL_SUM_IMAGE (\(y,x). f (x,y)) (s2 CROSS s1))``,
  RW_TAC std_ss []
  >> `s2 CROSS s1 = IMAGE (\a. (SND a, FST a)) (s1 CROSS s2)`
        by (RW_TAC std_ss [IN_IMAGE, IN_CROSS, EXTENSION] >> METIS_TAC [FST,SND,PAIR])
  >> POP_ORW
  >> `INJ (\a. (SND a, FST a)) (s1 CROSS s2) (IMAGE (\a. (SND a, FST a)) (s1 CROSS s2))`
       by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_CROSS]
           >> METIS_TAC [FST,SND,PAIR])
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, FINITE_CROSS, o_DEF]
  >> `(\(x,y). f (x,y)) = (\a. f a)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `a`
           >> RW_TAC std_ss [])
  >> RW_TAC std_ss []);
 *)

val EXTREAL_SUM_IMAGE_COUNT = store_thm
  ("EXTREAL_SUM_IMAGE_COUNT",
  ``!f. (!x. f x <> PosInf) \/ (!x. f x <> NegInf) ==>
        (EXTREAL_SUM_IMAGE f (count 2) = f 0 + f 1) /\
        (EXTREAL_SUM_IMAGE f (count 3) = f 0 + f 1 + f 2) /\
        (EXTREAL_SUM_IMAGE f (count 4) = f 0 + f 1 + f 2 + f 3) /\
        (EXTREAL_SUM_IMAGE f (count 5) = f 0 + f 1 + f 2 + f 3 + f 4)``,
    RW_TAC std_ss []
 >> `count 2 = {0;1}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
 >> `count 3 = {0;1;2}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
 >> `count 4 = {0;1;2;3}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
 >> `count 5 = {0;1;2;3;4}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_INSERT, IN_SING]
 >> `{1:num} DELETE 0 = {1}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{2:num} DELETE 1 = {2}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{3:num} DELETE 2 = {3}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{4:num} DELETE 3 = {4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING]
 >> `{2:num; 3} DELETE 1 = {2;3}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{3:num; 4} DELETE 2 = {3;4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{2:num; 3; 4} DELETE 1 = {2;3;4}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{1:num; 2} DELETE 0 = {1;2}` by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> `{1:num; 2; 3} DELETE 0 = {1;2;3}` by RW_TAC real_ss [EXTENSION, IN_DELETE,IN_SING,IN_INSERT]
 >> `{1:num; 2; 3; 4} DELETE 0 = {1;2;3;4}`
     by RW_TAC real_ss [EXTENSION, IN_DELETE, IN_SING, IN_INSERT]
 >> FULL_SIMP_TAC real_ss [FINITE_SING, FINITE_INSERT, EXTREAL_SUM_IMAGE_INSERT,
                           EXTREAL_SUM_IMAGE_SING, IN_INSERT, NOT_IN_EMPTY,
                           add_assoc, add_not_infty]
 >> DECIDE_TAC);

val _ = overload_on ("SIGMA", ``EXTREAL_SUM_IMAGE``);

(* N-ARY SUMMATION *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x2211, tmnm = "SIGMA"};

val NESTED_EXTREAL_SUM_IMAGE_REVERSE = store_thm (* need a version for PosInf *)
  ("NESTED_EXTREAL_SUM_IMAGE_REVERSE",
  ``!f s s'. FINITE s /\ FINITE s' /\
            (!x y. x IN s /\ y IN s' ==> f x y <> NegInf) ==>
            (EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (f x) s') s =
             EXTREAL_SUM_IMAGE (\x. EXTREAL_SUM_IMAGE (\y. f y x) s) s')``,
    rpt STRIP_TAC
 >> Know `SIGMA (\x. SIGMA (f x) s') s =
          SIGMA (\x. f (FST x) (SND x)) (s CROSS s')`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     ASM_REWRITE_TAC [IN_CROSS]) >> Rewr'
 >> Know `SIGMA (\x. SIGMA ((\x y. f y x) x) s) s' =
          SIGMA (\x. (\x y. f y x) (FST x) (SND x)) (s' CROSS s)`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     BETA_TAC >> ASM_REWRITE_TAC [IN_CROSS] >> PROVE_TAC [])
 >> BETA_TAC >> Rewr'
 >> Know `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
 >- (RW_TAC std_ss [EXTENSION, IN_CROSS, IN_IMAGE] \\
     EQ_TAC >- (STRIP_TAC >> Q.EXISTS_TAC `(SND x, FST x)` >> RW_TAC std_ss [PAIR]) \\
     RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND]) >> Rewr'
 >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
 >> `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
       by (RW_TAC std_ss [INJ_DEF, IN_IMAGE] >- METIS_TAC [] \\
           METIS_TAC [PAIR, PAIR_EQ])
 >> Know `SIGMA (\x. f (SND x) (FST x)) (IMAGE (\x. (SND x,FST x)) (s CROSS s')) =
          SIGMA ((\x. f (SND x) (FST x)) o (\x. (SND x,FST x))) (s CROSS s')`
 >- (irule EXTREAL_SUM_IMAGE_IMAGE >> art [] \\
     DISJ1_TAC >> RW_TAC std_ss [IN_IMAGE, IN_CROSS] \\
     RW_TAC std_ss [FST, SND])
 >> Rewr' >> RW_TAC std_ss [o_DEF]);

val EXTREAL_SUM_IMAGE_SUM_IMAGE_MONO = store_thm
  ("EXTREAL_SUM_IMAGE_SUM_IMAGE_MONO",
 ``!(f :num -> num -> extreal) a b c d.
        (!m n. 0 <= f m n) /\ a <= c /\ b <= d ==>
        SIGMA (\i. SIGMA (f i) (count a)) (count b) <=
        SIGMA (\i. SIGMA (f i) (count c)) (count d)``,
    rpt STRIP_TAC >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `SIGMA (\i. SIGMA (f i) (count a)) (count d)`
 >> CONJ_TAC
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     SIMP_TAC arith_ss [FINITE_COUNT] \\
     CONJ_TAC >- (MATCH_MP_TAC COUNT_MONO >> RW_TAC arith_ss []) \\
     GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> PROVE_TAC [FINITE_COUNT])
 >> irule EXTREAL_SUM_IMAGE_MONO
 >> SIMP_TAC arith_ss [FINITE_COUNT]
 >> CONJ_TAC
 >- (GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     SIMP_TAC arith_ss [FINITE_COUNT] \\
     CONJ_TAC >- (MATCH_MP_TAC COUNT_MONO >> RW_TAC arith_ss []) \\
     PROVE_TAC [])
 >> DISJ1_TAC >> GEN_TAC >> DISCH_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> RW_TAC std_ss [FINITE_COUNT])
 >> MATCH_MP_TAC pos_not_neginf
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
 >> RW_TAC std_ss [FINITE_COUNT]);

val EXTREAL_SUM_IMAGE_POW = store_thm
  ("EXTREAL_SUM_IMAGE_POW",
  ``!f s. FINITE s ==>
        ((!x. x IN s ==> f x <> NegInf) /\ (!x. x IN s ==> f x <> PosInf)) ==>
        ((EXTREAL_SUM_IMAGE f s) pow 2 =
          EXTREAL_SUM_IMAGE (\(i,j). f i * f j) (s CROSS s))``,
    rpt STRIP_TAC
 >> `(\(i,j). f i * f j) = (\x. (\i j. f i * f j) (FST x) (SND x))`
       by (RW_TAC std_ss [FUN_EQ_THM] \\
           Cases_on `x` >> RW_TAC std_ss []) >> POP_ORW
 >> (MP_TAC o Q.SPECL [`s`,`s`,`(\i j. f i * f j)`] o INST_TYPE [``:'b`` |-> ``:'a``])
       EXTREAL_SUM_IMAGE_SUM_IMAGE >> art []
 >> Know `((!x. x IN s CROSS s ==> (\i j. f i * f j) (FST x) (SND x) <> NegInf) \/
           (!x. x IN s CROSS s ==> (\i j. f i * f j) (FST x) (SND x) <> PosInf))`
 >- (RW_TAC std_ss [IN_CROSS] \\
     DISJ1_TAC >> RW_TAC std_ss [] \\
    `f (FST x) <> NegInf /\ f (SND x) <> NegInf` by PROVE_TAC [] \\
     METIS_TAC [mul_not_infty2])
 >> SIMP_TAC std_ss [] >> DISCH_TAC
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o GSYM)
 >> Know `!x. x IN s ==> SIGMA (\j. f x * f j) s = f x * SIGMA f s`
 >- (rpt STRIP_TAC >> `?c. f x = Normal c` by PROVE_TAC [extreal_cases] >> art [] \\
     ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_CMUL]) >> DISCH_TAC
 >> Know `SIGMA (\x. SIGMA (\j. f x * f j) s) s = SIGMA (\x. f x * (SIGMA f s)) s`
 >- (irule EXTREAL_SUM_IMAGE_EQ >> ASM_SIMP_TAC std_ss [] \\
     DISJ2_TAC >> GEN_TAC >> DISCH_TAC \\
    `f x <> PosInf /\ f x <> NegInf` by PROVE_TAC [] \\
     Suff `SIGMA f s <> PosInf /\ SIGMA f s <> NegInf` >- METIS_TAC [mul_not_infty2] \\
     ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]) >> Rewr'
 >> `SIGMA f s <> PosInf /\ SIGMA f s <> NegInf`
      by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY]
 >> `?c. SIGMA f s = Normal c` by PROVE_TAC [extreal_cases] >> art []
 >> ONCE_REWRITE_TAC [mul_comm]
 >> Know `SIGMA (\x. Normal c * f x) s = Normal c * SIGMA f s`
 >- ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_CMUL]
 >> Rewr' >> art [pow_2]);

(* ------------------------------------------------------------------------- *)
(* Supremums and infimums (these are always defined on extended reals)       *)
(* ------------------------------------------------------------------------- *)

val extreal_sup_def = Define
   `extreal_sup p =
       if !x. (!y. p y ==> y <= x) ==> (x = PosInf) then PosInf
       else (if !x. p x ==> (x = NegInf) then NegInf
             else Normal (sup (\r. p (Normal r))))`;

val extreal_inf_def = Define
   `extreal_inf p = -extreal_sup (IMAGE numeric_negate p)`;

val _ = overload_on ("sup", Term `extreal_sup`);
val _ = overload_on ("inf", Term `extreal_inf`);

val le_sup_imp = store_thm
  ("le_sup_imp", ``!p x. p x ==> x <= sup p``,
    RW_TAC std_ss [extreal_sup_def, le_infty, le_refl]
 >> FULL_SIMP_TAC std_ss []
 >> Cases_on `x`
 >| [ RW_TAC std_ss [le_infty],
     `x' < PosInf` by (Cases_on `x'` >> RW_TAC std_ss [lt_infty]) \\
      METIS_TAC [let_trans, lt_refl],
      RW_TAC std_ss [extreal_le_def] \\
      MATCH_MP_TAC REAL_IMP_LE_SUP \\
      CONJ_TAC >- METIS_TAC [] \\
      reverse CONJ_TAC >- (Q.EXISTS_TAC `r` >> RW_TAC real_ss []) \\
      Cases_on `x'` >| (* 3 subgoals *)
      [ METIS_TAC [le_infty],
        RW_TAC std_ss [],
        Q.EXISTS_TAC `r'` \\
        RW_TAC std_ss [] \\
        METIS_TAC [extreal_le_def] ] ]);

val le_sup_imp' = store_thm
  ("le_sup_imp'", ``!p x. x IN p ==> x <= sup p``,
    REWRITE_TAC [IN_APP]
 >> PROVE_TAC [le_sup_imp]);

val sup_le = store_thm
  ("sup_le", ``!p x. sup p <= x <=> (!y. p y ==> y <= x)``,
    RW_TAC std_ss [extreal_sup_def, le_infty]
 >- (EQ_TAC >- RW_TAC std_ss [le_infty] >> METIS_TAC [])
 >> FULL_SIMP_TAC std_ss []
 >> Cases_on `x` (* 3 subgoals *)
 >| [ METIS_TAC [le_infty, extreal_not_infty],
      METIS_TAC [le_infty],
      Cases_on `x'` >| (* 3 gubgoals *)
      [ METIS_TAC [le_infty],
        RW_TAC std_ss [],
        RW_TAC std_ss [extreal_le_def] \\
        EQ_TAC
        >- (RW_TAC std_ss [] \\
            Cases_on `y` >|
            [ METIS_TAC [le_infty],
              METIS_TAC [le_infty,extreal_not_infty],
              RW_TAC std_ss [extreal_le_def] \\
              MATCH_MP_TAC REAL_LE_TRANS \\
              Q.EXISTS_TAC `sup (\r. p (Normal r))` \\
              RW_TAC std_ss [] \\
              MATCH_MP_TAC REAL_IMP_LE_SUP \\
              CONJ_TAC >- METIS_TAC [] \\
              reverse CONJ_TAC >- (Q.EXISTS_TAC `r''` >> RW_TAC real_ss []) \\
              Q.EXISTS_TAC `r'` \\
              RW_TAC std_ss [] \\
              METIS_TAC [extreal_le_def] ]) \\
        RW_TAC std_ss [] \\
        MATCH_MP_TAC REAL_IMP_SUP_LE \\
        RW_TAC std_ss []
        >- (Cases_on `x''` >| (* 3 subgoals *)
            [ RW_TAC std_ss [],
              METIS_TAC [le_infty, extreal_not_infty],
              METIS_TAC [] ]) \\
        METIS_TAC [extreal_le_def] ] ]);

Theorem sup_le' : (* was: Sup_le_iff *)
    !p x. sup p <= x <=> (!y. y IN p ==> y <= x)
Proof
    METIS_TAC [sup_le, SPECIFICATION]
QED
val Sup_le_iff = sup_le';

val le_sup = store_thm
  ("le_sup", ``!p x. x <= sup p <=> (!y. (!z. p z ==> z <= y) ==> x <= y)``,
    RW_TAC std_ss [extreal_sup_def,le_infty]
 >- (EQ_TAC >- RW_TAC std_ss [le_infty] >> METIS_TAC [le_infty, le_refl])
 >> FULL_SIMP_TAC std_ss []
 >> Cases_on `x'` (* 3 subgoals *)
 >| [ METIS_TAC [le_infty],
      METIS_TAC [le_infty],
      Cases_on `x` >| (* 3 subgoals *)
      [ METIS_TAC [le_infty],
        METIS_TAC [le_infty, extreal_not_infty],
        RW_TAC std_ss [extreal_le_def] \\
        EQ_TAC
        >- (RW_TAC std_ss [] \\
            Cases_on `y` >|
            [ METIS_TAC [le_infty],
              METIS_TAC [le_infty],
              RW_TAC std_ss [extreal_le_def] \\
              MATCH_MP_TAC REAL_LE_TRANS \\
              Q.EXISTS_TAC `sup (\r. p (Normal r))` \\
              RW_TAC std_ss [] \\
              MATCH_MP_TAC REAL_IMP_SUP_LE \\
              RW_TAC std_ss []
              >- (Cases_on `x''` >| (* 3 gubgoals *)
                  [ RW_TAC std_ss [],
                    METIS_TAC [le_infty, extreal_not_infty],
                    METIS_TAC [] ]) \\
              METIS_TAC [extreal_le_def] ]) \\
        RW_TAC std_ss [extreal_le_def] \\
       (MP_TAC o Q.SPECL [`(\r. p (Normal r))`,`r'`]) REAL_LE_SUP \\
        MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``) \\
        CONJ_TAC
        >- (RW_TAC std_ss []
            >- METIS_TAC [extreal_cases, le_infty, extreal_not_infty] \\
            METIS_TAC [extreal_le_def]) \\
            RW_TAC std_ss [] \\
            Q.PAT_X_ASSUM `!y. (!z. p z ==> z <= y) ==> Normal r' <= y`
                (MATCH_MP_TAC o REWRITE_RULE [extreal_le_def] o Q.SPEC `Normal y`) \\
            Cases >| (* 3 subgoals *)
            [ METIS_TAC [le_infty],
              METIS_TAC [le_infty, extreal_not_infty],
              METIS_TAC [extreal_le_def] ] ] ]);

val le_sup' = store_thm
  ("le_sup'", ``!p x. x <= sup p <=> !y. (!z. z IN p ==> z <= y) ==> x <= y``,
    REWRITE_TAC [IN_APP]
 >> REWRITE_TAC [le_sup]);

val le_sup_imp2 = store_thm
  ("le_sup_imp2", ``!p z. (?x. x IN p) /\ (!x. x IN p ==> z <= x) ==> z <= sup p``,
    RW_TAC std_ss [le_sup']
 >> MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `x`
 >> CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art []);

val sup_eq = store_thm
  ("sup_eq", ``!p x. (sup p = x) <=>
                     (!y. p y ==> y <= x) /\ !y. (!z. p z ==> z <= y) ==> x <= y``,
    METIS_TAC [le_antisym, le_sup, sup_le]);

val sup_eq' = store_thm
  ("sup_eq'",
  ``!p x. (sup p = x) <=>
          (!y. y IN p ==> y <= x) /\ !y. (!z. z IN p ==> z <= y) ==> x <= y``,
    REWRITE_TAC [IN_APP]
 >> METIS_TAC [le_antisym, le_sup, sup_le]);

val sup_const = store_thm
  ("sup_const", ``!x. sup (\y. y = x) = x``,
    RW_TAC real_ss [sup_eq, le_refl]);

Theorem sup_sing :
    !a:extreal. sup {a} = a
Proof
    REWRITE_TAC [METIS [EXTENSION, IN_SING, IN_DEF] ``{a} = (\x. x = a)``]
 >> SIMP_TAC std_ss [sup_const]
QED

val sup_const_alt = store_thm
  ("sup_const_alt", ``!p z. (?x. p x) /\ (!x. p x ==> (x = z)) ==> (sup p = z)``,
    RW_TAC std_ss [sup_eq,le_refl]
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss []);

val sup_const_alt' = store_thm
  ("sup_const_alt'",
  ``!p z. (?x. x IN p) /\ (!x. x IN p ==> (x = z)) ==> (sup p = z)``,
    RW_TAC std_ss [sup_eq,le_refl,IN_APP]
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss []);

val sup_const_over_set = store_thm
  ("sup_const_over_set", ``!s k. s <> {} ==> (sup (IMAGE (\x. k) s) = k)``,
    RW_TAC std_ss [sup_eq]
 >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) \\
     RW_TAC std_ss [IN_IMAGE] >> RW_TAC std_ss [le_refl])
 >> POP_ASSUM MATCH_MP_TAC
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> RW_TAC std_ss [IN_IMAGE]
 >> METIS_TAC [CHOICE_DEF]);

val sup_const_over_univ = store_thm
  ("sup_const_over_univ", ``!k. sup (IMAGE (\x. k) UNIV) = k``,
    GEN_TAC >> MATCH_MP_TAC sup_const_over_set
 >> SET_TAC []);

val sup_num = store_thm
  ("sup_num", ``sup (\x. ?n :num. x = &n) = PosInf``,
    RW_TAC std_ss [GSYM le_infty,le_sup]
 >> Cases_on `y`
 >| [ POP_ASSUM (MP_TAC o Q.SPEC `0`) \\
      RW_TAC real_ss [le_infty, extreal_of_num_def, extreal_not_infty],
      RW_TAC std_ss [le_refl],
      RW_TAC std_ss [le_infty, extreal_not_infty] \\
      MP_TAC (Q.SPEC `r` REAL_BIGNUM) \\
      PURE_REWRITE_TAC [real_lt] \\
      STRIP_TAC \\
      Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `&n`) \\
      RW_TAC std_ss [extreal_of_num_def] >- METIS_TAC [] \\
      METIS_TAC [extreal_le_def] ]);

val sup_le_sup_imp = store_thm
  ("sup_le_sup_imp",
  ``!p q. (!x. p x ==> ?y. q y /\ x <= y) ==> sup p <= sup q``,
    RW_TAC std_ss [sup_le]
 >> METIS_TAC [le_trans, le_sup_imp]);

val sup_le_sup_imp' = store_thm
  ("sup_le_sup_imp'",
  ``!p q. (!x. x IN p ==> ?y. y IN q /\ x <= y) ==> sup p <= sup q``,
    REWRITE_TAC [IN_APP]
 >> PROVE_TAC [sup_le_sup_imp]);

val sup_mono = store_thm
  ("sup_mono",
  ``!p q. (!n:num. p n <= q n) ==> sup (IMAGE p UNIV) <= sup (IMAGE q UNIV)``,
    RW_TAC std_ss [sup_le,le_sup]
 >> Q.PAT_X_ASSUM `IMAGE p UNIV y` (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
 >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `q x`
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!z. Q ==> z <= y'` MATCH_MP_TAC
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
 >> METIS_TAC []);

(* This is more general than "sup_mono", as f <= g in arbitrary order *)
Theorem sup_mono_ext : (* was: SUP_mono *)
    !f g A B. (!n. n IN A ==> ?m. m IN B /\ f n <= g m) ==>
              sup {f n | n IN A} <= sup {g n | n IN B}
Proof
  RW_TAC std_ss [] THEN MATCH_MP_TAC sup_le_sup_imp THEN
  GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `g m` THEN
  GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN ASM_SET_TAC []
QED

val sup_mono_subset = store_thm
  ("sup_mono_subset", ``!p q. p SUBSET q ==> extreal_sup p <= extreal_sup q``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC sup_le_sup_imp
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC `x`
 >> REWRITE_TAC [le_refl]
 >> PROVE_TAC [SUBSET_DEF, IN_APP]);

val inf_mono_subset = store_thm
  ("inf_mono_subset", ``!p q. p SUBSET q ==> extreal_inf q <= extreal_inf p``,
    rpt STRIP_TAC
 >> REWRITE_TAC [extreal_inf_def, le_neg]
 >> MATCH_MP_TAC sup_mono_subset
 >> PROVE_TAC [IMAGE_SUBSET]);

val sup_suc = store_thm
  ("sup_suc", ``!f. (!m n. m <= n ==> f m <= f n) ==>
                    (sup (IMAGE (\n. f (SUC n)) UNIV) = sup (IMAGE f UNIV))``,
    RW_TAC std_ss [sup_eq, sup_le, le_sup]
 >- (POP_ASSUM MATCH_MP_TAC \\
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
     POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     METIS_TAC [])
 >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
 >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
 >> Cases_on `x`
 >- (MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `f 1` \\
     RW_TAC std_ss [] \\
     POP_ASSUM MATCH_MP_TAC \\
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
    `SUC 0 = 1` by RW_TAC real_ss [] \\
     METIS_TAC [])
 >> POP_ASSUM MATCH_MP_TAC
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> METIS_TAC []);

val sup_shift = store_thm
  ("sup_shift",
  ``!f :num -> extreal.
      (!m n. m <= n ==> f m <= f n) ==>
       !N. (sup (IMAGE (\n. f (n + N)) UNIV) = sup (IMAGE f UNIV))``,
    GEN_TAC >> DISCH_TAC
 >> Induct_on `N` >- RW_TAC arith_ss [ETA_THM]
 >> Know `(\n. f (n + SUC N)) = (\n. (\n. f (n + N)) (SUC n))`
 >- (FUN_EQ_TAC >> RW_TAC arith_ss [ADD_CLAUSES]) >> Rewr'
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC sup_suc
 >> RW_TAC std_ss []);

val sup_seq = store_thm
  ("sup_seq",
  ``!f l. mono_increasing f ==>
         ((f --> l) <=> (sup (IMAGE (\n. Normal (f n)) UNIV) = Normal l))``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- (RW_TAC std_ss [sup_eq]
      >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> RW_TAC std_ss [extreal_le_def]
          >> METIS_TAC [mono_increasing_suc, SEQ_MONO_LE, ADD1])
      >> `!n. Normal (f n) <= y`
            by (RW_TAC std_ss []
                >> POP_ASSUM MATCH_MP_TAC
                >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
                >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
                >> METIS_TAC [])
      >> Cases_on `y`
      >| [METIS_TAC [le_infty, extreal_not_infty],
          METIS_TAC [le_infty],
          METIS_TAC [SEQ_LE_IMP_LIM_LE,extreal_le_def]])
  >> RW_TAC std_ss [extreal_sup_def]
  >> `(\r. IMAGE (\n. Normal (f n)) UNIV (Normal r)) = IMAGE f UNIV`
       by (RW_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE, IN_UNIV]
           >> EQ_TAC
           >> (RW_TAC std_ss []
               >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
               >> RW_TAC std_ss [IN_IMAGE, IN_UNIV])
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV, IN_IMAGE]
           >> METIS_TAC [])
  >> POP_ORW
  >> FULL_SIMP_TAC std_ss []
  >> `!n. Normal (f n) <= x`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!y. P` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
           >> METIS_TAC [])
  >> `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans]
  >> `?z. x = Normal z` by METIS_TAC [extreal_cases]
  >> `!n. f n <= z` by FULL_SIMP_TAC std_ss [extreal_le_def]
  >> RW_TAC std_ss [SEQ]
  >> (MP_TAC o Q.ISPECL [`IMAGE (f:num->real) UNIV`,`e:real/2`]) SUP_EPSILON
  >> SIMP_TAC std_ss [REAL_LT_HALF1]
  >> `!y x z. IMAGE f UNIV x <=> x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
  >> POP_ORW
  >> Know `(?z. !x. x IN IMAGE f UNIV ==> x <= z)`
  >- (Q.EXISTS_TAC `z`
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [])
  >> `?x. x IN IMAGE f UNIV` by RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  >> RW_TAC std_ss []
  >> `?x. x IN IMAGE f univ(:num) /\ sup (IMAGE f univ(:num)) <= x + e / 2` by METIS_TAC []
  >> RW_TAC std_ss [GSYM ABS_BETWEEN, GREATER_EQ]
  >> FULL_SIMP_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> Q.EXISTS_TAC `x''''''`
  >> RW_TAC std_ss [REAL_LT_SUB_RADD]
  >- (MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f x'''''' + e / 2`
      >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LET_TRANS
      >> Q.EXISTS_TAC `f n + e / 2`
      >> reverse CONJ_TAC >- METIS_TAC [REAL_LET_ADD2,REAL_LT_HALF2,REAL_LE_REFL]
      >> RW_TAC std_ss [REAL_LE_RADD]
      >> METIS_TAC [mono_increasing_def])
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `sup (IMAGE f UNIV)`
   >> RW_TAC std_ss [REAL_LT_ADDR]
   >> Suff `!y. (\y. y IN IMAGE f UNIV) y ==> y <= sup (IMAGE f UNIV)`
   >- METIS_TAC [IN_IMAGE, IN_UNIV]
   >> SIMP_TAC std_ss [IN_DEF]
   >> MATCH_MP_TAC REAL_SUP_UBOUND_LE
   >> `!y x z. IMAGE f UNIV x <=> x IN IMAGE f UNIV` by RW_TAC std_ss [IN_DEF]
   >> POP_ORW
   >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   >> Q.EXISTS_TAC `z'`
   >> RW_TAC std_ss []);

val sup_lt_infty = store_thm
  ("sup_lt_infty", ``!p. (sup p < PosInf) ==> (!x. p x ==> x < PosInf)``,
    METIS_TAC [le_sup_imp,let_trans]);

val sup_max = store_thm
  ("sup_max", ``!p z. p z /\ (!x. p x ==> x <= z) ==> (sup p = z)``,
    RW_TAC std_ss [sup_eq]);

val sup_add_mono = store_thm
  ("sup_add_mono",
  ``!f g. (!n. 0 <= f n) /\ (!n. f n <= f (SUC n)) /\
          (!n. 0 <= g n) /\ (!n. g n <= g (SUC n)) ==>
          (sup (IMAGE (\n. f n + g n) UNIV) = sup (IMAGE f UNIV) + sup (IMAGE g UNIV))``,
 (* new proof *)
  RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> MATCH_MP_TAC le_add2
      >> RW_TAC std_ss [le_sup]
      >> POP_ASSUM MATCH_MP_TAC
      >> METIS_TAC [SPECIFICATION,IN_IMAGE,IN_UNIV])
  >> Cases_on `y = PosInf` >- RW_TAC std_ss [le_infty]
  >> Cases_on `sup (IMAGE f UNIV) = 0`
  >- (RW_TAC std_ss [sup_le, add_lzero]
      >> FULL_SIMP_TAC std_ss [sup_eq]
      >> `!n. f n = 0` by METIS_TAC [EXTENSION, IN_IMAGE, IN_UNIV, SPECIFICATION, le_antisym]
      >> Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
      >> RW_TAC std_ss [add_lzero]
      >> METIS_TAC [])
  >> Cases_on `sup (IMAGE g UNIV) = 0`
  >- (RW_TAC std_ss [sup_le, add_rzero]
      >> FULL_SIMP_TAC std_ss [sup_eq]
      >> `!n. g n = 0` by METIS_TAC [EXTENSION, IN_IMAGE, IN_UNIV, SPECIFICATION, le_antisym]
      >> Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
      >> RW_TAC std_ss [add_rzero]
      >> METIS_TAC [])
  >> `!n. f n + g n <= y`
       by (RW_TAC std_ss []
           >> Q.PAT_ASSUM `!z. Q z ==> P z` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
           >> METIS_TAC [])
  >> `!n. g n <= f n + g n` by METIS_TAC [add_lzero, le_add2, le_refl]
  >> `!n. f n <= f n + g n` by METIS_TAC [add_rzero, le_add2, le_refl]
  >> `!n. g n <> PosInf` by METIS_TAC [le_trans, lt_infty, let_trans]
  >> `!n. g n <> NegInf` by METIS_TAC [le_trans, le_infty, lt_infty, lte_trans,
                                       extreal_of_num_def, extreal_not_infty]
  >> `!n. f n <> PosInf` by METIS_TAC [le_trans, lt_infty, let_trans]
  >> `!n. f n <> NegInf` by METIS_TAC [le_trans, le_infty, lt_infty, lte_trans,
                                       extreal_of_num_def, extreal_not_infty]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `sup (IMAGE (\n. (sup (IMAGE f UNIV)) + g n) UNIV)`
  >> reverse (RW_TAC std_ss [sup_le])
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> Suff `sup (IMAGE f UNIV) <= y - g n` >- RW_TAC std_ss [le_sub_eq]
      >> RW_TAC std_ss [sup_le]
      >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> MATCH_MP_TAC le_sub_imp
      >> RW_TAC std_ss []
      >> Cases_on `x <= n`
      >- (MATCH_MP_TAC le_trans
          >> Q.EXISTS_TAC `f n + g n`
          >> CONJ_TAC >- METIS_TAC [le_radd, ext_mono_increasing_def, ext_mono_increasing_suc]
          >> Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
      >> MATCH_MP_TAC le_trans
      >> Q.EXISTS_TAC `f x + g x`
      >> CONJ_TAC >- METIS_TAC [le_ladd, ext_mono_increasing_def, ext_mono_increasing_suc,
                                le_refl, NOT_LEQ, le_trans]
      >> Q.PAT_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [])
  >> `sup (IMAGE f UNIV) <> NegInf`
        by (RW_TAC std_ss [sup_eq,le_infty]
            >> Q.EXISTS_TAC `f (CHOICE (UNIV:num->bool))`
            >> RW_TAC std_ss []
            >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            >> METIS_TAC [IN_UNIV,IN_IMAGE])
  >> `sup (IMAGE g UNIV) <> NegInf`
        by (RW_TAC std_ss [sup_eq,le_infty]
            >> Q.EXISTS_TAC `g (CHOICE (UNIV:num->bool))`
            >> RW_TAC std_ss []
            >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            >> METIS_TAC [IN_UNIV,IN_IMAGE])
  >> Cases_on `sup (IMAGE f univ(:num)) = PosInf`
  >- (`sup (IMAGE (\n. sup (IMAGE f univ(:num)) + g n) univ(:num)) = PosInf`
        by (RW_TAC std_ss [extreal_add_def,sup_eq,le_infty]
          >> POP_ASSUM (MP_TAC o Q.SPEC `PosInf + g (CHOICE (UNIV:num->bool))`)
          >> RW_TAC std_ss []
          >> `PosInf + g (CHOICE univ(:num)) <= y'`
               by (POP_ASSUM MATCH_MP_TAC
                   >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
                   >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
                   >> METIS_TAC [extreal_add_def])
          >> METIS_TAC [extreal_add_def,extreal_cases,le_infty])
      >> METIS_TAC [le_infty])
  >> RW_TAC std_ss [add_comm]
  >> Suff `sup (IMAGE g UNIV) <=
           sup (IMAGE (\n. g n + sup (IMAGE f UNIV)) UNIV) - sup (IMAGE f UNIV)`
  >- METIS_TAC [le_sub_eq,add_comm]
  >> RW_TAC std_ss [sup_le]
  >> MATCH_MP_TAC le_sub_imp
  >> RW_TAC std_ss []
  >> RW_TAC std_ss [le_sup]
  >> Q.PAT_ASSUM `IMAGE g UNIV y'` (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> METIS_TAC []);

val sup_sum_mono = store_thm
  ("sup_sum_mono",
  ``!f s. FINITE s /\ (!i:num. i IN s ==> (!n. 0 <= f i n)) /\
          (!i:num. i IN s ==> (!n. f i n <= f i (SUC n))) ==>
          (sup (IMAGE (\n. SIGMA (\i:num. f i n) s) UNIV) =
           SIGMA (\i:num. sup (IMAGE (f i) UNIV)) s)``,
 (* new proof *)
  Suff `!s. FINITE s ==> (\s. !f. (!i:num. i IN s ==> (!n. 0 <= f i n)) /\
                         (!i:num. i IN s ==> (!n. f i n <= f i (SUC n))) ==>
                      (sup (IMAGE (\n. SIGMA (\i:num. f i n) s) UNIV) =
                       SIGMA (\i:num. sup (IMAGE (f i) UNIV)) s)) s`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,UNIV_NOT_EMPTY,sup_const_over_set]
  >> `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
  >> `!n. (SIGMA (\i. f i n) (e INSERT s) = (\i. f i n) e + SIGMA (\i. f i n) (s DELETE e))`
        by (STRIP_TAC
            >> (MATCH_MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i n)`,`s`] o
                INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
            >> METIS_TAC [IN_INSERT, le_infty, lt_infty, extreal_of_num_def, extreal_not_infty])
  >> RW_TAC std_ss []
  >> `!n. !x. x IN e INSERT s ==> f x n <> NegInf`
      by METIS_TAC [IN_INSERT, le_infty, lt_infty, extreal_of_num_def, extreal_not_infty]
  >> `sup (IMAGE (\n. f e n + (\n. SIGMA (\i. f i n) s) n) UNIV) =
      sup (IMAGE (f e) UNIV) + sup (IMAGE (\n. SIGMA (\i. f i n) s) UNIV)`
        by ((MATCH_MP_TAC o Q.SPECL [`f e`, `(\n. SIGMA (\i. f i n) s)`] o
             INST_TYPE [alpha |-> ``:num``]) sup_add_mono
            >> FULL_SIMP_TAC std_ss [IN_INSERT,EXTREAL_SUM_IMAGE_POS]
            >> RW_TAC std_ss []
            >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s` o INST_TYPE [alpha |-> ``:num``])
                  EXTREAL_SUM_IMAGE_MONO
            >> FULL_SIMP_TAC std_ss [IN_INSERT])
  >> FULL_SIMP_TAC std_ss []
  >> `!i. i IN e INSERT s ==> 0 <= (\i. sup (IMAGE (f i) univ(:num))) i`
      by (RW_TAC std_ss [le_sup]
          >> MATCH_MP_TAC le_trans
          >> Q.EXISTS_TAC `f i 0`
          >> FULL_SIMP_TAC std_ss []
          >> POP_ASSUM MATCH_MP_TAC
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
  >> `!i. i IN e INSERT s ==> (\i. sup (IMAGE (f i) univ(:num))) i <> NegInf`
      by METIS_TAC [IN_INSERT,le_infty,lt_infty,extreal_of_num_def,extreal_not_infty]
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
  >> FULL_SIMP_TAC std_ss [IN_INSERT]);

val sup_le_mono = store_thm
  ("sup_le_mono",
  ``!f z. (!n. f n <= f (SUC n)) /\ z < sup (IMAGE f UNIV) ==> ?n. z <= f n``,
  RW_TAC std_ss []
  >> SPOSE_NOT_THEN ASSUME_TAC
  >> FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
  >> `!x. x IN (IMAGE f UNIV) ==> x <= z`
       by METIS_TAC [IN_IMAGE,IN_UNIV,lt_imp_le]
  >> METIS_TAC [sup_le,SPECIFICATION,extreal_lt_def]);

val sup_cmul = store_thm
  ("sup_cmul",
  ``!f c. 0 <= c ==> (sup (IMAGE (\n. (Normal c) * f n) UNIV) =
                      (Normal c) * sup (IMAGE f UNIV))``,
  RW_TAC std_ss []
  >> Cases_on `c = 0` >- RW_TAC real_ss [mul_lzero, GSYM extreal_of_num_def, UNIV_NOT_EMPTY,
                                         sup_const_over_set]
  >> `0 < c` by METIS_TAC [REAL_LT_LE]
  >> RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> Cases_on `sup (IMAGE f UNIV) = PosInf`
      >- RW_TAC std_ss [extreal_mul_def,le_infty]
      >> Cases_on `f n = NegInf`
      >- RW_TAC std_ss [extreal_mul_def,le_infty]
      >> `f n <= sup (IMAGE f UNIV)`
          by (MATCH_MP_TAC le_sup_imp
              >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
              >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
              >> METIS_TAC [])
      >> `f n <> PosInf /\ sup (IMAGE f UNIV) <> NegInf`
          by METIS_TAC [let_trans,lte_trans,lt_infty]
      >> `?r. f n = Normal r` by METIS_TAC [extreal_cases]
      >> `?r. sup (IMAGE f UNIV) = Normal r` by METIS_TAC [extreal_cases]
      >> RW_TAC std_ss [extreal_mul_def,extreal_le_def]
      >> METIS_TAC [REAL_LE_LMUL,extreal_le_def])
  >> `!n. Normal c * f n <= y`
        by (RW_TAC std_ss []
            >> POP_ASSUM MATCH_MP_TAC
            >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
            >> METIS_TAC [])
  >> `!n. f n <= y / (Normal c)` by METIS_TAC [le_rdiv,mul_comm]
  >> ONCE_REWRITE_TAC [mul_comm]
  >> RW_TAC std_ss [le_rdiv,sup_le]
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> METIS_TAC []);

(* Another version of `sup_cmul`: f is positive, c can be PosInf *)
Theorem sup_cmult :
    !f c. 0 <= c /\ (!n. 0 <= f n) ==>
         (sup (IMAGE (\n. c * f n) UNIV) = c * sup (IMAGE f UNIV))
Proof
    rpt STRIP_TAC
 >> Cases_on `c <> PosInf`
 >- (IMP_RES_TAC pos_not_neginf \\
    `?r. c = Normal r` by PROVE_TAC [extreal_cases] >> art [] \\
     MATCH_MP_TAC sup_cmul \\
     REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
     PROVE_TAC [])
 >> fs []
 >> Know `0 <= sup (IMAGE f univ(:'a))`
 >- (RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `f ARB` >> RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> PROVE_TAC [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [le_lt, Once DISJ_SYM]))
 >- (FIRST_ASSUM (REWRITE_TAC o wrap o SYM) >> REWRITE_TAC [mul_rzero] \\
     Know `!n. f n = 0`
     >- (POP_ASSUM (MP_TAC o SYM) \\
         RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV] \\
         RW_TAC std_ss [GSYM le_antisym] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> Rewr' \\
     REWRITE_TAC [mul_rzero] \\
     MATCH_MP_TAC sup_const_over_set >> SET_TAC [])
 >> RW_TAC std_ss [mul_lposinf]
 >> Know `?n. 0 < f n`
 >- (CCONTR_TAC >> fs [] \\
     POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [extreal_lt_def])) \\
    `!n. f n = 0` by PROVE_TAC [le_antisym] \\
    `f = \n. 0` by PROVE_TAC [] \\
     ASSUME_TAC (Q.SPEC `0` sup_const_over_univ) \\
    `(\x. 0) = f` by METIS_TAC [] >> fs [lt_refl]) >> STRIP_TAC
 >> RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV, le_infty]
 >> RW_TAC std_ss [GSYM le_antisym, Once le_infty]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n`
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC mul_lposinf >> art []
QED

val sup_lt = store_thm
  ("sup_lt", ``!P y. (?x. P x /\ y < x) <=> y < sup P``,
  RW_TAC std_ss []
  >> EQ_TAC >- METIS_TAC [le_sup_imp,lte_trans]
  >> RW_TAC std_ss []
  >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
  >> METIS_TAC [sup_le,extreal_lt_def]);

Theorem lt_sup : (* was: less_Sup_iff *)
    !a s. a < sup s <=> ?x. x IN s /\ a < x
Proof
    METIS_TAC [sup_lt, SPECIFICATION]
QED
val less_Sup_iff = lt_sup;

val sup_lt' = store_thm
  ("sup_lt'", ``!P y. (?x. x IN P /\ y < x) <=> y < sup P``,
    RW_TAC std_ss [IN_APP]
 >> REWRITE_TAC [sup_lt]);

val sup_lt_epsilon = store_thm (* c.f. SUP_EPSILON *)
  ("sup_lt_epsilon",
  ``!P e. (0 < e) /\ (?x. P x /\ x <> NegInf) /\ (sup P <> PosInf) ==>
          ?x. P x /\ sup P < x + e``,
  RW_TAC std_ss []
  >> Cases_on `e = PosInf`
  >- (Q.EXISTS_TAC `x`
      >> RW_TAC std_ss []
      >> METIS_TAC [extreal_add_def,lt_infty,extreal_cases])
  >> `e <> NegInf` by METIS_TAC [le_sup_imp,lt_infty,lte_trans,
                                 extreal_of_num_def,extreal_not_infty]
  >> `sup P <> NegInf` by METIS_TAC [le_sup_imp,lt_infty,lte_trans]
  >> `sup P < sup P + e`
     by (Cases_on `sup P` >> Cases_on `e`
         >> RW_TAC std_ss [extreal_cases, extreal_add_def, extreal_lt_def, extreal_le_def,
                           GSYM real_lt]
         >> METIS_TAC [REAL_LT_ADDR, extreal_lt_def, extreal_le_def, extreal_of_num_def, real_lt])
  >> `sup P - e < sup P` by METIS_TAC [sub_lt_imp]
  >> `?x. P x /\ (sup P - e) < x` by METIS_TAC [sup_lt]
  >> Q.EXISTS_TAC `x'`
  >> RW_TAC std_ss []
  >> `x' <> PosInf` by METIS_TAC [le_sup_imp,let_trans,lt_infty]
  >> `?r. sup P = Normal r` by METIS_TAC [extreal_cases]
  >> `?r. e = Normal r` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss [extreal_sub_def]
  >> `x' <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lt_trans]
  >> `?r. x' = Normal r` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss [extreal_add_def,extreal_lt_def,extreal_le_def,GSYM real_lt,
                           REAL_LT_SUB_RADD]);

val inf_le_imp = store_thm
  ("inf_le_imp", ``!p x. p x ==> inf p <= x``,
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,le_sup]
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_IMAGE]
  >> METIS_TAC [SPECIFICATION]);

val inf_le_imp' = store_thm
  ("inf_le_imp'", ``!p x. x IN p ==> inf p <= x``,
    REWRITE_TAC [IN_APP]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC inf_le_imp >> art []);

val le_inf = store_thm
  ("le_inf",
   ``!p x. x <= inf p <=> (!y. p y ==> x <= y)``,
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,sup_le]
  >> EQ_TAC
  >- (RW_TAC std_ss []
      >> `-y IN (IMAGE numeric_negate p)`
           by (RW_TAC std_ss [IN_IMAGE]
               >> METIS_TAC [SPECIFICATION])
      >> METIS_TAC [le_neg,SPECIFICATION])
  >> RW_TAC std_ss []
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE]
  >> METIS_TAC [le_neg,SPECIFICATION]);

val le_inf' = store_thm
  ("le_inf'",
  ``!p x. x <= inf p <=> (!y. y IN p ==> x <= y)``,
    REWRITE_TAC [IN_APP]
 >> REWRITE_TAC [le_inf]);

val inf_le = store_thm
  ("inf_le",
   ``!p x. (inf p <= x) <=> (!y. (!z. p z ==> y <= z) ==> y <= x)``,
  RW_TAC std_ss [extreal_inf_def,Once (GSYM le_neg),neg_neg,le_sup]
  >> EQ_TAC
  >- (RW_TAC std_ss []
      >> `!z. IMAGE numeric_negate p z ==> y <= -z`
            by (RW_TAC std_ss []
                >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
                >> RW_TAC std_ss [IN_IMAGE]
                >> METIS_TAC [neg_neg,SPECIFICATION])
      >> `!z. IMAGE numeric_negate p z ==> z <= -y`
           by METIS_TAC [le_neg,neg_neg]
      >> `(!z. IMAGE numeric_negate p z ==> z <= -y) ==> -x <= -y`
           by METIS_TAC []
      >> METIS_TAC [le_neg])
  >> RW_TAC std_ss []
  >> `!z. p z ==> -z <= y`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!z. IMAGE numeric_negate p z ==> z <= y` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE]
           >> METIS_TAC [SPECIFICATION])
  >> `!z. p z ==> -y <= z` by METIS_TAC [le_neg,neg_neg]
  >> METIS_TAC [le_neg,neg_neg]);

val inf_le' = store_thm
  ("inf_le'", ``!p x. (extreal_inf p <= x) <=>
                        (!y. (!z. z IN p ==> y <= z) ==> y <= x)``,
    REWRITE_TAC [IN_APP]
 >> ACCEPT_TAC inf_le);

val inf_eq = store_thm
  ("inf_eq", ``!p x. (extreal_inf p = x) <=>
                       (!y. p y ==> x <= y) /\
                       (!y. (!z. p z ==> y <= z) ==> y <= x)``,
  METIS_TAC [le_antisym,inf_le,le_inf]);

val inf_eq' = store_thm
  ("inf_eq'", ``!p x. (extreal_inf p = x) <=>
                        (!y. y IN p ==> x <= y) /\
                        (!y. (!z. z IN p ==> y <= z) ==> y <= x)``,
    REWRITE_TAC [IN_APP]
 >> ACCEPT_TAC inf_eq);

val inf_const = store_thm
  ("inf_const", ``!x. extreal_inf (\y. y = x) = x``,
    RW_TAC real_ss [inf_eq, le_refl]);

Theorem inf_sing :
    !a:extreal. inf {a} = a
Proof
    REWRITE_TAC [METIS [EXTENSION, IN_SING, IN_DEF] ``{a} = (\x. x = a)``]
 >> SIMP_TAC std_ss [inf_const]
QED

val inf_const_alt = store_thm
  ("inf_const_alt", ``!p z. (?x. p x) /\ (!x. p x ==> (x = z)) ==> (inf p = z)``,
  RW_TAC std_ss [inf_eq,le_refl]
  >> POP_ASSUM MATCH_MP_TAC
  >> RW_TAC std_ss []);

val inf_const_over_set = store_thm
  ("inf_const_over_set", ``!s k. s <> {} ==> (inf (IMAGE (\x. k) s) = k)``,
  RW_TAC std_ss [inf_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE] >> RW_TAC std_ss [le_refl])
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_IMAGE]
  >> METIS_TAC [CHOICE_DEF]);

val inf_suc = store_thm
  ("inf_suc",
   ``!f. (!m n. m <= n ==> f n <= f m) ==>
     (inf (IMAGE (\n. f (SUC n)) UNIV) = inf (IMAGE f UNIV))``,
  RW_TAC std_ss [inf_eq,inf_le,le_inf]
  >- (POP_ASSUM MATCH_MP_TAC
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [])
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `f (SUC x)`
  >> RW_TAC real_ss []
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> METIS_TAC []);

val inf_seq = store_thm
  ("inf_seq",
  ``!f l. mono_decreasing f ==>
         ((f --> l) <=> (inf (IMAGE (\n. Normal (f n)) UNIV) = Normal l))``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- (RW_TAC std_ss [inf_eq]
      >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> RW_TAC std_ss [extreal_le_def]
          >> METIS_TAC [mono_decreasing_suc,SEQ_LE_MONO,ADD1])
      >> `!n. y <= Normal (f n)`
            by (RW_TAC std_ss []
                >> POP_ASSUM MATCH_MP_TAC
                >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
                >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
                >> METIS_TAC [])
      >> Cases_on `y`
      >| [METIS_TAC [le_infty],
          METIS_TAC [le_infty,extreal_not_infty],
          METIS_TAC [LE_SEQ_IMP_LE_LIM,extreal_le_def]])
  >> RW_TAC std_ss [extreal_inf_def,extreal_sup_def,extreal_ainv_def,extreal_not_infty]
  >> `(\r. IMAGE numeric_negate (IMAGE (\n. Normal (f n)) univ(:num)) (Normal r)) =
       IMAGE (\n. - f n) UNIV`
       by (RW_TAC std_ss [EXTENSION,IN_ABS,IN_IMAGE,IN_UNIV]
           >> EQ_TAC
           >- (RW_TAC std_ss []
               >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
               >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
               >> METIS_TAC [extreal_ainv_def,extreal_11])
           >> RW_TAC std_ss []
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
           >> METIS_TAC [extreal_ainv_def,extreal_11])
  >> POP_ORW
  >> FULL_SIMP_TAC std_ss []
  >> `!n. -Normal (f n) <= x`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!y. P` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
           >> METIS_TAC [])
  >> `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans]
  >> `?z. x = Normal z` by METIS_TAC [extreal_cases]
  >> `!n. -(f n) <= z` by METIS_TAC [extreal_le_def,extreal_ainv_def]
  >> Suff `(\n. -f n) --> sup (IMAGE (\n. -f n) univ(:num))`
  >- METIS_TAC [SEQ_NEG,REAL_NEG_NEG]
  >> `mono_increasing (\n. -f n)`
        by FULL_SIMP_TAC std_ss [mono_increasing_def,mono_decreasing_def,REAL_LE_NEG]
  >> Suff `?r. (\n. -f n) --> r`
  >- METIS_TAC [mono_increasing_converges_to_sup]
  >> RW_TAC std_ss [GSYM convergent]
  >> MATCH_MP_TAC SEQ_ICONV
  >> FULL_SIMP_TAC std_ss [GREATER_EQ,real_ge,mono_increasing_def]
  >> MATCH_MP_TAC SEQ_BOUNDED_2
  >> Q.EXISTS_TAC `-f 0`
  >> Q.EXISTS_TAC `z`
  >> RW_TAC std_ss []);

val inf_lt_infty = store_thm
  ("inf_lt_infty", ``!p. (NegInf < inf p) ==> (!x. p x ==> NegInf < x)``,
  METIS_TAC [inf_le_imp,lte_trans]);

val inf_min = store_thm
  ("inf_min", ``!p z. p z /\ (!x. p x ==> z <= x) ==> (inf p = z)``,
  RW_TAC std_ss [inf_eq]);

val inf_cminus = store_thm
  ("inf_cminus", ``!f c. Normal c - inf (IMAGE f UNIV) =
                         sup (IMAGE (\n. Normal c - f n) UNIV)``,
 (* new proof *)
  RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> `inf (IMAGE f UNIV) <= f n`
           by (MATCH_MP_TAC inf_le_imp
               >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
               >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
               >> METIS_TAC [])
      >> METIS_TAC [le_lsub_imp])
  >> `!n. Normal c - f n <= y`
        by (RW_TAC std_ss []
            >> Q.PAT_ASSUM `!z. P` MATCH_MP_TAC
            >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
            >> METIS_TAC [])
  >> RW_TAC std_ss [extreal_inf_def,sub_rneg]
  >> Suff `sup (IMAGE numeric_negate (IMAGE f UNIV)) <= y - Normal c`
  >- METIS_TAC [le_sub_eq,extreal_not_infty,add_comm_normal]
  >> RW_TAC std_ss [sup_le]
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
  >> RW_TAC std_ss [le_sub_eq,extreal_not_infty,GSYM add_comm_normal]
  >> Cases_on `y = PosInf` >- RW_TAC std_ss [le_infty]
  >> `f x' <> NegInf` by METIS_TAC [extreal_sub_def,lt_infty,extreal_lt_def]
  >> METIS_TAC [extreal_not_infty,extreal_sub_add]);

(* The "inf" of an empty set is PosInf, reasonable but quite unexpected *)
val inf_empty = store_thm
  ("inf_empty", ``inf EMPTY = PosInf``,
    RW_TAC std_ss [extreal_inf_def, extreal_sup_def, IMAGE_EMPTY,
                   REWRITE_RULE [IN_APP] NOT_IN_EMPTY, extreal_ainv_def]);

(* The "sup" of an empty set is NegInf, reasonable but quite unexpected *)
val sup_empty = store_thm
  ("sup_empty", ``sup EMPTY = NegInf``,
    RW_TAC std_ss [extreal_sup_def, IMAGE_EMPTY,
                   REWRITE_RULE [IN_APP] NOT_IN_EMPTY, extreal_ainv_def]
 >> METIS_TAC [num_not_infty]);

val sup_univ = store_thm
  ("sup_univ", ``sup univ(:extreal) = PosInf``,
    RW_TAC std_ss [sup_eq', IN_UNIV, GSYM le_infty]);

val inf_univ = store_thm
  ("inf_univ", ``inf univ(:extreal) = NegInf``,
    RW_TAC std_ss [inf_eq', IN_UNIV, GSYM le_infty]);

val inf_lt = store_thm
  ("inf_lt", ``!P y. (?x. P x /\ x < y) <=> extreal_inf P < y``,
    RW_TAC std_ss []
 >> EQ_TAC >- METIS_TAC [inf_le_imp, let_trans]
 >> RW_TAC std_ss []
 >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
 >> METIS_TAC [le_inf,extreal_lt_def]);

val inf_lt' = store_thm
  ("inf_lt'", ``!P y. (?x. x IN P /\ x < y) <=> extreal_inf P < y``,
    REWRITE_TAC [IN_APP]
 >> REWRITE_TAC [inf_lt]);

(* dual version of sup_lt_epsilon *)
val lt_inf_epsilon = store_thm
  ("lt_inf_epsilon", ``!P e. (0 < e) /\ (?x. P x /\ x <> PosInf) /\ (inf P <> NegInf)
                         ==> (?x. P x /\ x < inf P + e)``,
    RW_TAC std_ss []
 >> Cases_on `e = PosInf` (* ``inf P <> NegInf`` is necessary here *)
 >- (Q.EXISTS_TAC `x`
     >> RW_TAC std_ss []
     >> METIS_TAC [extreal_add_def,lt_infty,extreal_cases])
 >> `e <> NegInf` by METIS_TAC [le_sup_imp,lt_infty,lte_trans,
                                extreal_of_num_def,extreal_not_infty]
 >> `inf P <> PosInf` by METIS_TAC [inf_le_imp,lt_infty,let_trans]
 >> `inf P < inf P + e`
     by (Cases_on `inf P` >> Cases_on `e`
         >> RW_TAC std_ss [extreal_cases,extreal_add_def,extreal_lt_def,extreal_le_def,GSYM real_lt]
         >> METIS_TAC [REAL_LT_ADDR,extreal_lt_def,extreal_le_def,extreal_of_num_def,real_lt])
 >> `?x. P x /\ x < inf P + e` by METIS_TAC [inf_lt]
 >> Q.EXISTS_TAC `x'`
 >> RW_TAC std_ss []);

Theorem sup_comm : (* was: SUP_commute *)
    !f. sup {sup {f i j | j IN univ(:num)} | i IN univ(:num)} =
        sup {sup {f i j | i IN univ(:num)} | j IN univ(:num)}
Proof
  RW_TAC std_ss [sup_eq] THENL
  [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
   RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [sup_le] THEN
   GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
   RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [le_sup] THEN
   GEN_TAC THEN DISCH_THEN (MP_TAC o Q.SPEC `sup {f i (j:num) | i IN univ(:num)}`) THEN
   Q_TAC SUFF_TAC `{sup {f i j | i IN univ(:num)} | j IN univ(:num)}
    (sup {f i j | i IN univ(:num)})` THENL
   [DISCH_TAC, ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC []] THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN
   Q.EXISTS_TAC `sup {f i j | i IN univ(:num)}` THEN ASM_REWRITE_TAC [le_sup] THEN
   GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [sup_le] THEN GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN SIMP_TAC std_ss [sup_le] THEN
  GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
  RW_TAC std_ss [GSPECIFICATION] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `sup {f (i:num) j | j IN univ(:num)}`) THEN
  Q_TAC SUFF_TAC `{sup {f i j | j IN univ(:num)} | i IN univ(:num)}
   (sup {f i j | j IN univ(:num)})` THENL
  [ALL_TAC, ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC []] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC le_trans THEN
  Q.EXISTS_TAC `sup {f i j | j IN univ(:num)}` THEN ASM_SIMP_TAC std_ss [le_sup] THEN
  GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC []
QED

Theorem sup_close : (* was: Sup_ereal_close *)
    !e s. 0 < e /\ (abs (sup s) <> PosInf) /\ (s <> {}) ==>
          ?x. x IN s /\ sup s - e < x
Proof
  RW_TAC std_ss [] THEN
  `?r. sup s = Normal r` by METIS_TAC [extreal_cases, extreal_abs_def] THEN
  `e <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lt_trans] THEN
  Q_TAC SUFF_TAC `Normal r - e < sup s` THENL
  [SIMP_TAC std_ss [less_Sup_iff] THEN RW_TAC std_ss [],
   ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ``e = PosInf`` THENL
   [ASM_REWRITE_TAC [extreal_sub_def, lt_infty], ALL_TAC] THEN
   `?k. e = Normal k` by METIS_TAC [extreal_cases] THEN
   ASM_SIMP_TAC std_ss [extreal_sub_def, extreal_lt_eq] THEN
   MATCH_MP_TAC (REAL_ARITH ``0 < k ==> a - k < a:real``) THEN
   ONCE_REWRITE_TAC [GSYM extreal_lt_eq] THEN
   METIS_TAC [extreal_of_num_def]]
QED
val Sup_ereal_close = sup_close;

(* This lemma find a countable monotonic sequence of element in any non-empty
   extreal sets, with the same limit point.
 *)
Theorem sup_countable_seq : (* was: Sup_countable_SUPR *)
    !A. A <> {} ==> ?f:num->extreal. IMAGE f UNIV SUBSET A /\
                      (sup A = sup {f n | n IN UNIV})
Proof
    RW_TAC std_ss []
 >> STRIP_ASSUME_TAC (Q.SPEC `sup A` extreal_cases) (* 3 subgoals *)
 >| [ (* goal 1 (of 3): NegInf *)
      POP_ASSUM (MP_TAC o REWRITE_RULE [sup_eq]) THEN RW_TAC std_ss [le_infty] THEN
     `A = {NegInf}` by ASM_SET_TAC [] THEN
      ASM_REWRITE_TAC [] THEN Q.EXISTS_TAC `(\n. NegInf)` THEN
      CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN SIMP_TAC std_ss [] THEN
      AP_TERM_TAC THEN SET_TAC [],
      (* goal 2 (of 3): PosInf *)
   FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
   ASM_CASES_TAC ``PosInf IN A`` THENL
   [Q.EXISTS_TAC `(\x. PosInf)` THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
    SIMP_TAC std_ss [] THEN REWRITE_TAC [SET_RULE ``{PosInf | n IN univ(:num)} = {PosInf}``] THEN
    SIMP_TAC std_ss [sup_sing], ALL_TAC] THEN
   Q_TAC SUFF_TAC `?x. x IN A /\ 0 <= x` THENL
   [STRIP_TAC,
    UNDISCH_TAC ``sup A = PosInf`` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    SIMP_TAC std_ss [sup_eq] THEN RW_TAC std_ss [lt_infty, GSYM extreal_lt_def] THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `z`) THEN ASM_SIMP_TAC std_ss [le_lt]] THEN
   Q_TAC SUFF_TAC `!n. ?f. f IN A /\ x' + Normal (&n) <= f` THENL
   [DISCH_TAC,
    CCONTR_TAC THEN Q_TAC SUFF_TAC `?n. sup A <= x' + Normal (&n)` THENL
    [RW_TAC std_ss [GSYM extreal_lt_def] THEN
     `x' <> PosInf` by METIS_TAC [] THEN
     ASM_CASES_TAC ``x' = NegInf`` THENL
     [FULL_SIMP_TAC std_ss [extreal_add_def, lt_infty], ALL_TAC] THEN
     `?r. x' = Normal r` by METIS_TAC [extreal_cases] THEN
     ASM_SIMP_TAC std_ss [extreal_add_def, lt_infty],
     ALL_TAC] THEN
    SIMP_TAC std_ss [sup_le] THEN FULL_SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
    Q.EXISTS_TAC `n` THEN GEN_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `y`) THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [le_lt]] THEN
   Q_TAC SUFF_TAC `?f. !z. f z IN A /\ x' + Normal (&z) <= f z` THENL
   [STRIP_TAC, METIS_TAC []] THEN
   Q_TAC SUFF_TAC `sup {f n | n IN UNIV} = PosInf` THENL
   [DISCH_TAC THEN Q.EXISTS_TAC `f` THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ASM_REWRITE_TAC [] THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `!n. ?i. Normal (&n) <= f i` THENL
   [DISCH_TAC,
    GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN STRIP_TAC THEN
    Q.EXISTS_TAC `n` THEN MATCH_MP_TAC le_trans THEN
    Q.EXISTS_TAC `x' + Normal (&n)` THEN ASM_REWRITE_TAC [] THEN
    `x' <> PosInf` by METIS_TAC [] THEN
    `x' <> NegInf` by (METIS_TAC [lt_infty, lte_trans, num_not_infty]) THEN
    `?r. x' = Normal r` by (METIS_TAC [extreal_cases]) THEN
    ASM_SIMP_TAC std_ss [extreal_add_def, extreal_le_def] THEN
    MATCH_MP_TAC (REAL_ARITH ``0 <= b ==> a <= b + a:real``) THEN
    METIS_TAC [extreal_le_def, extreal_of_num_def]] THEN
   SIMP_TAC std_ss [sup_eq] THEN CONJ_TAC THENL [SIMP_TAC std_ss [le_infty], ALL_TAC] THEN
   RW_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [GSYM extreal_lt_def, GSYM lt_infty] THEN
   POP_ASSUM (MP_TAC o MATCH_MP SIMP_EXTREAL_ARCH) THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `SUC n`) THEN STRIP_TAC THEN
   Q.EXISTS_TAC `f i` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    METIS_TAC [IN_UNIV], ALL_TAC] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `Normal (&SUC n)` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `&n` THEN
   ASM_REWRITE_TAC [] THEN SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq],
      (* goal 3 (of 3): Normal r *)
      Know `!n:num. ?x. x IN A /\ sup A < x + 1 / &(SUC n)`
      >- (GEN_TAC \\
          Know `?x. x IN A /\ sup A - 1 / &(SUC n) < x`
          >- (MATCH_MP_TAC Sup_ereal_close \\
              ASM_SIMP_TAC std_ss [extreal_abs_def, lt_infty] \\
             `&(SUC n) = Normal &(SUC n)` by METIS_TAC [extreal_of_num_def] \\
             `SUC n <> 0` by RW_TAC arith_ss [] \\
             `(0 :real) < &(SUC n)` by METIS_TAC [REAL_NZ_IMP_LT] \\
              METIS_TAC [lt_div, lt_01]) >> RW_TAC std_ss [] \\
          Q.EXISTS_TAC `x` >> art [] \\
         `&(SUC n) = Normal &(SUC n)` by METIS_TAC [extreal_of_num_def] \\
         `&(SUC n) <> (0 :real)` by RW_TAC real_ss [] \\
         `(1 :extreal) / &SUC n = Normal (1 / &SUC n)`
            by METIS_TAC [extreal_of_num_def, extreal_div_eq] >> fs [] \\
         `Normal (1 / &SUC n) <> PosInf /\ Normal (1 / &SUC n) <> NegInf`
            by PROVE_TAC [extreal_not_infty] \\
          METIS_TAC [sub_lt_eq]) >> DISCH_TAC \\
      FULL_SIMP_TAC std_ss [SKOLEM_THM] \\
      Know `sup {f n | n IN univ(:num)} = sup A`
      >- (RW_TAC std_ss [sup_eq', GSPECIFICATION, IN_UNIV]
          >- (Q.PAT_X_ASSUM `sup A = _` (ONCE_REWRITE_TAC o wrap o SYM) \\
              MATCH_MP_TAC le_sup_imp >> METIS_TAC [IN_APP]) \\
          Q.PAT_X_ASSUM `sup A = _` (ONCE_REWRITE_TAC o wrap o SYM) \\
          MATCH_MP_TAC le_epsilon >> RW_TAC std_ss [] \\
         `e <> NegInf` by METIS_TAC [lt_trans, lt_infty] \\
         `?r. e = Normal r` by METIS_TAC [extreal_cases] \\
          ONCE_ASM_REWRITE_TAC [] \\
         `0 < r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
         `?n. inv (&SUC n) < r` by METIS_TAC [REAL_ARCH_INV_SUC] \\
          MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `f n + 1 / &SUC n` \\
          CONJ_TAC >- METIS_TAC [le_lt] \\
          MATCH_MP_TAC le_add2 \\
          CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                       Q.EXISTS_TAC `n` >> REWRITE_TAC []) \\
         `&SUC n <> (0 :real)` by RW_TAC real_ss [] \\
          ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_div_eq,
                               extreal_le_eq, GSYM REAL_INV_1OVER] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
      Q.EXISTS_TAC `f` >> ASM_SET_TAC [] ]
QED
val Sup_countable_SUPR = sup_countable_seq;

Theorem sup_seq_countable_seq : (* was: SUPR_countable_SUPR *)
    !A g. A <> {} ==>
          ?f:num->extreal. IMAGE f UNIV SUBSET IMAGE g A /\
                    (sup {g n | n IN A} = sup {f n | n IN UNIV})
Proof
  RW_TAC std_ss [] THEN ASSUME_TAC Sup_countable_SUPR THEN
  POP_ASSUM (MP_TAC o Q.SPEC `IMAGE g A`) THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN DISCH_THEN (MATCH_MP_TAC) THEN
  ASM_SET_TAC []
QED
val SUPR_countable_SUPR = sup_seq_countable_seq;

(* ------------------------------------------------------------------------- *)
(*  Limit superior and limit inferior (limsup and liminf) [1, p.313] [4]     *)
(*  Used in Fatou's lemma (lebesgueTheory) and the 2nd part of SLLN          *)
(* ------------------------------------------------------------------------- *)

(* for a sequence of function (u :num -> 'a -> extreal),
   use `ext_limsup (\n. u n x)` as "limsup u x" [1, p.63], etc. *)
val ext_limsup_def = Define
   `ext_limsup (a :num -> extreal) = inf (IMAGE (\m. sup {a n | m <= n}) UNIV)`;

val ext_liminf_def = Define
   `ext_liminf (a :num -> extreal) = sup (IMAGE (\m. inf {a n | m <= n}) UNIV)`;

val _ = overload_on ("limsup", ``ext_limsup``);
val _ = overload_on ("liminf", ``ext_liminf``);


(* ------------------------------------------------------------------------- *)
(* Suminf over extended reals. Definition and properties                     *)
(* ------------------------------------------------------------------------- *)

(* old definition, which (wrongly) allows `!f. 0 <= ext_suminf f`:
val ext_suminf_def = Define
   `ext_suminf f = sup (IMAGE (\n. SIGMA f (count n)) UNIV)`;

   new definition, which is only specified on positive functions: *)
local
  val thm = Q.prove (
     `?sum. !f. (!n. 0 <= f n) ==>
                (sum f = sup (IMAGE (\n. SIGMA f (count n)) UNIV))`,
      Q.EXISTS_TAC `\f. sup (IMAGE (\n. SIGMA f (count n)) UNIV)` \\
      RW_TAC std_ss []);
in
  val ext_suminf_def = new_specification
    ("ext_suminf_def", ["ext_suminf"], thm);
end;

Theorem ext_suminf_alt : (* without IMAGE *)
    !f. (!n. 0 <= f n) ==>
        (ext_suminf (\x. f x) = sup {SIGMA (\i. f i) (count n) | n IN UNIV})
Proof
    RW_TAC std_ss [ext_suminf_def, IMAGE_DEF]
QED

Theorem ext_suminf_alt' : (* without IMAGE, further simplified *)
    !f. (!n. 0 <= f n) ==>
        (ext_suminf (\x. f x) = sup {SIGMA f (count n) | n | T})
Proof
    RW_TAC bool_ss [ext_suminf_alt, ETA_AX, IN_UNIV]
QED

Theorem ext_suminf_add :
    !f g. (!n. 0 <= f n /\ 0 <= g n) ==>
          (ext_suminf (\n. f n + g n) = ext_suminf f + ext_suminf g)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\n. f n + g n) n`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC le_add >> art []) >> DISCH_TAC
 >> RW_TAC std_ss [ext_suminf_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))
 >> RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV]
 >- (`!n. f n <> NegInf /\ g n <> NegInf`
       by METIS_TAC [lt_infty, lte_trans, num_not_infty] \\
     RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_ADD] \\
     MATCH_MP_TAC le_add2 \\
     RW_TAC std_ss [le_sup'] \\
     POP_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC [])
 >> Know `!n. SIGMA (\n. f n + g n) (count n) <= y`
 >- (RW_TAC std_ss [] >> POP_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> `!n. f n <> NegInf /\ g n <> NegInf`
       by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> `!n. SIGMA (\n. f n + g n) (count n) =
         SIGMA f (count n) + SIGMA g (count n)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_ADD, FINITE_COUNT]
 >> `!n. SIGMA f (count n) + SIGMA g (count n) <= y`
       by FULL_SIMP_TAC std_ss []
 >> Know `!n m. SIGMA f (count n) + SIGMA g (count m) <= y`
 >- (RW_TAC std_ss [] \\
     Cases_on `n <= m`
     >- (MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC `SIGMA f (count m) + SIGMA g (count m)` \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC le_radd_imp \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
         RW_TAC std_ss [FINITE_COUNT, SUBSET_DEF, IN_COUNT] \\
         DECIDE_TAC) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `SIGMA f (count n) + SIGMA g (count n)` \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_ladd_imp \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     RW_TAC std_ss [FINITE_COUNT, SUBSET_DEF, IN_COUNT] \\
     DECIDE_TAC) >> DISCH_TAC
 >> Cases_on `y = PosInf` >- RW_TAC std_ss [le_infty]
 >> `!n. SIGMA f (count n) <> NegInf`
       by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, FINITE_COUNT]
 >> `!n. SIGMA g (count n) <> NegInf`
       by METIS_TAC [EXTREAL_SUM_IMAGE_NOT_INFTY, FINITE_COUNT]
 >> `y <> NegInf` by METIS_TAC [lt_infty, add_not_infty, lte_trans]
 >> FULL_SIMP_TAC std_ss [GSYM le_sub_eq2]
 >> Know `!m. sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <= y - SIGMA g (count m)`
 >- (RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
     FULL_SIMP_TAC std_ss []) >> DISCH_TAC
 >> Know `sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <> NegInf`
 >- (RW_TAC std_ss [lt_infty, GSYM sup_lt', IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `SIGMA f (count 0)` \\
     reverse (RW_TAC bool_ss []) >- FULL_SIMP_TAC std_ss [lt_infty] \\
     Q.EXISTS_TAC `0` >> REWRITE_TAC []) >> DISCH_TAC
 >> `!m. SIGMA g (count m) + sup (IMAGE (\n. SIGMA f (count n)) univ(:num)) <= y`
       by METIS_TAC [le_sub_eq2, add_comm]
 >> `!m. SIGMA g (count m) <= y - sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
       by METIS_TAC [le_sub_eq2]
 >> `!m. sup (IMAGE (\n. SIGMA g (count n)) univ(:num)) <=
         y - sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
       by (RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
           FULL_SIMP_TAC std_ss [])
 >> Know `sup (IMAGE (\n. SIGMA g (count n)) univ(:num)) <> NegInf`
 >- (RW_TAC std_ss [lt_infty, GSYM sup_lt', IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `SIGMA g (count 0)` \\
     reverse (RW_TAC bool_ss []) >- FULL_SIMP_TAC std_ss [lt_infty] \\
     Q.EXISTS_TAC `0` >> REWRITE_TAC []) >> DISCH_TAC
 >> METIS_TAC [le_sub_eq2, add_comm]
QED

Theorem ext_suminf_cmul :
    !f c. 0 <= c /\ (!n. 0 <= f n) ==>
          (ext_suminf (\n. c * f n) = c * ext_suminf f)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\n. c * f n) n`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC le_mul >> art [])
 >> RW_TAC std_ss [ext_suminf_def]
 >> `c <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans]
 >> `!n. f n <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans]
 >> reverse (Cases_on `c` >> (RW_TAC std_ss []))
 >- (`!n. SIGMA (\n. Normal r * f n) (count n) =
          Normal r * SIGMA f (count n)`
       by METIS_TAC [EXTREAL_SUM_IMAGE_CMUL, FINITE_COUNT] >> POP_ORW \\
     METIS_TAC [sup_cmul, extreal_le_def, extreal_of_num_def])
 >> Cases_on `!n. f n = 0`
 >- (RW_TAC std_ss [extreal_mul_def, extreal_of_num_def, EXTREAL_SUM_IMAGE_0,
                    FINITE_COUNT] \\
     Know `sup (IMAGE (\n. Normal 0) univ(:num)) = 0`
     >- (MATCH_MP_TAC sup_const_alt' \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         REWRITE_TAC [extreal_of_num_def]) >> DISCH_TAC \\
     RW_TAC std_ss [extreal_of_num_def, extreal_mul_def])
 >> FULL_SIMP_TAC std_ss []
 >> `0 < f n` by METIS_TAC [lt_le]
 >> Know `0 < sup (IMAGE (\n. SIGMA f (count n)) univ(:num))`
 >- (RW_TAC std_ss [GSYM sup_lt'] \\
     Q.EXISTS_TAC `SIGMA f (count (SUC n))` \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV]
     >- (Q.EXISTS_TAC `SUC n` >> REWRITE_TAC []) \\
    `f n <= SIGMA f (count (SUC n))`
       by METIS_TAC [COUNT_SUC, IN_INSERT, FINITE_COUNT,
                     EXTREAL_SUM_IMAGE_POS_MEM_LE] \\
     METIS_TAC [lte_trans]) >> DISCH_TAC
 >> `PosInf * f n <= SIGMA (\n. PosInf * f n) (count (SUC n))`
       by (`!n. 0 <= PosInf * f n` by METIS_TAC [le_infty, le_mul] \\
           `n IN count (SUC n)` by METIS_TAC [COUNT_SUC, IN_INSERT] \\
           (MP_TAC o REWRITE_RULE [FINITE_COUNT] o
            Q.ISPECL [`(\n:num. PosInf * f n)`, `count (SUC n)`])
              EXTREAL_SUM_IMAGE_POS_MEM_LE \\
           RW_TAC std_ss [])
 >> `!x. 0 < x ==> (PosInf * x = PosInf)`
       by (Cases_on `x`
           >| [ METIS_TAC [lt_infty],
                RW_TAC std_ss [extreal_mul_def],
                RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def,
                                extreal_mul_def] ])
 >> `PosInf * f n = PosInf`
       by ((Cases_on `f n` >> FULL_SIMP_TAC std_ss [extreal_mul_def])
           >- METIS_TAC []
           >> METIS_TAC [extreal_lt_eq, extreal_of_num_def])
 >> `SIGMA (\n. PosInf * f n) (count (SUC n)) = PosInf` by METIS_TAC [le_infty]
 >> `SIGMA (\n. PosInf * f n) (count (SUC n)) <=
     sup (IMAGE (\n. SIGMA (\n. PosInf * f n) (count n)) univ(:num))`
       by (MATCH_MP_TAC le_sup_imp' \\
           RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
           METIS_TAC [])
 >> `sup (IMAGE (\n. SIGMA (\n. PosInf * f n) (count n)) univ(:num)) = PosInf`
       by METIS_TAC [le_infty]
 >> METIS_TAC []
QED

Theorem ext_suminf_cmul_alt :
    !f c. 0 <= c /\ (!n. 0 <= f n) /\ (!n. f n < PosInf) ==>
         (ext_suminf (\n. (Normal c) * f n) = (Normal c) * ext_suminf f)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\n. Normal c * f n) n`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC le_mul >> art [] \\
     ASM_REWRITE_TAC [extreal_of_num_def, extreal_le_eq]) >> DISCH_TAC
 >> RW_TAC std_ss [ext_suminf_def]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))
 >> Know `!n. SIGMA (\n. Normal c * f n) (count n) =
              (Normal c) * SIGMA f (count n)`
 >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_CMUL \\
     RW_TAC std_ss [FINITE_COUNT, lt_infty]) >> Rewr'
 >> RW_TAC std_ss [sup_cmul]
QED

(* Note: changed `ext_suminf f <> PosInf` to `ext_suminf f < PosInf` for
   easier applications. To get the original version, use "lt_infty". *)
Theorem ext_suminf_lt_infty :
    !f. (!n. 0 <= f n) /\ ext_suminf f < PosInf ==> !n. f n < PosInf
Proof
    rpt STRIP_TAC
 >> Q.PAT_ASSUM `!n. 0 <= f n`
       ((FULL_SIMP_TAC std_ss) o wrap o (MATCH_MP ext_suminf_def))
 >> Know `!n. SIGMA f (count n) < PosInf`
 >- (GEN_TAC \\
    `!n. SIGMA f (count n) IN IMAGE (\n. SIGMA f (count n)) UNIV`
       by (RW_TAC std_ss [IN_IMAGE, IN_UNIV] >> METIS_TAC []) \\
     METIS_TAC [sup_lt_infty, SPECIFICATION])
 >> DISCH_TAC
 >> Suff `f n <= SIGMA f (count (SUC n))` >- METIS_TAC [let_trans]
 >> `FINITE (count (SUC n))` by RW_TAC std_ss [FINITE_COUNT]
 >> `n IN (count (SUC n))` by RW_TAC real_ss [IN_COUNT]
 >> METIS_TAC [EXTREAL_SUM_IMAGE_POS_MEM_LE]
QED

local val th =
      SIMP_RULE std_ss [GSYM lt_infty]
                       (ONCE_REWRITE_RULE [MONO_NOT_EQ] (Q.SPEC `f` ext_suminf_lt_infty))
in
val ext_suminf_posinf = store_thm
  ("ext_suminf_posinf",
  ``!f. (!n. 0 <= f n) /\ (?n. f n = PosInf) ==> (ext_suminf f = PosInf)``,
    METIS_TAC [th])
end;

Theorem ext_suminf_suminf :
    !r. (!n. 0 <= r n) /\ ext_suminf (\n. Normal (r n)) <> PosInf ==>
        (ext_suminf (\n. Normal (r n)) = Normal (suminf r))
Proof
     GEN_TAC
  >> Suff `(!n. 0 <= r n) ==> ext_suminf (\n. Normal (r n)) <> PosInf ==>
           (ext_suminf (\n. Normal (r n)) = Normal (suminf r))` >- rw []
  >> DISCH_TAC
  >> Know `!n. 0 <= (\n. Normal (r n)) n`
  >- (RW_TAC std_ss [extreal_of_num_def, extreal_le_eq])
  >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def)) >> Rewr'
  >> RW_TAC std_ss []
  >> `!n. FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL]
  >> `(\n. Normal (SIGMA r (count n))) = (\n. Normal ((\n. SIGMA r (count n)) n))` by METIS_TAC []
  >> POP_ORW
  >> `mono_increasing (\n. SIGMA r (count n))`
      by (RW_TAC std_ss [mono_increasing_def,GSYM extreal_le_def]
          >> FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_NORMAL]
          >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
          >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,SUBSET_DEF,IN_COUNT]
          >> DECIDE_TAC)
  >> RW_TAC std_ss [GSYM sup_seq]
  >> FULL_SIMP_TAC std_ss [suminf,sums,REAL_SUM_IMAGE_EQ_sum]
  >> RW_TAC std_ss []
  >> SELECT_ELIM_TAC
  >> RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss [sup_eq,le_infty]
  >> `!n. SIGMA (\n. Normal (r n)) (count n) <= y`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!z. P ==> Q` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
           >> METIS_TAC [])
  >> `!n. 0 <= SIGMA (\n. Normal (r n)) (count n)`
       by (RW_TAC std_ss []
           >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
           >> METIS_TAC [extreal_le_def,extreal_of_num_def])
  >> `y <> NegInf` by METIS_TAC [lt_infty,num_not_infty,lte_trans]
  >> `?z. y = Normal z` by METIS_TAC [extreal_cases]
  >> `!n. SIGMA r (count n) <= z` by METIS_TAC [extreal_le_def,EXTREAL_SUM_IMAGE_NORMAL]
  >> RW_TAC std_ss [GSYM convergent]
  >> MATCH_MP_TAC SEQ_ICONV
  >> FULL_SIMP_TAC std_ss [GREATER_EQ,real_ge,mono_increasing_def]
  >> MATCH_MP_TAC SEQ_BOUNDED_2
  >> METIS_TAC [REAL_SUM_IMAGE_POS]
QED

(* another version with functional composition *)
val ext_suminf_suminf' = store_thm
  ("ext_suminf_suminf'",
  ``!r. (!n. 0 <= r n) /\ (ext_suminf (Normal o r) < PosInf) ==>
        (ext_suminf (Normal o r) = Normal (suminf r))``,
    METIS_TAC [o_DEF, ext_suminf_suminf, lt_infty]);

Theorem ext_suminf_mono :
    !f g. (!n. 0 <= g n) /\ (!n. g n <= f n) ==> (ext_suminf g <= ext_suminf f)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= f n`
 >- (GEN_TAC >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `g n` >> art []) >> DISCH_TAC
 >> RW_TAC std_ss [ext_suminf_def, sup_le', le_sup', IN_IMAGE, IN_UNIV]
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `SIGMA f (count n)`
 >> RW_TAC std_ss []
 >- (MATCH_MP_TAC ((REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n`)
                       EXTREAL_SUM_IMAGE_MONO) \\
     RW_TAC std_ss [COUNT_SUC, IN_INSERT, IN_COUNT] \\
     DISJ1_TAC >> RW_TAC std_ss [] \\
     MATCH_MP_TAC pos_not_neginf >> art [])
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC []
QED

(* removed ‘!n. 0 <= f n’ from antecedents *)
Theorem ext_suminf_eq :
    !f g. (!n. f n = g n) ==> (ext_suminf f = ext_suminf g)
Proof
    rpt STRIP_TAC
 >> Suff ‘f = g’ >- rw []
 >> rw [FUN_EQ_THM]
QED

Theorem ext_suminf_sub :
    !f g. (!n. 0 <= g n /\ g n <= f n) /\ ext_suminf f <> PosInf ==>
          (ext_suminf (\i. f i - g i) = ext_suminf f - ext_suminf g)
Proof
    RW_TAC std_ss []
 >> `!n. 0 <= g n` by PROVE_TAC []
 >> `!n. 0 <= f n` by PROVE_TAC [le_trans]
 >> Know `ext_suminf g <= ext_suminf f`
 >- (RW_TAC std_ss [ext_suminf_def, sup_le', le_sup', IN_IMAGE, IN_UNIV] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `SIGMA f (count n)` \\
     RW_TAC std_ss []
     >- (MATCH_MP_TAC ((REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n`)
                         EXTREAL_SUM_IMAGE_MONO) \\
         RW_TAC std_ss [IN_COUNT] \\
         DISJ1_TAC \\
         METIS_TAC [lt_infty, lte_trans, num_not_infty, le_trans]) \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> `ext_suminf g <> PosInf` by METIS_TAC [lt_infty,let_trans]
 >> `!n. f n <> PosInf` by METIS_TAC [ext_suminf_lt_infty,le_trans,lt_infty]
 >> `!n. g n <> PosInf` by METIS_TAC [ext_suminf_lt_infty,lt_infty]
 >> `!n. f n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty,le_trans]
 >> `!n. g n <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
 >> `?p. !n. f n = Normal (p n)`
       by (Q.EXISTS_TAC `(\n. @r. f n = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `?q. !n. g n = Normal (q n)`
       by (Q.EXISTS_TAC `(\n. @r. g n = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `f = (\n. Normal (p n))` by METIS_TAC []
 >> `g = (\n. Normal (q n))` by METIS_TAC []
 >> FULL_SIMP_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_le_def,
                          extreal_not_infty, extreal_of_num_def]
 >> `!n. p n - q n <= p n`
       by METIS_TAC [REAL_LE_SUB_RADD, REAL_ADD_COMM, REAL_LE_ADDR]
 >> Know `ext_suminf (\i. Normal (p i - q i)) <> PosInf`
 >- (`!n. Normal (p n - q n) <= Normal (p n)` by METIS_TAC [extreal_le_def] \\
     Know `ext_suminf (\i. Normal (p i - q i)) <= ext_suminf (\n. Normal (p n))`
     >- (MATCH_MP_TAC ext_suminf_mono \\
         RW_TAC std_ss [extreal_le_eq, extreal_of_num_def] \\
         METIS_TAC [REAL_SUB_LE]) >> DISCH_TAC \\
     METIS_TAC [lt_infty, let_trans])
 >> `!n. 0 <= p n` by METIS_TAC [REAL_LE_TRANS]
 >> `!n. 0 <= p n - q n` by METIS_TAC [REAL_SUB_LE]
 >> RW_TAC std_ss [ext_suminf_suminf, extreal_sub_def]
 (* stage work *)
 >> Know `!n. 0 <= (\n. Normal (p n)) n`
 >- RW_TAC std_ss [extreal_of_num_def, extreal_le_eq]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def))
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Know `!n. 0 <= (\n. Normal (q n)) n`
 >- RW_TAC std_ss [extreal_of_num_def, extreal_le_eq]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def))
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Know `!n. 0 <= (\i. Normal (p i - q i)) n`
 >- RW_TAC std_ss [extreal_of_num_def, extreal_sub_def, extreal_le_eq]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def))
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> FULL_SIMP_TAC std_ss [sup_eq', le_infty, IN_IMAGE, IN_UNIV]
 >> Know `!n. SIGMA (\n. Normal (p n)) (count n) <= y`
 >- (RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> Know `!n. SIGMA (\n. Normal (q n)) (count n) <= y'`
 >- (RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> Know `!n. SIGMA (\n. Normal (p n - q n)) (count n) <= y''`
 >- (RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!z. Q ==> (z <= y)`   K_TAC
 >> Q.PAT_X_ASSUM `!z. Q ==> (z <= y')`  K_TAC
 >> Q.PAT_X_ASSUM `!z. Q ==> (z <= y'')` K_TAC
 >> Q.PAT_X_ASSUM `sup a <= sup b`       K_TAC
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT]
 >> `0 <= y` by METIS_TAC [REAL_SUM_IMAGE_POS,FINITE_COUNT,extreal_le_def,
                            extreal_of_num_def,le_trans]
 >> `0 <= y'` by METIS_TAC [REAL_SUM_IMAGE_POS,FINITE_COUNT,extreal_le_def,
                             extreal_of_num_def,le_trans]
 >> `0 <= SIGMA (\n. p n - q n) (count n)`
       by (MATCH_MP_TAC REAL_SUM_IMAGE_POS
           >> RW_TAC std_ss [FINITE_COUNT])
 >> `0 <= y''` by METIS_TAC [extreal_le_def,extreal_of_num_def,le_trans]
 >> `y <> NegInf /\ y' <> NegInf /\ y'' <> NegInf`
       by METIS_TAC [lt_infty,num_not_infty,lte_trans]
 >> `?z. y = Normal z` by METIS_TAC [extreal_cases]
 >> `?z'. y' = Normal z'` by METIS_TAC [extreal_cases]
 >> `?z''. y'' = Normal z''` by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_le_def, extreal_not_infty]
 >> RW_TAC std_ss [suminf, sums]
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >- (RW_TAC std_ss [GSYM convergent]
      >> MATCH_MP_TAC SEQ_ICONV
      >> RW_TAC std_ss [GREATER_EQ,real_ge]
      >- (MATCH_MP_TAC SEQ_BOUNDED_2
          >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
          >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `z''`
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
          >> RW_TAC std_ss [FINITE_COUNT])
      >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      >> FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      >> DECIDE_TAC)
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >- (RW_TAC std_ss [GSYM convergent]
      >> MATCH_MP_TAC SEQ_ICONV
      >> RW_TAC std_ss [GREATER_EQ,real_ge]
      >- (MATCH_MP_TAC SEQ_BOUNDED_2
          >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
          >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `z`
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
          >> RW_TAC std_ss [FINITE_COUNT])
      >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      >> FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      >> DECIDE_TAC)
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >- (RW_TAC std_ss [GSYM convergent]
      >> MATCH_MP_TAC SEQ_ICONV
      >> RW_TAC std_ss [GREATER_EQ,real_ge]
      >- (MATCH_MP_TAC SEQ_BOUNDED_2
          >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
          >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `z'`
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
          >> RW_TAC std_ss [FINITE_COUNT])
      >> RW_TAC std_ss [REAL_SUM_IMAGE_EQ_sum,GSYM extreal_le_def]
      >> FULL_SIMP_TAC std_ss [FINITE_COUNT,GSYM EXTREAL_SUM_IMAGE_NORMAL]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
      >> RW_TAC std_ss [extreal_le_def,extreal_of_num_def,FINITE_COUNT,SUBSET_DEF,IN_COUNT]
      >> DECIDE_TAC)
 >> Suff `(\n. sum (0,n) (\i. p i - q i)) --> (x' - x'')` >- METIS_TAC [SEQ_UNIQ]
 >> FULL_SIMP_TAC std_ss [REAL_SUM_IMAGE_EQ_sum]
 >> `(\n. SIGMA (\i. p i - q i) (count n)) =
     (\n. (\n. SIGMA p (count n)) n - (\n.  SIGMA q (count n)) n)`
        by (RW_TAC std_ss [FUN_EQ_THM,real_sub]
            >> `-SIGMA q (count n') = SIGMA (\x. - q x) (count n')`
                by METIS_TAC [REAL_NEG_MINUS1,REAL_SUM_IMAGE_CMUL,FINITE_COUNT]
            >> RW_TAC std_ss [REAL_SUM_IMAGE_ADD,FINITE_COUNT])
 >> POP_ORW
 >> MATCH_MP_TAC SEQ_SUB
 >> RW_TAC std_ss []
QED

Theorem ext_suminf_sum :
    !f n. (!n. 0 <= f n) /\ (!m. n <= m ==> (f m = 0)) ==>
          (ext_suminf f = SIGMA f (count n))
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [ext_suminf_def, sup_eq', IN_IMAGE, IN_UNIV]
 >- (Cases_on `n' <= n`
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
         RW_TAC real_ss [SUBSET_DEF, IN_COUNT, FINITE_COUNT])
     >> `count n SUBSET (count n')` by METIS_TAC [IN_COUNT,NOT_LESS_EQUAL,SUBSET_DEF,LESS_TRANS]
     >> `count n' = (count n) UNION (count n' DIFF (count n))` by METIS_TAC [UNION_DIFF]
     >> POP_ORW
     >> `DISJOINT (count n) (count n' DIFF count n)` by METIS_TAC [DISJOINT_DIFF]
     >> `!n. f n <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lte_trans]
     >> RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_DISJOINT_UNION]
     >> `FINITE (count n' DIFF count n)` by METIS_TAC [FINITE_COUNT,FINITE_DIFF]
     >> (MP_TAC o (REWRITE_RULE [FINITE_COUNT]) o
         (Q.ISPECL [`count n`, `count n' DIFF count n`])) EXTREAL_SUM_IMAGE_DISJOINT_UNION
     >> RW_TAC std_ss []
     >> POP_ASSUM (MP_TAC o Q.SPEC `f`)
     >> RW_TAC std_ss []
     >> Suff `SIGMA f (count n' DIFF count n) = 0`
     >- RW_TAC std_ss [add_rzero,le_refl]
     >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
     >> RW_TAC std_ss [IN_COUNT,IN_DIFF]
     >> METIS_TAC [NOT_LESS])
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC []
QED

val _ = overload_on ("suminf", ``ext_suminf``);

val ext_suminf_zero = store_thm
  ("ext_suminf_zero", ``!f. (!n. f n = 0) ==> (ext_suminf f = 0)``,
    rpt STRIP_TAC
 >> ASSUME_TAC (Q.SPECL [`f`, `0`] ext_suminf_sum)
 >> `0 = SIGMA f (count 0)` by PROVE_TAC [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap)
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [le_refl]);

(* |- suminf (\n. 0) = 0 *)
val ext_suminf_0 = save_thm (* was: suminf_0 *)
  ("ext_suminf_0", SIMP_RULE std_ss [] (Q.SPEC `\n. 0` ext_suminf_zero));

Theorem ext_suminf_pos :
    !f. (!n. 0 <= f n) ==> (0 <= ext_suminf f)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC (REWRITE_RULE [ext_suminf_0]
                               (Q.SPECL [`f`, `\n. 0`] ext_suminf_mono))
 >> rw [le_refl]
QED

val ext_suminf_sing = store_thm
  ("ext_suminf_sing",
  ``!r. 0 <= r ==> (ext_suminf (\n. if n = 0 then r else 0) = r)``,
    GEN_TAC >> STRIP_TAC
 >> Q.ABBREV_TAC `f = (\n :num. if n = 0 then r else 0)`
 >> Suff `ext_suminf f = SIGMA f (count 1)`
 >- (Rewr >> REWRITE_TAC [ONE, COUNT_SUC, COUNT_ZERO] \\
     REWRITE_TAC [EXTREAL_SUM_IMAGE_SING] \\
     Q.UNABBREV_TAC `f` >> SIMP_TAC std_ss [])
 >> MATCH_MP_TAC ext_suminf_sum
 >> Q.UNABBREV_TAC `f`
 >> SIMP_TAC arith_ss []
 >> METIS_TAC [le_refl]);

(* finite version of ext_suminf_add *)
Theorem ext_suminf_sigma :
    !f n. (!i x. i < n ==> 0 <= f i x) ==>
          (SIGMA (ext_suminf o f) (count n) = ext_suminf (\x. SIGMA (\i. f i x) (count n)))
Proof
    REWRITE_TAC [o_DEF]
 >> GEN_TAC >> Induct_on `n`
 >- (DISCH_TAC >> REWRITE_TAC [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY] \\
     MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC ext_suminf_zero \\
     BETA_TAC >> REWRITE_TAC [])
 >> RW_TAC std_ss [COUNT_SUC]
 >> Know `SIGMA (\i. suminf (f i)) (n INSERT count n) =
          (\i. suminf (f i)) n + SIGMA (\i. suminf (f i)) (count n DELETE n)`
 >- (irule EXTREAL_SUM_IMAGE_PROPERTY \\
     REWRITE_TAC [FINITE_COUNT, IN_INSERT, IN_COUNT] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC >> BETA_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC ext_suminf_pos \\
     GEN_TAC >> POP_ASSUM STRIP_ASSUME_TAC \\ (* 2 subgoals, same tactics *)
    `x < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> Rewr' >> BETA_TAC >> REWRITE_TAC [COUNT_DELETE]
 >> Know `!i x. i < n ==> 0 <= f i x`
 >- (rpt STRIP_TAC >> `i < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> DISCH_TAC >> RES_TAC >> POP_ORW
 >> Q.PAT_X_ASSUM `X ==> Y` K_TAC
 >> Know `!x. SIGMA (\i. f i x) (n INSERT count n) =
              (\i. f i x) n + SIGMA (\i. f i x) (count n DELETE n)`
 >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_PROPERTY \\
     REWRITE_TAC [FINITE_COUNT, IN_INSERT, IN_COUNT] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC >> BETA_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     POP_ASSUM STRIP_ASSUME_TAC \\ (* 2 subgoals, same tactics *)
    `x' < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> Rewr' >> BETA_TAC >> REWRITE_TAC [COUNT_DELETE]
 >> `suminf (\x. f n x + SIGMA (\i. f i x) (count n)) =
     suminf (\x. (f n) x + (\y. SIGMA (\i. f i y) (count n)) x)` by PROVE_TAC []
 >> POP_ORW
 >> Suff `suminf (\x. f n x + (\y. SIGMA (\i. f i y) (count n)) x) =
          suminf (f n) + suminf (\x. SIGMA (\i. f i x) (count n))` >- Rewr
 >> MATCH_MP_TAC ext_suminf_add >> GEN_TAC >> BETA_TAC
 >> CONJ_TAC >- (`n < SUC n` by RW_TAC arith_ss [] >> PROVE_TAC [])
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
 >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT]
QED

(* |- !f n.
         (!i x. i < n ==> 0 <= f i x) ==>
         (SIGMA (\x. suminf (f x)) (count n) =
          suminf (\x. SIGMA (\i. f i x) (count n))) *)
val ext_suminf_sigma' = save_thm
  ("ext_suminf_sigma'", REWRITE_RULE [o_DEF] ext_suminf_sigma);

val lemma = prove (
  ``!f n'. (!i. (!m n. m <= n ==> (\x. f x i) m <= (\x. f x i) n)) /\
        (!n i. 0 <= f n i) ==>
        (SIGMA (\i. sup {f k i | k IN univ(:num)}) (count n') =
         sup {SIGMA (\i. f k i) (count n') | k IN UNIV})``,
  RW_TAC std_ss [] THEN Q.ABBREV_TAC `s = count n'` THEN
  `FINITE s` by METIS_TAC [FINITE_COUNT] THEN POP_ASSUM MP_TAC THEN
  Q.SPEC_TAC (`s`,`s`) THEN SET_INDUCT_TAC THENL
  [SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IN_UNIV] THEN
   ONCE_REWRITE_TAC [SET_RULE ``{0 | k | T} = {0}``] THEN
   SIMP_TAC std_ss [sup_sing],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `sup {SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e} | k IN univ(:num)} =
   sup {SIGMA (\i. f k i) s' | k IN univ(:num)} +
   sup {SIGMA (\i. f k i) {e} | k IN univ(:num)}` THENL
  [ALL_TAC,
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   ONCE_REWRITE_TAC [METIS [] ``SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e} =
     (\k. SIGMA (\i. f k i) s') k + (\k. SIGMA (\i. f k i) {e}) k``] THEN
   MATCH_MP_TAC sup_add_mono THEN RW_TAC std_ss [] THENL
   [MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN ASM_SIMP_TAC std_ss [],
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_MONO) THEN
    RW_TAC std_ss [] THEN DISJ1_TAC THEN GEN_TAC THEN
    SIMP_TAC std_ss [lt_infty] THEN DISCH_TAC THEN
    METIS_TAC [lte_trans, num_not_infty, lt_infty],
    ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING],
    ALL_TAC] THEN
   RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING]] THEN
  DISCH_TAC THEN `FINITE {e}` by SIMP_TAC std_ss [FINITE_SING] THEN
  `DISJOINT s' {e}` by ASM_SET_TAC [] THEN
  `!k.
   (!x. x IN (s' UNION {e}) ==> (\i. f k i) x <> NegInf) \/
   (!x. x IN (s' UNION {e}) ==> (\i. f k i) x <> PosInf) ==>
   (SIGMA (\i. f k i) (s' UNION {e}) = SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e})` by
   METIS_TAC [EXTREAL_SUM_IMAGE_DISJOINT_UNION] THEN
  Q_TAC SUFF_TAC `!k. (SIGMA (\i. f k i) (s' UNION {e}) =
       SIGMA (\i. f k i) s' + SIGMA (\i. f k i) {e})` THENL
  [ALL_TAC,
   GEN_TAC THEN POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN
   RW_TAC std_ss [lt_infty] THEN METIS_TAC [lte_trans, num_not_infty, lt_infty]] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC [SET_RULE ``e INSERT s' = s' UNION {e}``] THEN
  ASM_REWRITE_TAC [] THEN
  `(!x. x IN s' UNION {e} ==> (\i. sup {f k i | k IN univ(:num)}) x <> NegInf) \/
   (!x. x IN s' UNION {e} ==> (\i. sup {f k i | k IN univ(:num)}) x <> PosInf) ==>
   (SIGMA (\i. sup {f k i | k IN univ(:num)}) (s' UNION {e}) =
    SIGMA (\i. sup {f k i | k IN univ(:num)}) s' + SIGMA (\i. sup {f k i | k IN univ(:num)}) {e})`
   by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION THEN ASM_SIMP_TAC std_ss []) THEN
  Q_TAC SUFF_TAC `(SIGMA (\i. sup {f k i | k IN univ(:num)}) (s' UNION {e}) =
        SIGMA (\i. sup {f k i | k IN univ(:num)}) s' +
        SIGMA (\i. sup {f k i | k IN univ(:num)}) {e})` THENL
  [ALL_TAC,
   POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN RW_TAC std_ss [sup_eq] THEN
   DISJ1_TAC THEN Q.EXISTS_TAC `f k x` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
   METIS_TAC [lte_trans, num_not_infty, lt_infty]]
 >> Rewr'
 >> ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING]);

Theorem ext_suminf_sup_eq : (* was: suminf_SUP_eq *)
   !(f:num->num->extreal).
     (!i. (!m n. m <= n ==> (\x. f x i) m <= (\x. f x i) n)) /\
     (!n i. 0 <= f n i) ==>
     (suminf (\i. sup {f n i | n IN UNIV}) = sup {suminf (\i. f n i) | n IN UNIV})
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\i. sup {f n i | n IN UNIV}) n`
 >- (RW_TAC set_ss [IN_UNIV, le_sup'] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `f 0 n` >> rw [] \\
     POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `0` >> rw [])
 >> RW_TAC std_ss [ext_suminf_def, IMAGE_DEF]
 >> Suff `!n. SIGMA (\i. sup {f k i | k IN UNIV}) (count n) =
              sup {SIGMA (\i. f k i) (count n) | k IN UNIV}`
 >- (DISCH_TAC \\
     Know `sup {SIGMA (\i. sup {f n i | n IN UNIV}) (count n) | n IN UNIV} =
           sup {sup {SIGMA (\i. f k i) (count n) | k IN UNIV} | n IN UNIV}`
     >- (AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN METIS_TAC []) >> Rewr' \\
     Know
    `sup {sup {(\k n. SIGMA (\i. f k i) (count n)) k n | k IN UNIV} | n IN UNIV} =
     sup {sup {(\k n. SIGMA (\i. f k i) (count n)) k n | n IN UNIV} | k IN UNIV}`
     >- (Q.ABBREV_TAC `g = (\k n. SIGMA (\i. f k i) (count n))` \\
         SIMP_TAC std_ss [sup_comm]) \\
     METIS_TAC [])
 >> ASM_SIMP_TAC std_ss [lemma]
QED

(* ------------------------------------------------------------------------- *)
(*  Further theorems concerning the relationship of suminf and SIGMA         *)
(*  Used by the new measureTheory. (Chun Tian)                               *)
(* ------------------------------------------------------------------------- *)

(* The extreal version of POS_SUMMABLE (util_probTheory) *)
Theorem pos_summable :
    !f. (!n. 0 <= f n) /\ (?r. !n. SIGMA f (count n) <= Normal r) ==>
        suminf f < PosInf
Proof
    GEN_TAC >> STRIP_TAC
 (* 1. f is a normal extreal function *)
 >> Know `!n. f n <> PosInf`
 >- (CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
     Q.PAT_X_ASSUM `!n. SIGMA f (count n) <= Normal r`
       (MP_TAC o (REWRITE_RULE [COUNT_SUC]) o (Q.SPEC `SUC n`)) \\
    `FINITE (count n)` by PROVE_TAC [FINITE_COUNT] \\
    `!x. x IN (n INSERT (count n)) ==> f x <> NegInf` by PROVE_TAC [le_not_infty] \\
     ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, GSYM extreal_lt_def] \\
     Suff `SIGMA f (count n DELETE n) <> NegInf`
     >- RW_TAC std_ss [add_infty, lt_infty] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     CONJ_TAC >- PROVE_TAC [FINITE_DELETE] \\
     rpt STRIP_TAC >> PROVE_TAC [le_not_infty])
 >> DISCH_TAC
 (* 2. g is the real version of f, and `!n. 0 <= g n` *)
 >> Q.ABBREV_TAC `g = real o f`
 >> Know `f = \x. Normal (g x)`
 >- (Q.UNABBREV_TAC `g` >> REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
     REWRITE_TAC [o_DEF] >> BETA_TAC \\
    `!n. f n <> NegInf` by PROVE_TAC [pos_not_neginf] \\
     METIS_TAC [normal_real]) >> DISCH_TAC
 >> Know `!n. 0 <= g n`
 >- (Q.UNABBREV_TAC `g` >> REWRITE_TAC [o_DEF] >> BETA_TAC \\
     POP_ASSUM K_TAC \\ (* useless *)
     GEN_TAC >> `0 <= f n /\ f n <> PosInf` by PROVE_TAC [] \\
     Q.ABBREV_TAC `h = f n` \\
     Cases_on `h` >|
     [ REWRITE_TAC [REAL_LE_REFL, extreal_not_infty, real_def],
       REWRITE_TAC [REAL_LE_REFL, extreal_not_infty, real_def],
       REWRITE_TAC [real_normal] \\
       METIS_TAC [extreal_of_num_def, extreal_le_def] ]) >> DISCH_TAC
 (* 3. g is summable, using POS_SUMMABLE *)
 >> Know `summable g`
 >- (MATCH_MP_TAC POS_SUMMABLE >> art [] \\
     Q.PAT_X_ASSUM `f = \x. Normal (g x)` SUBST_ALL_TAC \\
     REWRITE_TAC [REAL_SUM_IMAGE_EQ_sum] \\
     Q.EXISTS_TAC `r` >> GEN_TAC \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     METIS_TAC [EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT])
 (* stage work *)
 >> RW_TAC std_ss [summable, sums, REAL_SUM_IMAGE_EQ_sum]
 >> Q.PAT_X_ASSUM `!n. 0 <= (\x. Normal (g x)) n`
      (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))
 (* 4. `\n. SIGMA g (count n)` is mono_increasing (for sup_seq) *)
 >> Know `mono_increasing (\n. SIGMA g (count n))`
 >- (REWRITE_TAC [mono_increasing_suc] >> BETA_TAC >> GEN_TAC \\
     MATCH_MP_TAC REAL_SUM_IMAGE_MONO_SET \\
     CONJ_TAC >- PROVE_TAC [FINITE_COUNT] \\
     CONJ_TAC >- PROVE_TAC [FINITE_COUNT] \\
     CONJ_TAC >- ( REWRITE_TAC [SUBSET_DEF, IN_COUNT] >> RW_TAC arith_ss [] ) \\
     rpt STRIP_TAC >> ASM_REWRITE_TAC [])
 >> DISCH_THEN (MP_TAC o (Q.SPEC `s`) o (MATCH_MP sup_seq))
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 (* 5. now swap Normal and SIGMA *)
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NORMAL, FINITE_COUNT, lt_infty]
QED

Theorem pow_half_ser :
    ext_suminf (\n. (1 / 2) pow (n + 1)) = 1
Proof
    Know `(1 / 2) = Normal (1 / 2)`
 >- (`(1 = Normal 1) /\ (2 = Normal 2) /\ 2 <> Normal 0`
        by RW_TAC real_ss [extreal_of_num_def, extreal_11] \\
     ASM_SIMP_TAC real_ss [extreal_div_def, extreal_mul_def, extreal_inv_def] \\
     RW_TAC real_ss [extreal_11, real_div])
 >> DISCH_THEN (ASM_REWRITE_TAC o wrap)
 >> REWRITE_TAC [extreal_pow_def]
 >> `1 = Normal 1` by PROVE_TAC [extreal_of_num_def]
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> REWRITE_TAC [REWRITE_RULE [GSYM extreal_11] (MATCH_MP SUM_UNIQ POW_HALF_SER)]
 >> `(\n. Normal ((1 / 2) pow (n + 1))) = (\n. Normal ((\n. (1 / 2) pow (n + 1)) n))`
        by METIS_TAC []
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> MATCH_MP_TAC ext_suminf_suminf
 >> BETA_TAC
 >> CONJ_TAC (* 2 subgoals *)
 >- (GEN_TAC \\
     Know `0:real <= (1 / 2)` >- (MATCH_MP_TAC REAL_LE_DIV >> RW_TAC real_ss []) \\
     DISCH_THEN (MP_TAC o (MATCH_MP POW_POS)) >> PROVE_TAC [])
 >> REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC pos_summable
 >> BETA_TAC
 >> CONJ_TAC (* 2 subgoals *)
 >- (GEN_TAC \\
     `0 = Normal 0` by PROVE_TAC [extreal_of_num_def] \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     REWRITE_TAC [extreal_le_eq] \\
     Know `0:real <= (1 / 2)` >- (MATCH_MP_TAC REAL_LE_DIV >> RW_TAC real_ss []) \\
     DISCH_THEN (MP_TAC o (MATCH_MP POW_POS)) >> PROVE_TAC [])
 >> Q.EXISTS_TAC `1`
 >> GEN_TAC
 >> `(\n. Normal ((1 / 2) pow (n + 1))) = (\n. Normal ((\n. (1 / 2) pow (n + 1)) n))`
        by METIS_TAC []
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> `FINITE (count n)` by PROVE_TAC [FINITE_COUNT]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP EXTREAL_SUM_IMAGE_NORMAL))
 >> REWRITE_TAC [extreal_le_eq]
 (* SIGMA (\n. (1 / 2) pow (n + 1)) (count n) <= 1 *)
 >> REWRITE_TAC [REAL_SUM_IMAGE_COUNT]
 >> `sum (0,n) (\n. (1 / 2) pow (n + 1)) = (\x. sum (0,x) (\n. (1 / 2) pow (n + 1))) n`
        by METIS_TAC []
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> MATCH_MP_TAC SEQ_MONO_LE
 >> REWRITE_TAC [GSYM sums, POW_HALF_SER]
 >> BETA_TAC
 >> REWRITE_TAC [GSYM REAL_SUM_IMAGE_COUNT]
 >> GEN_TAC >> MATCH_MP_TAC REAL_SUM_IMAGE_MONO_SET
 >> RW_TAC arith_ss [IN_COUNT, FINITE_COUNT, COUNT_SUC, GSYM ADD1, SUBSET_INSERT, SUBSET_REFL]
 >> MATCH_MP_TAC POW_POS
 >> PROVE_TAC [HALF_POS, REAL_LT_LE]
QED

val pow_half_ser' = save_thm (* was: suminf_half_series_ereal *)
  ("pow_half_ser'", (REWRITE_RULE [GSYM ADD1] pow_half_ser));

(* the lemma is non-trivial because it depends on "pos_summable" *)
val summable_ext_suminf = store_thm
  ("summable_ext_suminf",
  ``!f. (!n. 0 <= f n) /\ summable f ==> suminf (Normal o f) < PosInf``,
    REWRITE_TAC [o_DEF]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC pos_summable
 >> BETA_TAC
 >> CONJ_TAC >- ASM_REWRITE_TAC [extreal_le_eq, extreal_of_num_def]
 >> Q.EXISTS_TAC `suminf f`
 (* !n. SIGMA (\n. Normal (f n)) (count n) <= Normal (suminf f) *)
 >> GEN_TAC
 >> Know `SIGMA (\n. Normal (f n)) (count n) = Normal (SIGMA f (count n))`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> METIS_TAC [FINITE_COUNT])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> REWRITE_TAC [extreal_le_eq]
 (* SIGMA f (count n) <= suminf f *)
 >> REWRITE_TAC [REAL_SUM_IMAGE_COUNT]
 >> MATCH_MP_TAC SER_POS_LE
 >> METIS_TAC []);

val summable_ext_suminf_suminf = store_thm
  ("summable_ext_suminf_suminf",
  ``!f. (!n. 0 <= f n) /\ summable f ==> (suminf (Normal o f) = Normal (suminf f))``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC ext_suminf_suminf'
 >> ASM_REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC summable_ext_suminf
 >> ASM_REWRITE_TAC []);

(* added `(!n. 0 <= f n)`, otherwise not true *)
Theorem EXTREAL_SUM_IMAGE_le_suminf :
    !f n. (!n. 0 <= f n) ==> SIGMA f (count n) <= ext_suminf f
Proof
    rpt STRIP_TAC
 >> ASM_SIMP_TAC std_ss [ext_suminf_def]
 >> MATCH_MP_TAC le_sup_imp'
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC []
QED

Theorem ext_suminf_summable :
    !g. (!n. 0 <= g n) /\ suminf g < PosInf ==> summable (real o g)
Proof
    rpt STRIP_TAC
 >> Know `!n. g n < PosInf`
 >- (MATCH_MP_TAC ext_suminf_lt_infty \\
     METIS_TAC [lt_infty]) >> DISCH_TAC
 >> Q.ABBREV_TAC `f = real o g`
 >> Know `g = \n. Normal (f n)`
 >- (RW_TAC std_ss [FUN_EQ_THM] \\
     Q.UNABBREV_TAC `f` >> RW_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC normal_real \\
     METIS_TAC [lt_infty, pos_not_neginf]) >> DISCH_TAC
 >> MATCH_MP_TAC POS_SUMMABLE
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC `f` >> GEN_TAC >> RW_TAC std_ss [o_DEF] \\
     REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
     Know `Normal (real (g n)) = g n`
     >- (MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf]) \\
     DISCH_THEN (REWRITE_TAC o wrap) >> ASM_REWRITE_TAC [])
 >> Q.EXISTS_TAC `real (suminf g)`
 >> GEN_TAC >> REWRITE_TAC [GSYM REAL_SUM_IMAGE_COUNT]
 >> REWRITE_TAC [GSYM extreal_le_eq]
 >> `0 <= suminf g` by PROVE_TAC [ext_suminf_pos]
 >> Know `Normal (real (suminf g)) = suminf g`
 >- (MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 (* Normal (SIGMA f (count n)) <= suminf g *)
 >> Know `Normal (SIGMA f (count n)) = SIGMA (\n. Normal (f n)) (count n)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> PROVE_TAC [FINITE_COUNT])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> Q.PAT_X_ASSUM `g = (\n. Normal (f n))` (REWRITE_TAC o wrap o SYM)
 (* SIGMA g (count n) <= suminf g *)
 >> ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_le_suminf]
QED

val ext_suminf_real_suminf = store_thm
  ("ext_suminf_real_suminf",
  ``!g. (!n. 0 <= g n) /\ suminf g < PosInf ==> (suminf (real o g) = real (suminf g))``,
    rpt STRIP_TAC
 >> Know `!n. g n < PosInf`
 >- (MATCH_MP_TAC ext_suminf_lt_infty \\
     METIS_TAC [lt_infty])
 >> DISCH_TAC
 >> Know `!n. Normal (real (g n)) = g n`
 >- (GEN_TAC >> MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf])
 >> DISCH_TAC
 >> `summable (real o g)` by PROVE_TAC [ext_suminf_summable]
 >> REWRITE_TAC [GSYM extreal_11]
 >> `0 <= suminf g` by PROVE_TAC [ext_suminf_pos]
 >> Know `Normal (real (suminf g)) = suminf g`
 >- (MATCH_MP_TAC normal_real >> METIS_TAC [lt_infty, pos_not_neginf])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> Know `Normal (suminf (real o g)) = suminf (\n. Normal ((real o g) n))`
 >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC ext_suminf_suminf \\
     RW_TAC std_ss [o_DEF] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
       ASM_REWRITE_TAC [],
       (* goal 2 (of 2) *)
       METIS_TAC [lt_infty] ])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> ASM_SIMP_TAC std_ss [o_DEF]
 >> REWRITE_TAC [ETA_AX]);

val SUMINF_2D_suminf = prove (
  ``!(f :num -> num -> real) (g :num -> real) (h :num -> num # num).
       (!m n. 0 <= f m n) /\ (!n. summable (f n) /\ (suminf (f n) = g n)) /\ summable g /\
       BIJ h UNIV (UNIV CROSS UNIV) ==>
       (suminf (UNCURRY f o h) = suminf g)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC SUM_UNIQ
 >> MATCH_MP_TAC SUMINF_2D
 >> ASM_REWRITE_TAC []
 >> GEN_TAC
 >> `summable (f n)` by METIS_TAC []
 >> METIS_TAC [SUMMABLE_SUM]);

val SUMINF_2D_summable = prove (
  ``!(f :num -> num -> real) (g :num -> real) (h :num -> num # num).
       (!m n. 0 <= f m n) /\ (!n. summable (f n) /\ (suminf (f n) = g n)) /\ summable g /\
       BIJ h UNIV (UNIV CROSS UNIV) ==>
       summable (UNCURRY f o h)``,
    rpt STRIP_TAC
 >> REWRITE_TAC [summable]
 >> Q.EXISTS_TAC `suminf g`
 >> MATCH_MP_TAC SUMINF_2D
 >> ASM_REWRITE_TAC []
 >> GEN_TAC
 >> Suff `f n sums suminf (f n)` >- METIS_TAC []
 >> MATCH_MP_TAC SUMMABLE_SUM
 >> ASM_REWRITE_TAC []);

(* extreal version of SUMINF_2D, based on SUMINF_2D_suminf and SUMINF_2D_summable,
   c.f. ext_suminf_2d_infinite (more general, proved from scratch) *)
val ext_suminf_2d = store_thm
  ("ext_suminf_2d",
  ``!(f :num -> num -> extreal) (g :num -> extreal) (h :num -> num # num).
      (!m n. 0 <= f m n) /\
      (!n. ext_suminf (f n) = g n) /\  (* f n sums g n *)
      (ext_suminf g < PosInf) /\       (* summable g *)
      BIJ h UNIV (UNIV CROSS UNIV)
     ==>
      (ext_suminf (UNCURRY f o h) = ext_suminf g)``,
 (* general properties of g and f *)
    rpt STRIP_TAC
 >> `!n. 0 <= g n` by PROVE_TAC [ext_suminf_pos]
 >> `!n. g n < PosInf` by PROVE_TAC [ext_suminf_lt_infty]
 >> `!n. g n <> PosInf /\ g n <> NegInf` by PROVE_TAC [GSYM lt_infty, pos_not_neginf]
 >> `!x. 0 <= UNCURRY f x` by METIS_TAC [UNCURRY]
 >> Know `!m n. f m n < PosInf`
 >- (GEN_TAC >> MATCH_MP_TAC ext_suminf_lt_infty \\
     CONJ_TAC >- ASM_REWRITE_TAC [] \\
     METIS_TAC [lt_infty]) >> DISCH_TAC
 >> `!m n. f m n <> PosInf /\ f m n <> NegInf`
        by PROVE_TAC [GSYM lt_infty, pos_not_neginf]
 (* properties of `UNCURRY f` *)
 >> `!x. UNCURRY f x < PosInf` by METIS_TAC [UNCURRY]
 >> `!x. UNCURRY f x <> PosInf /\ UNCURRY f x <> NegInf`
        by PROVE_TAC [GSYM lt_infty, pos_not_neginf]
 (* convert g into real function g' *)
 >> Q.ABBREV_TAC `g' = real o g`
 >> Know `g = \x. Normal (g' x)`
 >- (Q.UNABBREV_TAC `g'` >> REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
     REWRITE_TAC [o_DEF] >> BETA_TAC \\
     METIS_TAC [normal_real])
 >> DISCH_TAC
 >> ASM_REWRITE_TAC []
 (* properties of g' *)
 >> Know `summable g'`
 >- (Q.UNABBREV_TAC `g'` \\
     MATCH_MP_TAC ext_suminf_summable >> ASM_REWRITE_TAC [])
 >> DISCH_TAC
 (* RHS reduce of the goal *)
 >> Know `suminf (\x. Normal (g' x)) = Normal (suminf g')`
 >- (MATCH_MP_TAC ext_suminf_suminf \\
     reverse CONJ_TAC >- fs [GSYM lt_infty] \\
     Q.UNABBREV_TAC `g'` >> REWRITE_TAC [o_DEF] >> BETA_TAC \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     GEN_TAC >> REWRITE_TAC [GSYM extreal_of_num_def] \\
     METIS_TAC [normal_real])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 (* convert f into real function f' *)
 >> Q.ABBREV_TAC `(f' :num -> num -> real) = (\n. real o f n)`
 >> Know `f = (\n. Normal o f' n)`
 >- (Q.UNABBREV_TAC `f'` >> REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
     REWRITE_TAC [o_DEF] >> BETA_TAC \\
     METIS_TAC [normal_real]) >> DISCH_TAC
 >> `!m n. Normal (f' m n) = f m n` by METIS_TAC [o_DEF]
 (* properties of f' *)
 >> Know `!m n. 0 <= f' m n`
 >- (NTAC 2 GEN_TAC \\
     REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
     METIS_TAC []) >> DISCH_TAC
 >> Know `!n. summable (f' n)`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f'` >> BETA_TAC \\
     MATCH_MP_TAC ext_suminf_summable >> METIS_TAC []) >> DISCH_TAC
 >> Know `!n. suminf (f' n) = g' n`
 >- (GEN_TAC >> REWRITE_TAC [GSYM extreal_11] \\
     Q.PAT_X_ASSUM `g = X`
        (REWRITE_TAC o wrap o (SIMP_RULE std_ss [FUN_EQ_THM]) o (MATCH_MP EQ_SYM)) \\
     Know `Normal (suminf (f' n)) = suminf (\m. Normal ((f' n) m))`
     >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC ext_suminf_suminf \\
         ASM_REWRITE_TAC [] >> BETA_TAC >> METIS_TAC [o_DEF]) >> Rewr \\
     Q.PAT_X_ASSUM `!m n. Normal (f' m n) = f m n` (REWRITE_TAC o wrap) \\
     METIS_TAC []) >> DISCH_TAC
 (* applying SUMINF_2D_summable *)
 >> Know `summable (UNCURRY f' o h)`
 >- (MATCH_MP_TAC SUMINF_2D_summable \\
     Q.EXISTS_TAC `g'` >> ASM_REWRITE_TAC []) >> DISCH_TAC
 >> `!n. 0 <= (UNCURRY f' o h) n` by RW_TAC std_ss [o_DEF, PAIRED_BETA_THM]
 >> Know `UNCURRY f o h = Normal o (UNCURRY f' o h)`
 >- (ASM_REWRITE_TAC [] \\
     PURE_ONCE_REWRITE_TAC [o_DEF] \\
     PURE_ONCE_REWRITE_TAC [PAIRED_BETA_THM] \\
     REWRITE_TAC [o_DEF, PAIRED_BETA_THM] \\
     METIS_TAC []) >> DISCH_TAC
 (* using summable_ext_suminf, indirectly uses "pos_summable"! *)
 >> Know `suminf (UNCURRY f o h) < PosInf`
 >- (ASM_REWRITE_TAC [] \\
     MATCH_MP_TAC summable_ext_suminf >> ASM_REWRITE_TAC []) >> DISCH_TAC
 >> ASM_REWRITE_TAC []
 (* LHS reduce of the goal *)
 >> Know `suminf (Normal o UNCURRY f' o h) = Normal (suminf (UNCURRY f' o h))`
 >- (MATCH_MP_TAC ext_suminf_suminf' \\
     ASM_REWRITE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM `UNCURRY f o h = Normal o UNCURRY f' o h`
        (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
     ASM_REWRITE_TAC []) >> Rewr
 (* remove outer `Normal`s from LHS and RHS *)
 >> REWRITE_TAC [extreal_11]
 (* finally, apply SUMINF_2D_suminf, with all assumptions already proved. *)
 >> MATCH_MP_TAC SUMINF_2D_suminf
 >> ASM_REWRITE_TAC []);

(* some local facts of extreals needed by CARATHEODORY_SEMIRING *)
val lt_inf_epsilon_set = store_thm
  ("lt_inf_epsilon_set",
  ``!P e. 0 < e /\ (?x. x IN P /\ x <> PosInf) /\ inf P <> NegInf ==>
          ?x. x IN P /\ x < inf P + e``,
    METIS_TAC [IN_APP, lt_inf_epsilon]);

val le_inf_epsilon_set = store_thm
  ("le_inf_epsilon_set",
  ``!P e. 0 < e /\ (?x. x IN P /\ x <> PosInf) /\ inf P <> NegInf ==>
          ?x. x IN P /\ x <= inf P + e``,
    rpt STRIP_TAC
 >> `?x. x IN P /\ x < inf P + e` by PROVE_TAC [lt_inf_epsilon_set]
 >> Q.EXISTS_TAC `x'` >> ASM_REWRITE_TAC []
 >> PROVE_TAC [lt_le]);

Theorem pow_half_ser_by_e :
    !e. 0 < e /\ e <> PosInf ==> (e = ext_suminf (\n. e * ((1 / 2) pow (n + 1))))
Proof
    rpt STRIP_TAC
 >> Cases_on `e` >> fs [lt_infty]
 >> `(\n. Normal r * (1 / 2) pow (n + 1)) = (\n. Normal r * (\n. (1 / 2) pow (n + 1)) n)`
        by METIS_TAC []
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> Suff `suminf (\n. Normal r * (\n. (1 / 2) pow (n + 1)) n) =
                      Normal r * suminf (\n. (1 / 2) pow (n + 1))`
 >- (DISCH_THEN (REWRITE_TAC o wrap) \\
     REWRITE_TAC [pow_half_ser, mul_rone])
 >> MATCH_MP_TAC ext_suminf_cmul_alt
 >> CONJ_TAC
 >- (MATCH_MP_TAC REAL_LT_IMP_LE \\
     PROVE_TAC [extreal_lt_eq, extreal_of_num_def])
 >> BETA_TAC
 >> CONJ_TAC >- (MATCH_MP_TAC pow_pos_le \\
                 PROVE_TAC [half_between])
 >> GEN_TAC
 >> METIS_TAC [half_not_infty, pow_not_infty, lt_infty]
QED

val pow_half_pos_lt = store_thm
  ("pow_half_pos_lt", ``!n. 0  < (1 / 2) pow (n + 1)``,
    MATCH_MP_TAC pow_pos_lt >> PROVE_TAC [half_between]);

val pow_half_pos_le = store_thm
  ("pow_half_pos_le", ``!n. 0 <= (1 / 2) pow (n + 1)``,
    MATCH_MP_TAC pow_pos_le >> PROVE_TAC [half_between]);

Theorem ext_suminf_eq_infty_imp :
    !f. (!n. 0 <= f n) /\ (ext_suminf f = PosInf) ==>
        !e. e < PosInf ==> ?n. e <= SIGMA f (count n)
Proof
    rpt STRIP_TAC
 >> `!n. SIGMA f (count n) = (\n. SIGMA f (count n)) n` by PROVE_TAC []
 >> POP_ORW >> MATCH_MP_TAC sup_le_mono
 >> BETA_TAC >> reverse CONJ_TAC
 >- ASM_SIMP_TAC std_ss [GSYM ext_suminf_def]
 >> GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
 >> fs [FINITE_COUNT, COUNT_SUC]
QED

(* the other direction *)
Theorem ext_suminf_eq_infty :
    !f. (!n. 0 <= f n) /\ (!e. e < PosInf ==> ?n. e <= SIGMA f (count n)) ==>
        (ext_suminf f = PosInf)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [GSYM le_infty]
 >> Suff `sup (\x. ?n : num. x = & n) <= suminf f` >- PROVE_TAC [sup_num]
 >> ASM_SIMP_TAC std_ss [ext_suminf_def]
 >> MATCH_MP_TAC sup_le_sup_imp'
 >> SIMP_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> RW_TAC std_ss [IN_APP]
 >> `&n < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def]
 >> RES_TAC
 >> Q.EXISTS_TAC `SIGMA f (count n')` >> art []
 >> Q.EXISTS_TAC `n'` >> REWRITE_TAC []
QED

(* general version of `ext_suminf_2d` without ``ext_suminf g < PosInf`` *)
Theorem ext_suminf_2d_full :
    !(f :num -> num -> extreal) (g :num -> extreal) (h :num -> num # num).
       (!m n. 0 <= f m n) /\ (!n. ext_suminf (f n) = g n) /\
        BIJ h UNIV (UNIV CROSS UNIV) ==>
       (ext_suminf (UNCURRY f o h) = ext_suminf g)
Proof
    rpt STRIP_TAC
 >> Cases_on `suminf g < PosInf`
 >- (MATCH_MP_TAC ext_suminf_2d >> art [])
 >> fs [GSYM lt_infty]
 >> Know `!n. 0 <= g n`
 >- (GEN_TAC \\
     Q.PAT_X_ASSUM `!n. X = g n` (REWRITE_TAC o wrap o GSYM) \\
     MATCH_MP_TAC ext_suminf_pos >> art []) >> DISCH_TAC
(* suminf (UNCURRY f o h) = PosInf *)
 >> Know `suminf g = sup (IMAGE
                           (\n. SIGMA (\i. SIGMA (f i) (count n)) (count n))
                           univ(:num))`
 >- (REWRITE_TAC [GSYM le_antisym] \\
     reverse CONJ_TAC >| (* easy goal first *)
     [ (* goal 1 (of 2) *)
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
       Q.PAT_X_ASSUM `suminf g = PosInf` (ONCE_REWRITE_TAC o wrap o SYM) \\
       POP_ASSUM (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def)) \\
       RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
       MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `SIGMA g (count n)` \\
       reverse CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                            Q.EXISTS_TAC `n` >> REWRITE_TAC []) \\
       irule EXTREAL_SUM_IMAGE_MONO \\
       SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
       CONJ_TAC >- (rpt STRIP_TAC \\
                    Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM) \\
                    ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_le_suminf]) \\
       DISJ1_TAC >> GEN_TAC >> DISCH_TAC >> STRIP_TAC >|
       [ (* goal 1.1 (of 2) *)
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT],
         (* goal 1.2 (of 2) *)
         MATCH_MP_TAC pos_not_neginf \\
         Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM) \\
         MATCH_MP_TAC ext_suminf_pos >> art [] ],
       (* goal 2 (of 2) *)
       POP_ASSUM (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def)) \\
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
      `g = (\n. g n)` by METIS_TAC [] >> POP_ORW \\
       Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM) \\
       Know `SIGMA (\n. suminf (f n)) (count n) = suminf (\x. SIGMA (\i. f i x) (count n))`
       >- (MATCH_MP_TAC ext_suminf_sigma' >> PROVE_TAC []) >> Rewr' \\
       (* stage work *)
       Know `!j. 0 <= (\x. SIGMA (\i. f i x) (count n)) j`
       >- (RW_TAC std_ss [] \\
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
           RW_TAC std_ss [FINITE_COUNT]) \\
       DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def))  \\
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
       RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
       Know `SIGMA (\x. SIGMA (\i. f i x) (count n)) (count n') =
             SIGMA (\x. SIGMA (f x) (count n')) (count n)`
       >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC NESTED_EXTREAL_SUM_IMAGE_REVERSE \\
           REWRITE_TAC [FINITE_COUNT, IN_COUNT] \\
           rpt GEN_TAC >> STRIP_TAC >> MATCH_MP_TAC pos_not_neginf >> art []) >> Rewr' \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC `SIGMA (\i. SIGMA (f i) (count (MAX n n'))) (count (MAX n n'))` \\
       reverse CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                            Q.EXISTS_TAC `MAX n n'` >> REWRITE_TAC []) \\
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE_MONO \\
       RW_TAC arith_ss [] ])
 >> DISCH_TAC
 >> Know `!r. r < PosInf ==> ?n. r <= SIGMA (\i. SIGMA (f i) (count n)) (count n)`
 >- (rpt STRIP_TAC \\
    `!n. SIGMA (\i. SIGMA (f i) (count n)) (count n) =
         (\n. SIGMA (\i. SIGMA (f i) (count n)) (count n)) n` by PROVE_TAC [] >> POP_ORW \\
     MATCH_MP_TAC sup_le_mono >> BETA_TAC \\
     reverse CONJ_TAC >- PROVE_TAC [] \\
     GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE_MONO \\
     RW_TAC arith_ss [])
 >> DISCH_TAC
 >> MATCH_MP_TAC ext_suminf_eq_infty
 >> CONJ_TAC >- RW_TAC std_ss [o_DEF, UNCURRY]
 >> rpt STRIP_TAC
 >> RES_TAC
 >> STRIP_ASSUME_TAC (((Q.SPEC `n`) o (MATCH_MP NUM_2D_BIJ_SMALL_SQUARE))
                          (ASSUME ``BIJ h univ(:num) (univ(:num) CROSS univ(:num))``))
 >> Q.EXISTS_TAC `N`
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `SIGMA (\i. SIGMA (f i) (count n)) (count n)` >> art []
 >> Know `SIGMA (\i. SIGMA (f i) (count n)) (count n) =
          SIGMA (\x. f (FST x) (SND x)) ((count n CROSS count n))`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     REWRITE_TAC [FINITE_COUNT] >> DISJ1_TAC \\
     GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC pos_not_neginf >> art []) >> Rewr'
 >> Know `SIGMA (UNCURRY f o h) (count N) = SIGMA (UNCURRY f) (IMAGE h (count N))`
 >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_IMAGE \\
     SIMP_TAC std_ss [FINITE_COUNT, UNCURRY] \\
     CONJ_TAC >- (DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
                  MATCH_MP_TAC pos_not_neginf >> art []) \\
     MATCH_MP_TAC INJ_IMAGE >> Q.EXISTS_TAC `UNIV` \\
     RW_TAC std_ss [INJ_DEF, IN_COUNT, IN_UNIV] \\
     PROVE_TAC [BIJ_DEF, INJ_DEF, IN_UNIV]) >> Rewr'
 >> Know `UNCURRY f = (\x. f (FST x) (SND x))`
 >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC >> REWRITE_TAC [UNCURRY]) >> Rewr'
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> art []
 >> CONJ_TAC >- (MATCH_MP_TAC FINITE_CROSS >> REWRITE_TAC [FINITE_COUNT])
 >> CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT])
 >> GEN_TAC >> BETA_TAC >> DISCH_TAC >> art []
QED

Theorem harmonic_series_pow_2 :
    ext_suminf (\n. inv (&(SUC n) pow 2)) < PosInf
Proof
    Q.ABBREV_TAC `f :num -> real = \n. inv (&(SUC n) pow 2)`
 >> Suff `(\n. inv (&(SUC n) pow 2)) = Normal o f`
 >- (Rewr' >> MATCH_MP_TAC summable_ext_suminf \\
     rw [HARMONIC_SERIES_POW_2, Abbr `f`])
 >> RW_TAC real_ss [Abbr `f`, o_DEF, FUN_EQ_THM]
 >> Know `(0 :real) < &(SUC n) pow 2`
 >- (MATCH_MP_TAC REAL_POW_LT >> RW_TAC real_ss []) >> DISCH_TAC
 >> `&(SUC n) pow 2 <> (0 :real)` by PROVE_TAC [REAL_LT_IMP_NE]
 >> ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_inv_eq, extreal_pow_def]
QED

(* ------------------------------------------------------------------------- *)
(* Minimum and maximum                                                       *)
(* ------------------------------------------------------------------------- *)

val extreal_min_def = Define
   `extreal_min (x :extreal) y = if x <= y then x else y`;

val extreal_max_def = Define
   `extreal_max (x :extreal) y = if x <= y then y else x`;

val _ = overload_on ("min", Term `extreal_min`);
val _ = overload_on ("max", Term `extreal_max`);

val min_le = store_thm
  ("min_le", ``!z x y. min x y <= z <=> x <= z \/ y <= z``,
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [le_total, le_trans]);

val min_le1 = store_thm
  ("min_le1", ``!x y. min x y <= x``,
    PROVE_TAC [min_le, le_refl]);

val min_le2 = store_thm
  ("min_le2", ``!x y. min x y <= y``,
    PROVE_TAC [min_le, le_refl]);

val le_min = store_thm
  ("le_min", ``!z x y. z <= min x y <=> z <= x /\ z <= y``,
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [le_total, le_trans]);

val min_le2_imp = store_thm
  ("min_le2_imp", ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> min x1 x2 <= min y1 y2``,
    RW_TAC std_ss [le_min]
 >> RW_TAC std_ss [min_le]);

val min_refl = store_thm
  ("min_refl", ``!x. min x x = x``,
    RW_TAC std_ss [extreal_min_def, le_refl]);

val min_comm = store_thm
  ("min_comm", ``!x y. min x y = min y x``,
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [le_antisym, le_total]);

val min_infty = store_thm
  ("min_infty",
  ``!x. (min x PosInf = x) /\ (min PosInf x = x) /\
        (min NegInf x = NegInf) /\ (min x NegInf = NegInf)``,
    RW_TAC std_ss [extreal_min_def, le_infty]);

val le_max = store_thm
  ("le_max", ``!z x y. z <= max x y <=> z <= x \/ z <= y``,
    RW_TAC std_ss [extreal_max_def]
 >> PROVE_TAC [le_total, le_trans]);

val le_max1 = store_thm
  ("le_max1", ``!x y. x <= max x y``,
    PROVE_TAC [le_max, le_refl]);

val le_max2 = store_thm
  ("le_max2", ``!x y. y <= max x y``,
    PROVE_TAC [le_max, le_refl]);

val max_le = store_thm
  ("max_le", ``!z x y. max x y <= z <=> x <= z /\ y <= z``,
    RW_TAC std_ss [extreal_max_def]
 >> PROVE_TAC [le_total, le_trans]);

val max_le2_imp = store_thm
  ("max_le2_imp", ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> max x1 x2 <= max y1 y2``,
    RW_TAC std_ss [max_le]
 >> RW_TAC std_ss [le_max]);

val max_refl = store_thm
  ("max_refl", ``!x. max x x = x``,
    RW_TAC std_ss [extreal_max_def, le_refl]);

val max_comm = store_thm
  ("max_comm", ``!x y. max x y = max y x``,
    RW_TAC std_ss [extreal_max_def]
 >> PROVE_TAC [le_antisym, le_total]);

val max_infty = store_thm
  ("max_infty",
  ``!x. (max x PosInf = PosInf) /\ (max PosInf x = PosInf) /\
        (max NegInf x = x) /\ (max x NegInf = x)``,
    RW_TAC std_ss [extreal_max_def, le_infty]);

val max_reduce = store_thm
  ("max_reduce", ``!x y :extreal. x <= y \/ x < y ==> (max x y = y) /\ (max y x = y)``,
    PROVE_TAC [lt_imp_le, extreal_max_def, max_comm]);

val min_reduce = store_thm
  ("min_reduce", ``!x y :extreal. x <= y \/ x < y ==> (min x y = x) /\ (min y x = x)``,
    PROVE_TAC [lt_imp_le, extreal_min_def, min_comm]);

val lt_max_between = store_thm
  ("lt_max_between", ``!x b d. x < max b d /\ b <= x ==> x < d``,
    RW_TAC std_ss [extreal_max_def]
 >> fs [GSYM extreal_lt_def]
 >> PROVE_TAC [let_antisym]);

val min_le_between = store_thm
  ("min_le_between", ``!x a c. min a c <= x /\ x < a ==> c <= x``,
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [let_antisym]);

Theorem abs_max :
    !x :extreal. abs x = max x (-x)
Proof
    GEN_TAC >> `0 <= x \/ x < 0` by PROVE_TAC [let_total]
 >- (`abs x = x` by PROVE_TAC [GSYM abs_refl] >> POP_ORW \\
     RW_TAC std_ss [GSYM le_antisym, le_max, le_refl, max_le] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `0` >> art [] \\
     POP_ASSUM (REWRITE_TAC o wrap o
                (REWRITE_RULE [Once (GSYM le_neg), neg_0])))
 >> IMP_RES_TAC abs_neg >> POP_ORW
 >> RW_TAC std_ss [GSYM le_antisym, le_max, le_refl, max_le]
 >> MATCH_MP_TAC lt_imp_le
 >> MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC `0` >> art []
 >> POP_ASSUM (REWRITE_TAC o wrap o
                (REWRITE_RULE [Once (GSYM lt_neg), neg_0]))
QED

(* `sup` is the maximal element of any finite non-empty extreal set,
    see also le_sup_imp'.
 *)
Theorem sup_maximal :
    !p. FINITE p /\ p <> {} ==> extreal_sup p IN p
Proof
    Suff `!p. FINITE p ==> p <> {} ==> extreal_sup p IN p` >- rw []
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> Cases_on `p = EMPTY` >- fs [sup_sing]
 >> Suff `sup (e INSERT p) = max e (sup p)`
 >- (Rewr' >> rw [extreal_max_def])
 >> RW_TAC std_ss [sup_eq']
 >| [ (* goal 1 (of 2) *)
      fs [IN_INSERT, le_max] \\
      DISJ2_TAC \\
      MATCH_MP_TAC le_sup_imp' >> art [],
      (* goal 2 (of 2) *)
      POP_ASSUM MATCH_MP_TAC \\
      fs [IN_INSERT, extreal_max_def] \\
      Cases_on `e <= sup p` >> fs [] ]
QED

(* `inf` is the minimal element of any finite non-empty extreal set.
    see also inf_le_imp'.
 *)
Theorem inf_minimal :
    !p. FINITE p /\ p <> {} ==> extreal_inf p IN p
Proof
    Suff `!p. FINITE p ==> p <> {} ==> extreal_inf p IN p` >- rw []
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> Cases_on `p = EMPTY` >- fs [inf_sing]
 >> Suff `inf (e INSERT p) = min e (inf p)`
 >- (Rewr' >> rw [extreal_min_def])
 >> RW_TAC std_ss [inf_eq']
 >| [ (* goal 1 (of 2) *)
      fs [IN_INSERT, min_le] \\
      DISJ2_TAC \\
      MATCH_MP_TAC inf_le_imp' >> art [],
      (* goal 2 (of 2) *)
      POP_ASSUM MATCH_MP_TAC \\
      fs [IN_INSERT, extreal_min_def] \\
      Cases_on `e <= inf p` >> fs [] ]
QED

(* ================================================================= *)
(*   Rational Numbers as a subset of extended real numbers           *)
(* ================================================================= *)

val Q_set_def = Define `Q_set = {x | ?a b. (x = (&a/(&b))) /\ (0 < &b)} UNION
                                {x | ?a b. (x = -(&a/(&b))) /\ (0 < &b)}`;

(* DOUBLE-STRUCK CAPITAL Q *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x211A, tmnm = "Q_set"};

val Q_not_infty = store_thm
  ("Q_not_infty", ``!x. x IN Q_set ==> ?y. x = Normal y``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION]
  >> `&b <> 0:real` by METIS_TAC [extreal_of_num_def,extreal_lt_eq,REAL_LT_IMP_NE]
  >> RW_TAC std_ss [extreal_of_num_def,extreal_div_eq,extreal_ainv_def]);

val Q_COUNTABLE = store_thm
  ("Q_COUNTABLE", ``countable Q_set``,
  RW_TAC std_ss [Q_set_def]
  >> MATCH_MP_TAC union_countable
  >> CONJ_TAC
  >- (RW_TAC std_ss [COUNTABLE_ALT]
      >> MP_TAC NUM_2D_BIJ_NZ_INV
      >> RW_TAC std_ss []
      >> Q.EXISTS_TAC `(\(a,b). &a/(&b)) o f`
      >> RW_TAC std_ss [GSPECIFICATION]
      >> FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV]
      >> PAT_X_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`)
      >> RW_TAC std_ss []
      >> FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,DIFF_DEF,
                                GSPECIFICATION,GSYM REAL_LT_NZ]
      >> `?y. f y = (a,b)` by METIS_TAC [lt_imp_ne,extreal_of_num_def,extreal_lt_eq]
      >> Q.EXISTS_TAC `y`
      >> RW_TAC real_ss [])
  >> RW_TAC std_ss [COUNTABLE_ALT]
  >> MP_TAC NUM_2D_BIJ_NZ_INV
  >> RW_TAC std_ss []
  >> Q.EXISTS_TAC `(\(a,b). -(&a/(&b))) o f`
  >> RW_TAC std_ss [GSPECIFICATION]
  >> FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV]
  >> PAT_X_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`)
  >> RW_TAC std_ss []
  >> FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,
                            DIFF_DEF,GSPECIFICATION,GSYM REAL_LT_NZ]
  >> `?y. f y = (a,b)` by METIS_TAC [lt_imp_ne,extreal_of_num_def,extreal_lt_eq]
  >> Q.EXISTS_TAC `y`
  >> RW_TAC real_ss []);

val NUM_IN_Q = store_thm
  ("NUM_IN_Q", ``!n:num. (&n IN Q_set) /\ (-&n IN Q_set)``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION]
  >- (DISJ1_TAC
      >> Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `1`
      >> RW_TAC std_ss [div_one,lt_01])
  >> DISJ2_TAC
  >> Q.EXISTS_TAC `n` >> Q.EXISTS_TAC `1`
  >> RW_TAC std_ss [div_one,lt_01]);

val Q_INFINITE = store_thm
  ("Q_INFINITE", ``~(FINITE Q_set)``,
  `{x | ?n:num. x = (&n)} SUBSET Q_set`
     by (RW_TAC std_ss [SUBSET_DEF,EXTENSION,GSPECIFICATION]
         >> METIS_TAC [NUM_IN_Q])
  >> Suff `~(FINITE {x | ?n:num. x = (&n)})`
  >- METIS_TAC [INFINITE_SUBSET]
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC (INST_TYPE [alpha |-> ``:num``] INFINITE_INJ)
  >> Q.EXISTS_TAC `(\n. &n)`
  >> Q.EXISTS_TAC `UNIV`
  >> RW_TAC real_ss [INFINITE_NUM_UNIV, INJ_DEF,GSPECIFICATION]
  >- METIS_TAC []
  >> FULL_SIMP_TAC real_ss [extreal_11,extreal_of_num_def]);

val OPP_IN_Q = store_thm
  ("OPP_IN_Q", ``!x. x IN Q_set ==> -x IN Q_set``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION]
  >- (DISJ2_TAC
      >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `b`
      >> RW_TAC real_ss [])
  >> DISJ1_TAC
  >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `b`
  >> RW_TAC real_ss [neg_neg]);

val INV_IN_Q = store_thm
  ("INV_IN_Q", ``!x. (x IN Q_set) /\ (x <> 0) ==> 1/x IN Q_set``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def]
  >- (Cases_on `0:real < &a`
      >- (DISJ1_TAC
          >> `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ,extreal_lt_eq]
          >> `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [extreal_div_eq,extreal_11]
          >> Q.EXISTS_TAC `b` >> Q.EXISTS_TAC `a`
          >> FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_11]
          >> `1:real / (&a / &b) = (1 / 1) / (&a / &b)` by RW_TAC real_ss []
          >> ASM_SIMP_TAC std_ss []
          >> RW_TAC real_ss [div_rat,extreal_lt_eq])
     >> DISJ2_TAC
     >> `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
     >> FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_lt_eq,extreal_11]
     >> `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE]
     >> FULL_SIMP_TAC real_ss [])
  >> Cases_on `0:real < &a`
  >- (DISJ2_TAC
      >> `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ,extreal_lt_eq]
      >> `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [extreal_div_eq,extreal_11,extreal_ainv_def,REAL_NEG_EQ0]
      >> Q.EXISTS_TAC `b` >> Q.EXISTS_TAC `a`
      >> FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_11,extreal_ainv_def]
      >> RW_TAC std_ss [extreal_lt_eq,extreal_ainv_def,extreal_div_eq,real_div,REAL_INV_MUL]
      >> `inv (&b) <> 0:real` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,REAL_INV_EQ_0,REAL_POS_NZ]
      >> RW_TAC real_ss [GSYM REAL_NEG_INV,REAL_NEG_EQ0,REAL_EQ_NEG,REAL_ENTIRE]
      >> RW_TAC real_ss [REAL_INV_MUL,REAL_INV_INV,REAL_MUL_COMM])
  >> DISJ2_TAC
  >> `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
  >> FULL_SIMP_TAC std_ss [extreal_div_eq,extreal_lt_eq,extreal_11,extreal_ainv_def]
  >> `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE,REAL_NEG_EQ0]
  >> FULL_SIMP_TAC real_ss []);

val CMUL_IN_Q = store_thm
  ("CMUL_IN_Q", ``!z:num x. x IN Q_set ==> (&z * x IN Q_set) /\ (-&z * x IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] >|
  [DISJ1_TAC
   >> Q.EXISTS_TAC `z*a` >> Q.EXISTS_TAC `b`
   >>  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   >> RW_TAC real_ss [extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ2_TAC
   >> Q.EXISTS_TAC `z*a` >> Q.EXISTS_TAC `b`
   >>  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   >> RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ2_TAC
   >> Q.EXISTS_TAC `z*a` >> Q.EXISTS_TAC `b`
   >>  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   >> RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC],
   DISJ1_TAC
   >> Q.EXISTS_TAC `z*a` >> Q.EXISTS_TAC `b`
   >>  `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
   >> RW_TAC real_ss [extreal_ainv_def,extreal_mul_def,extreal_div_eq,real_div,REAL_MUL_ASSOC]]);

val ADD_IN_Q = store_thm
  ("ADD_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x+y IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] >|
  [DISJ1_TAC
   >> `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   >> Q.EXISTS_TAC `(a*b' + a'*b)`
   >> Q.EXISTS_TAC `b*b'`
   >> RW_TAC std_ss [extreal_div_eq,extreal_add_def,extreal_11,extreal_lt_eq]
   >> RW_TAC real_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL],

   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   >> Cases_on `&a*(&b')-(&a'* (&b)) = 0:real`
   >- (DISJ1_TAC
       >> Q.EXISTS_TAC `0`
       >> Q.EXISTS_TAC `1`
       >> RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def,GSYM real_sub]
       >> RW_TAC std_ss [REAL_SUB_RAT,REAL_DIV_LZERO,REAL_MUL_COMM])
   >> Cases_on `0:real < &a * (&b') - (&a' * (&b))`
   >- (DISJ1_TAC
       >> Q.EXISTS_TAC `(a * b' - a' * b)`
       >> Q.EXISTS_TAC `b * b'`
       >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
       >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
       >> RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_lt_eq]
       >> RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,GSYM mult_ints]
       >> `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT]
       >> `a' * b < a * b'` by FULL_SIMP_TAC real_ss []
       >> `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
       >> FULL_SIMP_TAC real_ss [REAL_SUB])
   >> DISJ2_TAC
   >> Q.EXISTS_TAC `(a' * b - a * b')`
   >> Q.EXISTS_TAC `b * b'`
   >>  `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   >> RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_lt_eq]
   >> `&a * &b' - &a' * &b < 0:real` by (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] >> FULL_SIMP_TAC real_ss [])
   >> `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]
   >> `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
   >> RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub]
   >> RW_TAC std_ss [GSYM mult_ints]
   >> FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],

   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   >> Cases_on `&a * (&b')-(&a' * (&b)) = 0:real`
   >- (DISJ1_TAC
       >> Q.EXISTS_TAC `0`
       >> Q.EXISTS_TAC `1`
       >> RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def]
       >> ONCE_REWRITE_TAC [GSYM REAL_NEG_EQ0]
       >> RW_TAC std_ss [REAL_NEG_ADD,REAL_NEG_NEG]
       >> RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,REAL_DIV_LZERO,REAL_SUB_0])
   >> Cases_on `0:real < &a * (&b') - (&a' * (&b))`
   >- (DISJ2_TAC
       >> Q.EXISTS_TAC `(a * b' - a' * b)`
       >> Q.EXISTS_TAC `b * b'`
       >> RW_TAC real_ss [extreal_lt_eq,extreal_div_eq,REAL_DIV_LZERO,extreal_11,extreal_ainv_def,extreal_add_def]
       >> RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub]
       >> RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub,GSYM mult_ints]
       >> `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT]
       >> `a' * b < a * b'` by FULL_SIMP_TAC real_ss []
       >> `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
       >> FULL_SIMP_TAC real_ss [REAL_SUB,neg_rat])
   >> DISJ1_TAC
   >> Q.EXISTS_TAC `(a' * b - a * b')`
   >> Q.EXISTS_TAC `b * b'`
   >> RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,extreal_lt_eq]
   >> `&a * &b' - &a' * &b < 0:real` by (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] >> FULL_SIMP_TAC real_ss [])
   >> `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]
   >> `a' * b <> a * b'` by FULL_SIMP_TAC real_ss []
   >> RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_11]
   >> RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM mult_ints]
   >> FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
   DISJ2_TAC
   >> `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
   >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
   >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
   >> Q.EXISTS_TAC `(a * b' + a' * b)`
   >> Q.EXISTS_TAC `b*b'`
   >> RW_TAC std_ss [extreal_div_eq,extreal_ainv_def,extreal_add_def,extreal_11,extreal_lt_eq]
   >> REWRITE_TAC [GSYM mult_ints,GSYM add_ints]
   >> RW_TAC std_ss [REAL_SUB_LNEG,GSYM real_sub,REAL_EQ_NEG]
   >> RW_TAC std_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL]]);

val SUB_IN_Q = store_thm
  ("SUB_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x - y IN Q_set)``,
  RW_TAC std_ss []
  >> `?x1. x = Normal x1` by METIS_TAC [Q_not_infty]
  >> `?y1. y = Normal y1` by METIS_TAC [Q_not_infty]
  >> RW_TAC std_ss [extreal_sub_def]
  >> METIS_TAC [OPP_IN_Q,ADD_IN_Q,extreal_add_def,extreal_sub_def,real_sub,extreal_ainv_def]);

val MUL_IN_Q = store_thm
  ("MUL_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) ==> (x * y IN Q_set)``,
  RW_TAC std_ss [Q_set_def,EXTENSION,GSPECIFICATION,IN_UNION,extreal_of_num_def] >|
 [DISJ1_TAC
  >> `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  >> Q.EXISTS_TAC `a * a'`
  >> Q.EXISTS_TAC `b * b'`
  >> RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq]
  >> FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ2_TAC
  >> `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  >> Q.EXISTS_TAC `a*a'`
  >> Q.EXISTS_TAC `b*b'`
  >> RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  >> FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ2_TAC
  >> `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  >> Q.EXISTS_TAC `a*a'`
  >> Q.EXISTS_TAC `b*b'`
  >> RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  >> FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
  DISJ1_TAC
  >> `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [extreal_lt_eq,REAL_LT_IMP_NE]
  >> `0:real < &(b * b')` by METIS_TAC [extreal_lt_eq,REAL_LT_MUL,mult_ints]
  >> `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE]
  >> Q.EXISTS_TAC `a*a'`
  >> Q.EXISTS_TAC `b*b'`
  >> RW_TAC std_ss [extreal_div_eq,extreal_mul_def,extreal_lt_eq,extreal_ainv_def]
  >> FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT]]);

val DIV_IN_Q = store_thm
  ("DIV_IN_Q", ``!x y. (x IN Q_set) /\ (y IN Q_set) /\ (y <> 0) ==> (x / y IN Q_set)``,
    RW_TAC std_ss []
 >> `?x1. x = Normal x1` by METIS_TAC [Q_not_infty]
 >> `?y1. y = Normal y1` by METIS_TAC [Q_not_infty]
 >> `Normal (inv y1) IN Q_set`
     by METIS_TAC [INV_IN_Q, REAL_INV_1OVER, INV_IN_Q, extreal_div_eq,
                   extreal_inv_def,extreal_of_num_def]
 >> FULL_SIMP_TAC real_ss [extreal_div_def, extreal_of_num_def, extreal_11,
                           extreal_inv_def, extreal_mul_def]
 >> METIS_TAC [MUL_IN_Q, extreal_mul_def]);

val rat_not_infty = store_thm
  ("rat_not_infty", ``!r. r IN Q_set ==> r <> NegInf /\ r <> PosInf``,
  RW_TAC std_ss [Q_set_def,GSPECIFICATION,IN_UNION,extreal_of_num_def]
  >> `&b <> 0:real` by METIS_TAC [extreal_lt_eq,REAL_LT_IMP_NE]
  >> RW_TAC std_ss [extreal_div_eq,extreal_ainv_def]);

val ceiling_def = Define
   `ceiling (Normal x) = LEAST (n:num). x <= &n`;

val CEILING_LBOUND = store_thm
  ("CEILING_LBOUND", ``!x. Normal x <= &(ceiling (Normal x))``,
  RW_TAC std_ss [ceiling_def]
  >> numLib.LEAST_ELIM_TAC
  >> REWRITE_TAC [SIMP_REAL_ARCH]
  >> METIS_TAC [extreal_of_num_def,extreal_le_def]);

val CEILING_UBOUND = store_thm
  ("CEILING_UBOUND", ``!x. (0 <= x) ==> &(ceiling( Normal x)) < (Normal x) + 1``,
  RW_TAC std_ss [ceiling_def,extreal_of_num_def,extreal_add_def,extreal_lt_eq]
  >> numLib.LEAST_ELIM_TAC
  >> REWRITE_TAC [SIMP_REAL_ARCH]
  >> RW_TAC real_ss []
  >> FULL_SIMP_TAC real_ss [GSYM real_lt]
  >> PAT_X_ASSUM ``!m. P`` (MP_TAC o Q.SPEC `n-1`)
  >> RW_TAC real_ss []
  >> Cases_on `n = 0` >- METIS_TAC [REAL_LET_ADD2,REAL_LT_01,REAL_ADD_RID]
  >> `0 < n` by RW_TAC real_ss []
  >> `&(n - 1) < x:real` by RW_TAC real_ss []
  >> `0 <= n-1` by RW_TAC real_ss []
  >> `0:real <= (&(n-1))` by RW_TAC real_ss []
  >> `0 < x` by METIS_TAC [REAL_LET_TRANS]
  >> Cases_on `n = 1` >- METIS_TAC [REAL_LE_REFL,REAL_ADD_RID,REAL_LTE_ADD2,REAL_ADD_COMM]
  >> `0 <> n-1` by RW_TAC real_ss []
  >> `&n - 1 < x` by RW_TAC real_ss [REAL_SUB]
  >> FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]);

val Q_DENSE_IN_R_LEMMA = store_thm
  ("Q_DENSE_IN_R_LEMMA", ``!x y. (0 <= x) /\ (x < y) ==> ?r. (r IN Q_set) /\ (x < r) /\ (r < y)``,
  (rpt Cases >> RW_TAC std_ss [le_infty,lt_infty,extreal_of_num_def,extreal_not_infty])
  >- (Q.EXISTS_TAC `(&ceiling (Normal r)) + 1`
      >> RW_TAC std_ss [extreal_of_num_def,extreal_add_def,lt_infty,extreal_lt_eq]
      >- METIS_TAC [ADD_IN_Q,NUM_IN_Q,extreal_add_def,extreal_of_num_def]
      >> METIS_TAC [extreal_lt_eq,let_trans,REAL_LT_ADDR,REAL_LT_01,extreal_le_def,CEILING_LBOUND,extreal_of_num_def])
  >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
  >> Cases_on `1 < r' - r`
  >- (Q.EXISTS_TAC `Normal (&(ceiling (Normal r')) - 1)`
      >> CONJ_TAC >- METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
      >> RW_TAC std_ss [extreal_lt_eq]
      >- METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LTE_TRANS,CEILING_LBOUND,extreal_of_num_def,extreal_lt_eq,extreal_le_def]
      >> METIS_TAC [REAL_LT_SUB_RADD,CEILING_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE,extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def])
  >> `0 < r' - r` by RW_TAC real_ss [REAL_SUB_LT]
  >> (MP_TAC o Q.SPEC `1`) (((UNDISCH o Q.SPEC `r' - r`) REAL_ARCH))
  >> RW_TAC real_ss []
  >> Suff `?r2. r2 IN Q_set /\ &n * Normal (r) < r2 /\ r2 < &n * Normal (r')`
  >- (RW_TAC real_ss []
      >> `0 < n` by ( RW_TAC real_ss [] >> SPOSE_NOT_THEN ASSUME_TAC >> `n = 0` by RW_TAC real_ss [] >> FULL_SIMP_TAC real_ss [])
      >> `0 < (&n)` by RW_TAC real_ss [extreal_lt_eq,extreal_of_num_def]
      >> Q.EXISTS_TAC `r2 / (&n)`
      >> RW_TAC real_ss [DIV_IN_Q,NUM_IN_Q,lt_imp_ne]
      >- (`?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
          >> FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_div_eq,extreal_lt_eq,extreal_mul_def]
          >> FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE])
      >> `?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
      >> FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_div_eq,extreal_lt_eq,extreal_mul_def]
      >> FULL_SIMP_TAC real_ss [REAL_LT_LDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE])
   >> `1 < &n * r' - &n * r` by FULL_SIMP_TAC real_ss [REAL_SUB_LDISTRIB]
   >> Q.EXISTS_TAC `&(ceiling (&n * Normal (r'))) - 1`
   >> CONJ_TAC >- METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
   >> RW_TAC std_ss [extreal_of_num_def,extreal_mul_def,extreal_sub_def,extreal_lt_eq,extreal_le_def]
   >- METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LTE_TRANS,CEILING_LBOUND,extreal_of_num_def,extreal_lt_eq,extreal_le_def]
   >> `0:real <= &n` by RW_TAC real_ss []
   >> `0:real <= &n * r'` by METIS_TAC [REAL_LE_MUL,REAL_LET_TRANS,REAL_LT_IMP_LE]
   >> METIS_TAC [REAL_LT_SUB_RADD,CEILING_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE,extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def,extreal_mul_def]);

val Q_DENSE_IN_R = store_thm
  ("Q_DENSE_IN_R", ``!x y. (x < y) ==> ?r. (r IN Q_set) /\ (x < r) /\ (r < y)``,
 RW_TAC std_ss []
 >> Cases_on `0<=x` >- RW_TAC std_ss [Q_DENSE_IN_R_LEMMA]
 >> FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
 >> `y <> NegInf` by METIS_TAC [lt_infty]
 >> (Cases_on `y` >> RW_TAC std_ss [])
 >- (Q.EXISTS_TAC `0` >> METIS_TAC [NUM_IN_Q,extreal_of_num_def,extreal_not_infty,lt_infty])
 >> `x <> PosInf` by METIS_TAC [lt_infty,lt_trans,extreal_not_infty,extreal_of_num_def]
 >> Cases_on `x = NegInf`
 >- (Cases_on `0<=r`
     >- (Q.EXISTS_TAC `&ceiling (Normal r)- 1`
         >> RW_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_not_infty,lt_infty,extreal_lt_eq]
         >- METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def]
         >> METIS_TAC [CEILING_UBOUND,REAL_LT_SUB_RADD,extreal_of_num_def,extreal_lt_eq,extreal_add_def])
     >> Q.EXISTS_TAC `- &ceiling (Normal (-r)) - 1`
     >> RW_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_not_infty,lt_infty,extreal_lt_eq,extreal_ainv_def]
     >- METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_sub_def,extreal_of_num_def,OPP_IN_Q,extreal_ainv_def]
     >> (MP_TAC o Q.SPEC `-r`) CEILING_LBOUND
     >> RW_TAC std_ss [extreal_of_num_def,extreal_le_def]
     >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM REAL_LE_NEG])
     >> RW_TAC std_ss [REAL_NEG_NEG]
     >> METIS_TAC [REAL_LT_SUB_RADD,REAL_LET_TRANS,REAL_LT_ADDR,REAL_LT_01])
 >> `?r. x = Normal r` by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_lt_eq]
 >> `Normal (-r') <= &(ceiling (Normal (-r')))` by RW_TAC real_ss [CEILING_LBOUND]
 >> `-Normal (r') <= &ceiling (Normal (-r'))` by METIS_TAC [extreal_ainv_def]
 >> `0 <= Normal (r') + &(ceiling (Normal (-r')))` by METIS_TAC [le_lneg,extreal_of_num_def,extreal_add_def,extreal_not_infty]
 >> `&(ceiling (Normal (-r'))) <> NegInf /\ &(ceiling (Normal (-r'))) <> PosInf`
     by METIS_TAC [extreal_of_num_def,extreal_not_infty]
 >> `Normal (r') + &(ceiling (Normal (-r'))) < Normal (r) + &(ceiling (Normal (-r')))`
    by METIS_TAC [extreal_lt_eq,lt_radd]
 >> Suff `?r2. (r2 IN Q_set) /\ (Normal r' + &ceiling (Normal (-r')) < r2) /\ (r2<Normal r + &ceiling (Normal (-r')))`
 >- (RW_TAC std_ss []
     >> Q.EXISTS_TAC `r2 - &ceiling (Normal (-r'))`
     >> CONJ_TAC >- METIS_TAC [SUB_IN_Q,NUM_IN_Q,extreal_of_num_def]
     >> `?y. r2 = Normal y` by METIS_TAC [Q_not_infty]
     >> FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_lt_eq,extreal_le_def,extreal_sub_def,extreal_add_def]
     >> RW_TAC std_ss [GSYM REAL_LT_ADD_SUB,REAL_LT_SUB_RADD])
 >> RW_TAC std_ss [Q_DENSE_IN_R_LEMMA]);

val COUNTABLE_ENUM_Q = store_thm
  ("COUNTABLE_ENUM_Q",
   ``!c. countable c <=> (c = {}) \/ (?f:extreal->'a. c = IMAGE f Q_set)``,
  RW_TAC std_ss []
  >> reverse EQ_TAC
  >- (NTAC 2 (RW_TAC std_ss [countable_EMPTY])
      >> RW_TAC std_ss [image_countable, Q_COUNTABLE])
  >> reverse (RW_TAC std_ss [COUNTABLE_ALT_BIJ])
  >- (DISJ2_TAC
      >> `countable Q_set` by RW_TAC std_ss [Q_COUNTABLE]
      >> `~(FINITE Q_set)` by RW_TAC std_ss [Q_INFINITE]
      >> (MP_TAC o Q.SPEC `Q_set`) (INST_TYPE [alpha |-> ``:extreal``] COUNTABLE_ALT_BIJ)
      >> RW_TAC std_ss []
      >> (MP_TAC o Q.SPECL [`enumerate Q_set`,`UNIV`,`Q_set`])
                (INST_TYPE [alpha |-> ``:num``, ``:'b`` |-> ``:extreal``] BIJ_INV)
      >> (MP_TAC o Q.SPECL [`enumerate c`,`UNIV`,`c`])
                (INST_TYPE [alpha |-> ``:num``, ``:'b`` |-> ``:'a``] BIJ_INV)
      >> RW_TAC std_ss []
      >> Q.EXISTS_TAC `(enumerate c) o g'`
      >> RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION]
      >> EQ_TAC
      >- (RW_TAC std_ss []
          >> Q.EXISTS_TAC `enumerate Q_set (g x)`
          >- METIS_TAC [BIJ_DEF,INJ_DEF]
          >> METIS_TAC [BIJ_DEF,INJ_DEF])
      >> RW_TAC std_ss []
      >> METIS_TAC [BIJ_DEF,INJ_DEF])
  >> POP_ASSUM MP_TAC
  >> Q.SPEC_TAC (`c`, `c`)
  >> HO_MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss []
  >- (DISJ2_TAC
      >> Q.EXISTS_TAC `K e`
      >> RW_TAC std_ss [EXTENSION, IN_SING, IN_IMAGE, IN_UNIV, K_THM]
      >> EQ_TAC
      >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `0` >> METIS_TAC [NUM_IN_Q])
      >> RW_TAC std_ss [])
  >> DISJ2_TAC
  >> ASSUME_TAC (Q.SPECL [`f:extreal->'a`,`Q_set`,`IMAGE f Q_set`]
                         (INST_TYPE [alpha |-> ``:extreal``, ``:'b`` |-> ``:'a``] INFINITE_INJ))
  >> `~(INJ f Q_set (IMAGE f Q_set))` by METIS_TAC [MONO_NOT,Q_INFINITE]
  >> FULL_SIMP_TAC std_ss [INJ_DEF] >- METIS_TAC [IN_IMAGE]
  >> Q.EXISTS_TAC `(\u. if u=x then e else f u)`
  >> `Q_set = (Q_set DIFF {x}) UNION {x}`
        by (RW_TAC std_ss [DIFF_DEF,UNION_DEF,EXTENSION,GSPECIFICATION,IN_SING] >> METIS_TAC [])
  >> `(IMAGE (\u. if u = x then e else f u) Q_set) =
        (IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x})) UNION
        (IMAGE (\u. if u = x then e else f u) {x})`
        by METIS_TAC [IMAGE_UNION]
  >> `IMAGE (\u. if u = x then e else f u) {x} = {e}`
        by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_SING]
  >> `IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x}) = IMAGE f Q_set`
        by ( RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,DIFF_DEF,IN_UNION,IN_SING] \\
             METIS_TAC[] )
  >> `IMAGE f Q_set = (IMAGE f (Q_set DIFF {x})) UNION (IMAGE f {x})` by METIS_TAC [IMAGE_UNION]
  >> `IMAGE f {x} = {f y}` by RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_SING]
  >> `IMAGE f Q_set = (IMAGE f (Q_set DIFF {x})) UNION {f y}` by METIS_TAC []
  >> `{f y} SUBSET IMAGE f (Q_set DIFF {x})`
        by ( RW_TAC std_ss [SUBSET_DEF,IN_IMAGE,IN_SING] >> Q.EXISTS_TAC `y` \\
             RW_TAC std_ss [IN_DIFF,IN_SING] )
  >> `IMAGE f Q_set = IMAGE f (Q_set DIFF {x})` by METIS_TAC [SUBSET_UNION_ABSORPTION,UNION_COMM]
  >> `IMAGE (\u. if u = x then e else f u) (Q_set DIFF {x}) = IMAGE f (Q_set DIFF {x})`
     by (RW_TAC std_ss [IMAGE_DEF,EXTENSION,GSPECIFICATION,DIFF_DEF,IN_SING] \\
              ( EQ_TAC >- ( RW_TAC std_ss [] >> Q.EXISTS_TAC `u` >> RW_TAC std_ss [] )
                >> RW_TAC std_ss []
                >> Q.EXISTS_TAC `x''`
                >> RW_TAC std_ss [] ))
  >> METIS_TAC [INSERT_SING_UNION,UNION_COMM]);

(* TODO: check (or move to) pred_setTheory *)
val CROSS_COUNTABLE_UNIV = store_thm
  ("CROSS_COUNTABLE_UNIV", ``countable (univ(:num) CROSS univ(:num))``,
  RW_TAC std_ss [COUNTABLE_ALT]
  >> `?(f :num -> num # num). BIJ f UNIV (UNIV CROSS UNIV)` by METIS_TAC [NUM_2D_BIJ_INV]
  >> Q.EXISTS_TAC `f`
  >> RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, CROSS_DEF, IN_UNIV]);

(* `open interval` of extreal sets. c.f. `OPEN_interval` / `CLOSE_interval`
    in real_toplogyTheory, `half_open_interval` in borelTheory *)
val open_interval_def = Define
   `open_interval (a :extreal) b = {x | a < x /\ x < b}`;

(* renamed from `open_intervals_set`, needed in borelTheory (lambda0_premeasure) *)
val open_intervals_def = Define
   `open_intervals = {open_interval a b | T}`;

val rational_intervals_def = Define
   `rational_intervals = {open_interval a b | a IN Q_set /\ b IN Q_set}`;

val COUNTABLE_RATIONAL_INTERVALS = store_thm
  ("COUNTABLE_RATIONAL_INTERVALS", ``countable rational_intervals``,
 (* proof *)
   `rational_intervals = IMAGE (\(a,b). open_interval a b) (Q_set CROSS Q_set)`
     by (RW_TAC std_ss [rational_intervals_def,IMAGE_DEF,EXTENSION,GSPECIFICATION,IN_CROSS]
         >> EQ_TAC
         >- (RW_TAC std_ss []
             >> Q.EXISTS_TAC `x'`
             >> Cases_on `x'`
             >> FULL_SIMP_TAC std_ss [PAIR_EQ])
         >> RW_TAC std_ss []
         >> Q.EXISTS_TAC `x'`
         >> Cases_on `x'`
         >> FULL_SIMP_TAC std_ss [PAIR_EQ,EXTENSION])
  >> METIS_TAC [COUNTABLE_CROSS, Q_COUNTABLE, image_countable]);

(* ------------------------------------------------------------------------- *)
(*  Remainders (tail) of positive infinite summations (unused)               *)
(* ------------------------------------------------------------------------- *)

(* an easy definition learnt from Buday Gergely <buday.gergely@uni-eszterhazy.hu>
val suminf_tail_def = Define `
    suminf_tail f =
      extreal_inf (IMAGE (\n. suminf f - SIGMA f (count n)) UNIV)`;
 *)

(* alternative hard definitions:
val suminf_tail_alt = store_thm
  ("suminf_tail_alt",
  ``!f. suminf_tail f = extreal_inf (IMAGE (\n. suminf (\i. f (n + i))) UNIV)``,
    ...);

val suminf_tail_alt2 = store_thm
  ("suminf_tail_alt2",
  ``!f. suminf_tail f =
        extreal_inf (IMAGE (\n. suminf (\i. if i < n then 0 else f i)) UNIV)``,
    ...);
 *)

(* c.f. [2, p.260 (364)]
val pos_summable_tail = store_thm
  ("pos_summable_tail",
  ``!f. (!n. 0 <= f n) /\ suminf f < PosInf ==> (suminf_tail f = 0)``,
    ...);
 *)

(* ------------------------------------------------------------------------- *)
(*  Finite Product Images (PI) of extreals                                   *)
(* ------------------------------------------------------------------------- *)

val EXTREAL_PROD_IMAGE_DEF = new_definition
  ("EXTREAL_PROD_IMAGE_DEF",
  ``EXTREAL_PROD_IMAGE f s = ITSET (\e acc. f e * acc) s (1 :extreal)``);

val _ = overload_on ("PI", ``EXTREAL_PROD_IMAGE``);
val _ = Unicode.unicode_version {u = UTF8.chr 0x220F, tmnm = "PI"};
val _ = TeX_notation {hol = UTF8.chr 0x220F, TeX = ("\\HOLTokenPI{}", 1)};
val _ = TeX_notation {hol = "PI"           , TeX = ("\\HOLTokenPI{}", 1)};

val EXTREAL_PROD_IMAGE_THM = store_thm
  ("EXTREAL_PROD_IMAGE_THM",
  ``!f. (EXTREAL_PROD_IMAGE f {} = 1) /\
        !e s. FINITE s ==>
             (EXTREAL_PROD_IMAGE f (e INSERT s) = f e * EXTREAL_PROD_IMAGE f (s DELETE e))``,
    rpt STRIP_TAC
 >- SIMP_TAC (srw_ss()) [ITSET_THM, EXTREAL_PROD_IMAGE_DEF]
 >> SIMP_TAC (srw_ss()) [EXTREAL_PROD_IMAGE_DEF]
 >> Q.ABBREV_TAC `g = \e acc. f e * acc`
 >> Suff `ITSET g (e INSERT s) 1 = g e (ITSET g (s DELETE e) 1)`
 >- (Q.UNABBREV_TAC `g` >> SRW_TAC [] [])
 >> MATCH_MP_TAC COMMUTING_ITSET_RECURSES
 >> Q.UNABBREV_TAC `g`
 >> RW_TAC std_ss []
 >> METIS_TAC [mul_assoc, mul_comm]);

val EXTREAL_PROD_IMAGE_EMPTY = store_thm
  ("EXTREAL_PROD_IMAGE_EMPTY", ``!f. EXTREAL_PROD_IMAGE f {} = 1``,
    SRW_TAC [] [EXTREAL_PROD_IMAGE_THM]);

val EXTREAL_PROD_IMAGE_SING = store_thm
  ("EXTREAL_PROD_IMAGE_SING", ``!f e. EXTREAL_PROD_IMAGE f {e} = f e``,
    SRW_TAC [] [EXTREAL_PROD_IMAGE_THM, mul_rone]);

val EXTREAL_PROD_IMAGE_PROPERTY = store_thm
  ("EXTREAL_PROD_IMAGE_PROPERTY",
  ``!f e s. FINITE s ==> (EXTREAL_PROD_IMAGE f (e INSERT s) =
                          f e * EXTREAL_PROD_IMAGE f (s DELETE e))``,
    PROVE_TAC [EXTREAL_PROD_IMAGE_THM]);

val EXTREAL_PROD_IMAGE_PAIR = store_thm
  ("EXTREAL_PROD_IMAGE_PAIR",
  ``!f a b. a <> b ==> (EXTREAL_PROD_IMAGE f {a; b} = f a * f b)``,
    RW_TAC std_ss []
 >> `FINITE {b}` by PROVE_TAC [FINITE_SING]
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`f`, `a`]) o (MATCH_MP EXTREAL_PROD_IMAGE_PROPERTY))
 >> RW_TAC std_ss []
 >> Know `{b} DELETE a = {b}`
 >- (RW_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DELETE, IN_SING] \\
     EQ_TAC >> rpt STRIP_TAC >> fs []) >> Rewr'
 >> REWRITE_TAC [EXTREAL_PROD_IMAGE_SING]);

val EXTREAL_PROD_IMAGE_EQ = store_thm
  ("EXTREAL_PROD_IMAGE_EQ",
  ``!s. FINITE s ==>
        !f f'. (!x. x IN s ==> (f x = f' x)) ==>
               (EXTREAL_PROD_IMAGE f s = EXTREAL_PROD_IMAGE f' s)``,
    Suff `!s. FINITE s ==>
              (\s. !f f'. (!x. x IN s ==> (f x = f' x)) ==>
                  (EXTREAL_PROD_IMAGE f s = EXTREAL_PROD_IMAGE f' s)) s`
 >- PROVE_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_PROD_IMAGE_EMPTY]
 >> FULL_SIMP_TAC std_ss [EXTREAL_PROD_IMAGE_PROPERTY, DELETE_NON_ELEMENT,
                          IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM]
 >> METIS_TAC []);

val EXTREAL_PROD_IMAGE_DISJOINT_UNION = store_thm
  ("EXTREAL_PROD_IMAGE_DISJOINT_UNION",
  ``!s s'. FINITE s /\ FINITE s' /\ DISJOINT s s' ==>
           !f. (EXTREAL_PROD_IMAGE f (s UNION s') =
                EXTREAL_PROD_IMAGE f s * EXTREAL_PROD_IMAGE f s')``,
    Suff `!s. FINITE s ==>
             (\s. !s'. FINITE s' ==>
                      (\s'. DISJOINT s s' ==>
                            !f. (EXTREAL_PROD_IMAGE f (s UNION s') =
                                 EXTREAL_PROD_IMAGE f s *
                                 EXTREAL_PROD_IMAGE f s')) s') s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- RW_TAC std_ss [DISJOINT_EMPTY, UNION_EMPTY, EXTREAL_PROD_IMAGE_EMPTY, mul_lone]
 >> rpt STRIP_TAC
 >> CONV_TAC (BETA_CONV) >> MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- RW_TAC std_ss [DISJOINT_EMPTY, UNION_EMPTY, EXTREAL_PROD_IMAGE_EMPTY, mul_rone]
 >> FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
 >> ONCE_REWRITE_TAC [DISJOINT_SYM]
 >> RW_TAC std_ss [INSERT_UNION, DISJOINT_INSERT, IN_INSERT]
 >> FULL_SIMP_TAC std_ss [DISJOINT_SYM]
 >> ONCE_REWRITE_TAC [UNION_COMM] >> RW_TAC std_ss [INSERT_UNION]
 >> ONCE_REWRITE_TAC [UNION_COMM] >> ONCE_REWRITE_TAC [INSERT_COMM]
 >> `FINITE (e INSERT s UNION s')` by RW_TAC std_ss [FINITE_INSERT, FINITE_UNION]
 >> Q.ABBREV_TAC `Q = e INSERT s UNION s'`
 >> FULL_SIMP_TAC std_ss [EXTREAL_PROD_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
 >> Q.UNABBREV_TAC `Q`
 >> `~(e' IN (e INSERT s UNION s'))`
      by (RW_TAC std_ss [IN_INSERT, IN_UNION] \\
          FULL_SIMP_TAC std_ss [EXTREAL_PROD_IMAGE_PROPERTY, DELETE_NON_ELEMENT])
 >> `~(e IN (s UNION s'))` by METIS_TAC [IN_UNION, DELETE_NON_ELEMENT]
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT, EXTREAL_PROD_IMAGE_PROPERTY, FINITE_UNION]
 >> FULL_SIMP_TAC std_ss [IN_INSERT]
 >> RW_TAC std_ss [mul_assoc]
 >> `f e' * (f e * EXTREAL_SUM_IMAGE f s * EXTREAL_SUM_IMAGE f s') =
       (f e * (EXTREAL_SUM_IMAGE f s * EXTREAL_SUM_IMAGE f s')) * f e'`
              by METIS_TAC [mul_comm, mul_assoc, IN_INSERT]
 >> POP_ORW
 >> RW_TAC std_ss [mul_assoc]
 >> METIS_TAC [mul_comm, mul_assoc]);

val EXTREAL_PROD_IMAGE_IMAGE = store_thm
  ("EXTREAL_PROD_IMAGE_IMAGE",
  ``!s. FINITE s ==>
        !f'. INJ f' s (IMAGE f' s) ==>
             !f. EXTREAL_PROD_IMAGE f (IMAGE f' s) = EXTREAL_PROD_IMAGE (f o f') s``,
 (* proof *)
    Suff `!s. FINITE s ==>
             (\s. !f'. INJ f' s (IMAGE f' s) ==>
                       !f. EXTREAL_PROD_IMAGE f (IMAGE f' s) =
                           EXTREAL_PROD_IMAGE (f o f') s) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_PROD_IMAGE_EMPTY, IMAGE_EMPTY, IMAGE_INSERT, INJ_DEF]
 >> `FINITE (IMAGE f' s)` by METIS_TAC [IMAGE_FINITE]
 >> RW_TAC std_ss [EXTREAL_PROD_IMAGE_PROPERTY]
 >> `~(f' e IN IMAGE f' s)`
        by (RW_TAC std_ss [IN_IMAGE] >> reverse (Cases_on `x IN s`)
            >- ASM_REWRITE_TAC [] >> METIS_TAC [IN_INSERT])
 >> `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
 >> `(IMAGE f' s) DELETE f' e = IMAGE f' s` by METIS_TAC [DELETE_NON_ELEMENT]
 >> ASM_REWRITE_TAC []
 >> `(!x. x IN s ==> f' x IN IMAGE f' s)` by METIS_TAC [IN_IMAGE]
 >> `(!x y. x IN s /\ y IN s ==> (f' x = f' y) ==> (x = y))` by METIS_TAC [IN_INSERT]
 >> FULL_SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Some prelimitaries of Radon-Nikodym Theorem                               *)
(* ------------------------------------------------------------------------- *)

val seq_sup_def = Define
  `(seq_sup P 0       = @r. r IN P /\ sup P < r + 1) /\
   (seq_sup P (SUC n) = @r. r IN P /\ sup P < r + Normal ((1 / 2) pow (SUC n)) /\
                           (seq_sup P n) < r /\ r < sup P)`;

val EXTREAL_SUP_SEQ = store_thm
  ("EXTREAL_SUP_SEQ",
  ``!P. (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) ==>
        ?x. (!n. x n IN P) /\ (!n. x n <= x (SUC n)) /\ (sup (IMAGE x UNIV) = sup P)``,
  RW_TAC std_ss []
  >> Cases_on `?z. P z /\ (z = sup P)`
  >- (Q.EXISTS_TAC `(\i. sup P)`
      >> RW_TAC std_ss [le_refl,SPECIFICATION]
      >> `IMAGE (\i:num. sup P) UNIV = (\i. i = sup P)`
           by RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_UNIV,IN_ABS]
      >> RW_TAC std_ss [sup_const])
  >> Cases_on `!x. P x ==> (x = NegInf)`
  >- (`sup P = NegInf` by METIS_TAC [sup_const_alt]
      >> Q.EXISTS_TAC `(\n. NegInf)`
      >> FULL_SIMP_TAC std_ss [le_refl]
      >> RW_TAC std_ss []
      >- METIS_TAC []
      >> METIS_TAC [UNIV_NOT_EMPTY,sup_const_over_set])
  >> FULL_SIMP_TAC std_ss []
  >> Q.EXISTS_TAC `seq_sup P`
  >> FULL_SIMP_TAC std_ss []
  >> `sup P <> PosInf` by METIS_TAC [sup_le,lt_infty,let_trans]
  >> `!x. P x ==> x < sup P` by METIS_TAC [lt_le,le_sup_imp]
  >> `!e. 0 < e ==> ?x. P x /\ sup P < x + e`
       by (RW_TAC std_ss [] >> MATCH_MP_TAC sup_lt_epsilon >> METIS_TAC [])
  >> `!n. 0:real < (1 / 2) pow n` by METIS_TAC [HALF_POS,REAL_POW_LT]
  >> `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
  >> `!n. seq_sup P n IN P`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >> METIS_TAC [lt_01,SPECIFICATION])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >> `?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
          >> rename1 `seq_sup P n < x2`
          >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
          >> rename1 `sup P < x3 + _`
          >> Q.EXISTS_TAC `max x2 x3`
          >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
          >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
              >> `x3 +  Normal ((1 / 2) pow (SUC n)) <= x2 +  Normal ((1 / 2) pow (SUC n))`
                  by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lte_trans])
  >> `!n. seq_sup P n <= seq_sup P (SUC n)`
      by (RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> rename1 `sup_sup P n < x2`
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> rename1 `sup P < x3 + _`
              >> Q.EXISTS_TAC `max x2 x3`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x3 + Normal ((1 / 2) pow (SUC n)) <= x2 + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss []
  >> `!n. sup P <= seq_sup P n + Normal ((1 / 2) pow n)`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def,pow,GSYM extreal_of_num_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >- METIS_TAC [lt_01,SPECIFICATION]
              >> METIS_TAC [lt_le])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> rename1 `sup_sup P n < x2`
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> rename1 `sup P < x3 + _`
              >> Q.EXISTS_TAC `max x2 x3`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x3 + Normal ((1 / 2) pow (SUC n)) <= x2 + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [SPECIFICATION,lt_le])
  >> MATCH_MP_TAC le_epsilon
  >> RW_TAC std_ss []
  >> `e <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lt_trans]
  >> `?r. e = Normal r` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss []
  >> `?n. Normal ((1 / 2) pow n) < Normal r` by METIS_TAC [EXTREAL_ARCH_POW_INV]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `seq_sup P n + Normal ((1 / 2) pow n)`
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC le_add2
  >> FULL_SIMP_TAC std_ss [lt_le]
  >> Q.PAT_X_ASSUM `!z. IMAGE (seq_sup P) UNIV z ==> z <= y` MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  >> METIS_TAC []);

val EXTREAL_SUP_FUN_SEQ_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_IMAGE",
  ``!(P:extreal->bool) (P':('a->extreal)->bool) f.
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P')
           ==> ?g. (!n:num. g n IN P') /\
                   (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  rpt STRIP_TAC
  >> `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (sup (IMAGE y UNIV) = sup P)`
     by METIS_TAC [EXTREAL_SUP_SEQ]
  >> Q.EXISTS_TAC `(\n. @r. (r IN P') /\ (f r  = y n))`
  >> `(\n. f (@(r :'a -> extreal). r IN (P' :('a -> extreal) -> bool) /\
                                  ((f :('a -> extreal) -> extreal) r = (y :num -> extreal) n))) = y`
  by (rw [FUN_EQ_THM] >> SELECT_ELIM_TAC
      >> RW_TAC std_ss []
      >> METIS_TAC [IN_IMAGE])
  >> ASM_SIMP_TAC std_ss []
  >> RW_TAC std_ss []
  >- (SELECT_ELIM_TAC
      >> RW_TAC std_ss []
      >> METIS_TAC [IN_IMAGE]));

val max_fn_seq_def = Define `
   (max_fn_seq g 0 x  = g 0 x) /\
   (max_fn_seq g (SUC n) x = max (max_fn_seq g n x) (g (SUC n) x))`;

val max_fn_seq_mono = store_thm
  ("max_fn_seq_mono", ``!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x``,
    RW_TAC std_ss [max_fn_seq_def,extreal_max_def,le_refl]);

val EXTREAL_SUP_FUN_SEQ_MONO_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_MONO_IMAGE",
  ``!f (P:extreal->bool) (P':('a->extreal)->bool).
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
       (!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
       (!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')
      ==>
       ?g. (!n. g n IN P') /\
           (!x n. g n x <= g (SUC n) x) /\
           (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
    rpt STRIP_TAC
  >> `?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)`
      by METIS_TAC [EXTREAL_SUP_FUN_SEQ_IMAGE]
  >> Q.EXISTS_TAC `max_fn_seq g`
  >> `!n. max_fn_seq g n IN P'`
      by (Induct
          >- (`max_fn_seq g 0 = g 0` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> METIS_TAC [])
              >> `max_fn_seq g (SUC n) = (\x. max (max_fn_seq g n x) (g (SUC n) x))`
                  by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> RW_TAC std_ss []
              >> METIS_TAC [])
  >> `!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x`
      by RW_TAC real_ss [max_fn_seq_def,extreal_max_def,le_refl]
  >> CONJ_TAC >- RW_TAC std_ss []
  >> CONJ_TAC >- RW_TAC std_ss []
  >> `!n. (!x. g n x <= max_fn_seq g n x)`
      by (Induct >- RW_TAC std_ss [max_fn_seq_def,le_refl]
          >> METIS_TAC [le_max2,max_fn_seq_def])
  >> `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
  >> `sup (IMAGE (\n. f (g n)) UNIV) <= sup (IMAGE (\n. f (max_fn_seq g n)) UNIV)`
      by (MATCH_MP_TAC sup_le_sup_imp
          >> RW_TAC std_ss []
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> Q.EXISTS_TAC `f (max_fn_seq g n)`
          >> RW_TAC std_ss []
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
  >> `sup (IMAGE (\n. f (max_fn_seq g n)) UNIV) <= sup P`
      by (RW_TAC std_ss [sup_le]
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> MATCH_MP_TAC le_sup_imp
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE]
          >> METIS_TAC [])
  >> METIS_TAC [le_antisym]);

val _ = export_theory();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales. Cambridge University Press (2005).
  [2] Fichtenholz, G.M.: Differential- und Integralrechnung (Differential and Integral
      Calculus), Vol.2. (1967).
  [3] Harrison, J.: Constructing the real numbers in HOL. TPHOLs. (1992).
  [4] Wikipedia: https://en.wikipedia.org/wiki/Limit_superior_and_limit_inferior
 *)
