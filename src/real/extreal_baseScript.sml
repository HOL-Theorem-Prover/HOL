(* ------------------------------------------------------------------------- *)
(* Extended Real Numbers - Basic Theory                                      *)
(*                                                                           *)
(* Original Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013, 2015)   *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Updated and further enriched by Chun Tian (2018 - 2023)                   *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open combinTheory tautLib prim_recTheory arithmeticTheory numLib hurdUtils;

open realTheory realLib iterateTheory;

val _ = new_theory "extreal_base";

Datatype : (* extreal_TY_DEF *)
    extreal = NegInf | PosInf | Normal real
End

(* INFINITY, the vertical position of UTF8.chr 0x2212 is better than "-" *)
val _ = Unicode.unicode_version {u = "+" ^ UTF8.chr 0x221E,
                                 tmnm = "PosInf"};
val _ = Unicode.unicode_version {u = UTF8.chr 0x2212 ^ UTF8.chr 0x221E,
                                 tmnm = "NegInf"};

val _ = TeX_notation {hol = "+" ^ UTF8.chr 0x221E,
                      TeX = ("\\ensuremath{+\\infty}", 1)};

val _ = TeX_notation {hol = UTF8.chr 0x2212 ^ UTF8.chr 0x221E,
                      TeX = ("\\ensuremath{-\\infty}", 1)};

Definition extreal_of_num_def :
    extreal_of_num n = Normal (&n)
End

(* from now on, ``0x`` is intepreted as ``0 :extreal`` *)
val _ = add_numeral_form (#"x", SOME "extreal_of_num");

Definition real_def :
    real x = if (x = NegInf) \/ (x = PosInf) then (0 :real)
             else @r. x = Normal r
End

Theorem real_normal[simp] :
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

Theorem extreal_cases :
    !x. (x = NegInf) \/ (x = PosInf) \/ (?r. x = Normal r)
Proof
    Cases >> RW_TAC std_ss []
QED

Theorem extreal_not_infty[simp] :
    !x. (Normal x <> NegInf) /\ (Normal x <> PosInf)
Proof
    RW_TAC std_ss []
QED

val extreal_distinct = DB.fetch "-" "extreal_distinct";

Theorem extreal_eq_zero[simp] :
    !x. (Normal x = 0) <=> (x = 0)
Proof
    RW_TAC std_ss [extreal_of_num_def]
QED

Theorem num_not_infty[simp] :
    !n. (&n <> NegInf) /\ (&n <> PosInf)
Proof
    RW_TAC std_ss [extreal_of_num_def]
QED

Theorem real_0[simp] :
    real 0 = 0
Proof
    rw [extreal_of_num_def]
QED

(* ------------------------------------------------------------------------- *)
(*     Definitions of Arithmetic Operations                                  *)
(* ------------------------------------------------------------------------- *)

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

(* This definition never changed but is moved here to be used by extreal_sub *)
Definition extreal_ainv_def :
   (extreal_ainv NegInf = PosInf) /\
   (extreal_ainv PosInf = NegInf) /\
   (extreal_ainv (Normal x) = Normal (- x))
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
Definition extreal_sub :
    extreal_sub x y = extreal_add x (extreal_ainv y)
End

(* The previous definition now becomes a theorem *)
Theorem extreal_sub_def :
   (extreal_sub (Normal x) (Normal y) = Normal (x - y)) /\
   (extreal_sub PosInf (Normal x) = PosInf) /\
   (extreal_sub NegInf (Normal x) = NegInf) /\
   (extreal_sub (Normal x) NegInf = PosInf) /\
   (extreal_sub (Normal x) PosInf = NegInf) /\
   (extreal_sub NegInf PosInf = NegInf) /\
   (extreal_sub PosInf NegInf = PosInf)
Proof
   rw [extreal_sub, extreal_add_def, extreal_ainv_def, real_sub]
QED

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

Overload "+"  = “extreal_add”
Overload "-"  = “extreal_sub”
Overload "*"  = “extreal_mul”
Overload "<=" = “extreal_le”

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

Definition extreal_abs_def :
   (extreal_abs (Normal x) = Normal (abs x)) /\
   (extreal_abs _ = PosInf)
End

Definition extreal_pow_def :
   (extreal_pow (Normal a) n = Normal (a pow n)) /\
   (extreal_pow PosInf n = (if n = 0 then Normal 1 else PosInf)) /\
   (extreal_pow NegInf n =
       (if n = 0 then Normal 1 else (if (EVEN n) then PosInf else NegInf)))
End

Definition extreal_sqrt_def :
   (extreal_sqrt (Normal x) = Normal (sqrt x)) /\
   (extreal_sqrt PosInf = PosInf)
End

Overload "/"            = “extreal_div”
Overload "<"            = “extreal_lt”
Overload "~"            = “extreal_ainv”
Overload numeric_negate = “extreal_ainv”
Overload "~"            = “bool$~”
Overload "¬"            = “bool$~” (* UOK *)
Overload inv            = “extreal_inv”
Overload realinv        = “extreal_inv”
Overload abs            = “extreal_abs”
Overload pow            = “extreal_pow”
Overload sqrt           = “extreal_sqrt”

(* pow-2 integrals appear in Variances and many other probability lemmas *)
val _ = overload_on (UnicodeChars.sup_2, “\x :extreal. x pow 2”);

(* pow-3 integrals appear in Liapounov's form of the central limit theorem *)
val _ = overload_on (UnicodeChars.sup_3, “\x :extreal. x pow 3”);

(* pow-4 integrals appear in Cantelli's Strong Law of Large Numbers *)
val _ = add_rule {fixity = Suffix 2100,
                  term_name = UnicodeChars.sup_4,
                  block_style = (AroundEachPhrase,(PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK UnicodeChars.sup_4]};

val _ = overload_on (UnicodeChars.sup_4, “\x :extreal. x pow 4”);
val _ = TeX_notation {hol = UnicodeChars.sup_4,
                      TeX = ("\\HOLTokenSupFour{}", 1)};

Definition extreal_min_def :
    extreal_min (x :extreal) y = if x <= y then x else y
End

Definition extreal_max_def :
    extreal_max (x :extreal) y = if x <= y then y else x
End

Overload min = “extreal_min”
Overload max = “extreal_max”

(* ------------------------------------------------------------------------- *)
(*   Addition                                                                *)
(* ------------------------------------------------------------------------- *)

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

Theorem add_comm_normal :
    !x y. Normal x + y = y + Normal x
Proof
    rpt STRIP_TAC
 >> Cases_on `y`
 >> RW_TAC std_ss [extreal_add_def, REAL_ADD_COMM]
QED

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

(* added one antecedent in the first part due to new definition of ``extreal_add`` *)
Theorem add_infty :
    (!x. x <> NegInf ==> ((x + PosInf = PosInf) /\ (PosInf + x = PosInf))) /\
    (!x. x <> PosInf ==> ((x + NegInf = NegInf) /\ (NegInf + x = NegInf)))
Proof
    RW_TAC std_ss [] >> Cases_on `x`
 >> RW_TAC std_ss [extreal_add_def, extreal_not_infty]
QED

Theorem add_not_infty :
    !x y. (x <> NegInf /\ y <> NegInf ==> x + y <> NegInf) /\
          (x <> PosInf /\ y <> PosInf ==> x + y <> PosInf)
Proof
    NTAC 2 Cases >> RW_TAC std_ss [extreal_add_def]
QED

Theorem EXTREAL_EQ_LADD :
    !x y z. x <> NegInf /\ x <> PosInf ==> ((x + y = x + z) <=> (y = z))
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_add_def, REAL_EQ_LADD]
QED

Theorem EXTREAL_EQ_RADD :
    !x y z. z <> NegInf /\ z <> PosInf ==> ((x + z = y + z) <=> (x = y))
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_add_def, REAL_EQ_RADD]
QED

Theorem extreal_double : (* cf. realTheory.REAL_DOUBLE *)
    !(x :extreal). x + x = 2 * x
Proof
    Cases
 >> rw [extreal_of_num_def, extreal_add_def, extreal_mul_def, REAL_DOUBLE]
QED

(* ------------------------------------------------------------------------- *)
(*    Ordering                                                               *)
(* ------------------------------------------------------------------------- *)

Theorem extreal_not_lt :
    !x y:extreal. ~(x < y) <=> y <= x
Proof
    REWRITE_TAC [TAUT `(~a <=> b) <=> (a <=> ~b)`] THEN
    SIMP_TAC std_ss [extreal_lt_def]
QED

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

Theorem le_infty :
   (!x. NegInf <= x /\ x <= PosInf) /\
   (!x. x <= NegInf <=> (x = NegInf)) /\
   (!x. PosInf <= x <=> (x = PosInf))
Proof
    RW_TAC std_ss []
 >> Cases_on `x`
 >> RW_TAC std_ss [extreal_le_def]
QED

(* NOTE: The statements of this theorem were slightly refined when moving
         here from extrealTheory. Old statements:

   |- !x y. NegInf < Normal y /\ Normal y < PosInf /\
            NegInf < PosInf /\ ~(x < NegInf) /\ ~(PosInf < x) /\
           (x <> PosInf <=> x < PosInf) /\ (x <> NegInf <=> NegInf < x)
 *)
Theorem lt_infty :
    NegInf < PosInf /\
   (!x. NegInf < Normal x /\ Normal x < PosInf) /\
   (!x. ~(x < NegInf) /\ ~(PosInf < x)) /\
   (!x. x <> PosInf <=> x < PosInf) /\
   (!x. x <> NegInf <=> NegInf < x)
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, lt_refl]
 >> Cases_on ‘x’
 >> fs [extreal_lt_def, extreal_le_def, lt_refl]
QED

Theorem lt_imp_le :
    !x y :extreal. x < y ==> x <= y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LT_IMP_LE]
QED

Theorem lt_imp_ne :
    !x y :extreal. x < y ==> x <> y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LT_IMP_NE]
QED

Theorem le_trans :
    !x y z :extreal. x <= y /\ y <= z ==> x <= z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_le_def,le_refl]
 >> METIS_TAC [REAL_LE_TRANS]
QED

Theorem lt_trans :
    !x y z :extreal. x < y /\ y < z ==> x < z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_lt_def, lt_refl, extreal_le_def, le_refl, GSYM real_lt]
 >> METIS_TAC [REAL_LT_TRANS]
QED

Theorem let_trans :
    !x y z:extreal. x <= y /\ y < z ==> x < z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt,REAL_LET_TRANS]
QED

Theorem le_antisym :
    !x y :extreal. (x <= y /\ y <= x) <=> (x = y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, le_refl, REAL_LE_ANTISYM]
QED

Theorem lt_antisym :
    !x y. ~(x < y /\ y < x)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [lt_infty, extreal_lt_eq]
 >> METIS_TAC [REAL_LT_ANTISYM, DE_MORGAN_THM]
QED

Theorem lte_trans :
    !x y z:extreal. x < y /\ y <= z ==> x < z
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_refl, le_refl, extreal_lt_def, extreal_le_def]
 >> METIS_TAC [real_lt, REAL_LTE_TRANS]
QED

Theorem let_antisym :
    !x y. ~(x < y /\ y <= x)
Proof
    rpt GEN_TAC
 >> CCONTR_TAC >> fs []
 >> `x < x` by PROVE_TAC [lte_trans]
 >> PROVE_TAC [lt_refl]
QED

(* NOTE: The statements of this theorem were slightly refined when moving
         here from extrealTheory. Old statements:

   |- !x. (0 <= x ==> x <> NegInf) /\ (x <= 0 ==> x <> PosInf)
*)
Theorem le_not_infty :
   (!x. 0 <= x ==> x <> NegInf) /\
   (!x. x <= 0 ==> x <> PosInf)
Proof
    NTAC 3 STRIP_TAC
 >> ONCE_REWRITE_TAC [lt_infty]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC (Q.SPECL [`NegInf`, `0`, `x`] lte_trans) \\
      PROVE_TAC [lt_infty, num_not_infty],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC (Q.SPECL [`x`, `0`, `PosInf`] let_trans) \\
      PROVE_TAC [lt_infty, num_not_infty] ]
QED

(* |- !x. 0 <= x ==> x <> NegInf, very useful in measureTheory *)
Theorem pos_not_neginf = CONJUNCT1 le_not_infty

(* |- !x. x <= 0 ==> x <> PosInf *)
Theorem neg_not_posinf = CONJUNCT2 le_not_infty

Theorem le_total :
    !x y. x <= y \/ y <= x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, REAL_LE_TOTAL]
QED

Theorem lt_total :
    !x y. (x = y) \/ x < y \/ y < x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, GSYM real_lt, REAL_LT_TOTAL]
QED

Theorem le_01[simp] : 0 <= 1
Proof
    RW_TAC std_ss [extreal_of_num_def, extreal_le_eq, REAL_LE_01]
QED

Theorem lt_01[simp] : 0 < 1
Proof
    RW_TAC std_ss [extreal_of_num_def, extreal_lt_eq, REAL_LT_01]
QED

Theorem ne_01[simp] : 0 <> 1
Proof
    RW_TAC std_ss [extreal_of_num_def, REAL_10]
QED

Theorem le_02[simp] : 0 <= 2
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_le_eq]
QED

Theorem lt_02[simp] : 0 < 2
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]
QED

Theorem lt_10[simp] : -1 < 0
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq, extreal_ainv_def]
QED

Theorem ne_02[simp] : 0 <> 2
Proof
    RW_TAC real_ss [extreal_of_num_def]
QED

(* NOTE: added [simp] when moving here from extrealTheory *)
Theorem le_num[simp] :
    !n:num. 0 <= &n
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_le_def]
QED

Theorem num_lt_infty[simp] :
    !n:num. &n < PosInf
Proof
    RW_TAC std_ss [extreal_of_num_def, lt_infty]
QED

Theorem lt_le :
    !x y. x < y <=> (x <= y /\ x <> y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LT_LE]
QED

Theorem le_lt :
    !x y. (x <= y) <=> x < y \/ (x = y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, lt_infty, le_infty, REAL_LE_LT]
QED

Theorem le_neg :
    !x y. -x <= -y <=> y <= x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def, lt_infty, le_infty,
                   REAL_LE_NEG]
QED

Theorem lt_neg :
    !x y. -x < -y <=> y < x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_le_def, extreal_ainv_def,  lt_infty,le_infty,
                   REAL_LT_NEG]
QED

Theorem le_add :
    !x y :extreal. 0 <= x /\ 0 <= y ==> 0 <= x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_of_num_def, REAL_LE_ADD]
QED

Theorem lt_add :
    !x y :extreal. 0 < x /\ 0 < y ==> 0 < x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LT_ADD]
QED

Theorem let_add :
    !x y:extreal. 0 <= x /\ 0 < y ==> 0 < x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LET_ADD]
QED

Theorem lte_add :
    !x y:extreal. 0 < x /\ 0 <= y ==> 0 < x + y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LTE_ADD]
QED

Theorem le_add2 :
    !w x y z. w <= x /\ y <= z ==> w + y <= x + z
Proof
    NTAC 4 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, le_infty, le_refl]
 >> METIS_TAC [REAL_LE_ADD2]
QED

Theorem lt_add2 :
    !w x y z. w < x /\ y < z ==> w + y < x + z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_lt_eq, lt_infty, REAL_LT_ADD2]
QED

Theorem let_add2 :
    !w x y z. w <> NegInf /\ w <> PosInf /\ w <= x /\ y < z ==> w + y < x + z
Proof
    NTAC 4 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty, le_refl]
 >> METIS_TAC [real_lt, REAL_LET_ADD2]
QED

Theorem let_add2_alt :
    !w x y z. x <> NegInf /\ x <> PosInf /\ w <= x /\ y < z ==> w + y < x + z
Proof
    NTAC 4 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_lt_def, extreal_add_def, le_infty, le_refl]
 >> METIS_TAC [real_lt, REAL_LET_ADD2]
QED

(* This theorem is newly added in extreal_baseTheory *)
Theorem le_addl :
    !x y. y <> NegInf /\ y <> PosInf ==> (y <= x + y <=> (0 <= x))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDL]
QED

Theorem le_addr :
    !x y. x <> NegInf /\ x <> PosInf ==> (x <= x + y <=> (0 <= y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDR]
QED

Theorem le_addl_imp :
    !x y. 0 <= x ==> y <= x + y
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDL]
QED

Theorem le_addr_imp :
    !x y. 0 <= y ==> x <= x + y
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, le_infty, extreal_of_num_def,
                   extreal_not_infty, REAL_LE_ADDR]
QED

Theorem le_ladd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (x + y <= x + z <=> y <= z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD]
QED

Theorem le_radd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y + x <= z + x <=> y <= z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD]
QED

Theorem le_radd_imp :
    !x y z. y <= z ==> y + x <= z + x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_RADD, le_infty, le_refl]
QED

Theorem le_ladd_imp :
    !x y z. y <= z ==> x + y <= x + z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, REAL_LE_LADD, le_infty, le_refl]
QED

Theorem lt_ladd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (x + y < x + z <=> y < z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_LADD]
QED

Theorem lt_radd :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y + x < z + x <=> y < z)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_le_def, extreal_lt_def, REAL_LE_RADD]
QED

Theorem lt_addl :
    !x y. y <> NegInf /\ y <> PosInf ==> (y < x + y <=> 0 < x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_lt_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty]
 >> REAL_ARITH_TAC
QED

(* This theorem is newly added in extreal_baseTheory *)
Theorem lt_addr :
    !x y. x <> NegInf /\ x <> PosInf ==> (x < x + y <=> 0 < y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_lt_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty]
 >> REAL_ARITH_TAC
QED

(* NOTE: two antecedents were added due to new definitions of ‘extreal_add’ *)
Theorem le_lneg :
    !x y. ((x <> NegInf /\ y <> NegInf) \/
           (x <> PosInf /\ y <> PosInf)) ==> (-x <= y <=> 0 <= x + y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_le_def, extreal_add_def, extreal_sub_def,
                   le_infty, extreal_of_num_def, extreal_not_infty, REAL_LE_LNEG]
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

(* |- !x y. x <= 0 /\ y <= 0 ==> x + y <= 0 *)
Theorem le_add_neg =
   (Q.GENL [`x`, `y`] (REWRITE_RULE [add_rzero] (Q.SPECL [`x`, `0`, `y`, `0`] le_add2)))

(* |- !x y. x < 0 /\ y < 0 ==> x + y < 0 *)
Theorem lt_add_neg =
   (Q.GENL [`x`, `y`] (REWRITE_RULE [add_rzero] (Q.SPECL [`x`, `0`, `y`, `0`] lt_add2)))

(* |- !x y. x <> NegInf /\ x <> PosInf /\ 0 < y ==> x < x + y *)
Theorem lt_addr_imp =
   (Q.GENL [`x`, `y`]
      (REWRITE_RULE [le_refl, add_rzero] (Q.SPECL [`x`, `x`, `0`, `y`] let_add2)))

(* ------------------------------------------------------------------------- *)
(*   Substraction (often with order)                                         *)
(* ------------------------------------------------------------------------- *)

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

Theorem sub_le_imp :
    !x y z. x <> NegInf /\ x <> PosInf /\ y <= z + x ==> y - x <= z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_RADD]
QED

Theorem sub_le_imp2 :
    !x y z. y <> NegInf /\ y <> PosInf /\ y <= z + x ==> y - x <= z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_RADD]
QED

Theorem le_sub_imp :
    !x y z. x <> NegInf /\ x <> PosInf /\ y + x <= z ==> y <= z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_LADD]
QED

Theorem le_sub_imp2 : (* new *)
    !x y z. z <> NegInf /\ z <> PosInf /\ y + x <= z ==> y <= z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                   REAL_LE_SUB_LADD]
QED

Theorem lt_sub_imp :
    !x y z. x <> NegInf /\ y <> NegInf /\ y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_ADD_SUB]
QED

Theorem lt_sub_imp' :
    !x y z. x <> PosInf /\ y <> PosInf /\ y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_ADD_SUB]
QED

Theorem lt_sub_imp2 : (* new *)
    !x y z. x <> NegInf /\ x <> PosInf /\ y + x < z ==> y < z - x
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_ADD_SUB]
QED

Theorem sub_lt_imp :
    !x y z. x <> NegInf /\ x <> PosInf /\ y < z + x ==> y - x < z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_SUB_RADD]
QED

Theorem sub_lt_eq :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y - x < z <=> y < z + x)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- PROVE_TAC [sub_lt_imp]
 >> Cases_on `x` >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_SUB_RADD]
QED

Theorem sub_lt_imp2 :
    !x y z. z <> NegInf /\ z <> PosInf /\ y < z + x ==> y - x < z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def, extreal_sub_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_SUB_RADD]
QED

Theorem sub_zero_lt :
    !x y. x < y ==> 0 < y - x
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LT]
QED

Theorem sub_zero_lt2 :
    !x y. x <> NegInf /\ x <> PosInf /\ 0 < y - x ==> x < y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def,extreal_add_def,extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LT]
QED

Theorem sub_lt_zero :
    !x y. x < y ==> x - y < 0
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_SUB_RADD]
QED

Theorem sub_lt_zero2 :
    !x y. y <> NegInf /\ y <> PosInf /\ x - y < 0 ==> x < y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, extreal_lt_eq,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_SUB_RADD]
QED

(* more antecedents added *)
Theorem sub_zero_le :
    !x y. x <> NegInf /\ x <> PosInf ==> (x <= y <=> 0 <= y - x)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_SUB_LE]
QED

Theorem sub_le_zero :
    !x y. y <> NegInf /\ y <> PosInf ==> (x <= y <=> x - y <= 0)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def,
                    lt_infty, extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_RADD]
QED

Theorem le_sub_eq :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y <= z - x <=> y + x <= z)
Proof
    METIS_TAC [le_sub_imp, sub_lt_imp, extreal_lt_def]
QED

Theorem le_sub_eq2 :
    !x y z. z <> NegInf /\ z <> PosInf /\ x <> NegInf /\ y <> NegInf ==>
           (y <= z - x <=> y + x <= z)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, lt_infty,
                    extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_LADD]
QED

Theorem sub_le_eq :
    !x y z. x <> NegInf /\ x <> PosInf ==> (y - x <= z <=> y <= z + x)
Proof
    METIS_TAC [sub_le_imp, lt_sub_imp2, extreal_lt_def]
QED

Theorem sub_le_eq2 :
    !x y z. y <> NegInf /\ y <> PosInf /\ x <> NegInf /\ z <> NegInf ==>
           (y - x <= z <=> y <= z + x)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_def, extreal_add_def, extreal_sub_def, lt_infty,
                    extreal_of_num_def, extreal_not_infty, REAL_LE_SUB_RADD]
QED

Theorem sub_le_switch :
    !x y z. x <> NegInf /\ x <> PosInf /\ z <> NegInf /\ z <> PosInf ==>
           (y - x <= z <=> y - z <= x)
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_le_def, le_infty, lt_infty]
 >> REAL_ARITH_TAC
QED

Theorem sub_le_switch2 :
    !x y z. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
           (y - x <= z <=> y - z <= x)
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_le_def, le_infty, lt_infty]
 >> REAL_ARITH_TAC
QED

(* more antecedents ‘x <> NegInf /\ y <> NegInf’ added *)
Theorem lt_sub :
    !x y z. x <> NegInf /\ y <> NegInf /\ z <> NegInf /\ z <> PosInf ==>
           (y + x < z <=> y < z - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, le_infty]
 >> METIS_TAC [REAL_LE_SUB_RADD]
QED

Theorem lt_sub' :
    !x y z. x <> PosInf /\ y <> PosInf /\ z <> NegInf /\ z <> PosInf ==>
           (y + x < z <=> y < z - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, le_infty]
 >> METIS_TAC [REAL_LE_SUB_RADD]
QED

Theorem sub_add2 :
    !x y. x <> NegInf /\ x <> PosInf ==> (x + (y - x) = y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_add_def, extreal_sub_def, REAL_SUB_ADD2]
QED

Theorem add_sub :
    !x y. y <> NegInf /\ y <> PosInf ==> (x + y - y = x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, REAL_ADD_SUB_ALT]
QED

Theorem add_sub_normal[simp] :
    !x r. x + Normal r - Normal r = x
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC add_sub
 >> REWRITE_TAC [extreal_not_infty]
QED

Theorem add_sub2 :
    !x y. y <> NegInf /\ y <> PosInf ==> (y + x - y = x)
Proof
   rpt Cases
>> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                  extreal_sub_def, REAL_ADD_SUB]
QED

Theorem sub_add :
    !x y. y <> NegInf /\ y <> PosInf ==> (x - y + y = x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_lt_def, extreal_le_def, extreal_add_def,
                   extreal_sub_def, REAL_SUB_ADD]
QED

Theorem sub_add_normal[simp] :
    !x r. x - Normal r + Normal r = x
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC sub_add
 >> REWRITE_TAC [extreal_not_infty]
QED

(* NOTE: this theorem is for compatibility purposes only, cf. extreal_sub *)
Theorem extreal_sub_add :
    !x y. (x <> NegInf /\ y <> PosInf) \/ (x <> PosInf /\ y <> NegInf) ==>
          (x - y = x + -y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_ainv_def, extreal_sub_def, extreal_add_def, real_sub]
QED

Theorem sub_0 :
    !x y :extreal. (x - y = 0) ==> (x = y)
Proof
    rpt Cases >> simp[extreal_sub_def]
QED

Theorem sub_eq_0 :
    !x y. x <> PosInf /\ x <> NegInf /\ (x = y) ==> (x - y = 0)
Proof
  RW_TAC std_ss []
  >> `?a. x = Normal a` by METIS_TAC [extreal_cases]
  >> simp[extreal_of_num_def, extreal_sub_def, REAL_SUB_REFL]
QED

Theorem sub_not_infty :
    !x y. (x <> NegInf /\ y <> PosInf ==> x - y <> NegInf) /\
          (x <> PosInf /\ y <> NegInf ==> x - y <> PosInf)
Proof
    rpt Cases >> RW_TAC std_ss [extreal_sub_def]
QED

(* ------------------------------------------------------------------------- *)
(*   Negation                                                                *)
(* ------------------------------------------------------------------------- *)

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

(* NOTE: using this theorem directly in any rewriting tactics will cause a self loop,
         while (GSYM neg_minus1) is more useful in turning ‘-1 * x’ to -x.
 *)
Theorem neg_minus1 :
    !x. -x = -1 * x
Proof
    Cases
 >> RW_TAC real_ss [extreal_ainv_def, extreal_of_num_def, extreal_mul_def]
QED

(* NOTE: the original unconditional statement is recovered *)
Theorem sub_rneg :
    !x y :extreal. x - -y = x + y
Proof
    rw [extreal_sub, neg_neg]
QED

Theorem sub_lneg :
    !x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (-x - y = -(x + y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, REAL_SUB_LNEG]
QED

Theorem neg_add :
    !x y. (x <> NegInf /\ y <> NegInf) \/ (x <> PosInf /\ y <> PosInf) ==>
          (-(x + y) = -x + -y)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, REAL_NEG_ADD]
QED

Theorem neg_sub :
    !x y. (x <> NegInf /\ x <> PosInf) \/ (y <> NegInf /\ y <> PosInf) ==>
          (-(x - y) = y - x)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_sub_def, extreal_ainv_def, REAL_NEG_SUB]
QED

Theorem le_lsub_imp :
    !x y z. y <= z ==> x - z <= x - y
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl]
 >> METIS_TAC [real_sub, REAL_LE_ADD2, REAL_LE_NEG, REAL_LE_REFL]
QED

Theorem lt_lsub_imp :
    !x y z. x <> PosInf /\ x <> NegInf /\ y < z ==> x - z < x - y
Proof
    rpt STRIP_TAC
 >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fs o wrap)
 >> Cases_on ‘y’ >> Cases_on ‘z’
 >> rw [extreal_sub_def, lt_infty]
 >> fs [lt_infty, lt_refl, extreal_lt_eq]
 >> RealArith.REAL_ASM_ARITH_TAC
QED

Theorem le_rsub_imp :
    !x y z. x <= y ==> x - z <= y - z
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl]
 >> METIS_TAC [real_sub, REAL_LE_ADD2, REAL_LE_NEG, REAL_LE_REFL]
QED

Theorem lt_rsub_imp :
    !x y z. z <> PosInf /\ z <> NegInf /\ x < y ==> x - z < y - z
Proof
    rpt STRIP_TAC
 >> ‘?r. z = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fs o wrap)
 >> Cases_on ‘x’ >> Cases_on ‘y’
 >> rw [extreal_sub_def, lt_infty]
 >> fs [lt_infty, lt_refl, extreal_lt_eq]
 >> RealArith.REAL_ASM_ARITH_TAC
QED

Theorem eq_sub_ladd_normal :
    !x y z. (x = y - Normal z) <=> (x + Normal z = y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl,
                   extreal_add_def, REAL_EQ_SUB_LADD]
QED

Theorem eq_sub_radd :
    !x y z. y <> NegInf /\ y <> PosInf ==> ((x - y = z) <=> (x = z + y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_sub_def, REAL_EQ_SUB_RADD]
QED

Theorem eq_sub_ladd :
    !x y z. z <> NegInf /\ z <> PosInf ==> ((x = y - z) <=> (x + z = y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def, extreal_sub_def, REAL_EQ_SUB_LADD]
QED

Theorem eq_sub_switch :
    !x y z. (x = Normal z - y) <=> (y = Normal z - x)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_sub_def, le_infty, le_refl, extreal_add_def]
 >> REAL_ARITH_TAC
QED

Theorem eq_add_sub_switch :
    !a b c d. b <> NegInf /\ b <> PosInf /\ c <> NegInf /\ c <> PosInf ==>
             ((a + b = c + d) <=> (a - c = d - b))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_add_def,extreal_sub_def]
 >> REAL_ARITH_TAC
QED

Theorem sub_refl :
    !x. x <> NegInf /\ x <> PosInf ==> x - x = 0
Proof
    Cases >> RW_TAC real_ss [extreal_sub_def, extreal_of_num_def]
QED

Theorem sub_infty :
   (!x. x <> NegInf ==> (x - NegInf = PosInf)) /\
   (!x. x <> PosInf ==> (x - PosInf = NegInf)) /\
   (!x. x <> PosInf ==> (PosInf - x = PosInf)) /\
   (!x. x <> NegInf ==> (NegInf - x = NegInf))
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> FULL_SIMP_TAC std_ss [extreal_sub_def]
QED

(* ------------------------------------------------------------------------- *)
(*     Multiplication                                                        *)
(* ------------------------------------------------------------------------- *)

Theorem extreal_mul_eq :
    !x y. extreal_mul (Normal x) (Normal y) = Normal (x * y)
Proof
    rw [extreal_mul_def]
QED

Theorem mul_comm :
    !x y:extreal. x * y = y * x
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_mul_def, REAL_MUL_COMM]
QED

Theorem mul_assoc :
    !x y z:extreal. x * (y * z) = x * y * z
Proof
    NTAC 3 Cases
 >> RW_TAC real_ss [extreal_mul_def, REAL_MUL_ASSOC, REAL_MUL_LZERO,
                    REAL_MUL_RZERO, REAL_ENTIRE, REAL_LT_LMUL_0, REAL_POS_NZ,
                    DE_MORGAN_THM]
 >> FULL_SIMP_TAC real_ss [DE_MORGAN_THM, REAL_NOT_LT, REAL_LT_LMUL_0, GSYM REAL_LT_LE]
 >> METIS_TAC [REAL_LT_LMUL_0_NEG, REAL_LT_RMUL_0_NEG, REAL_LT_RMUL_NEG_0,
               REAL_LT_LE, REAL_LT_GT, REAL_ENTIRE, REAL_LT_LMUL_NEG_0,
               REAL_LT_LMUL_NEG_0_NEG, REAL_LT_RMUL_0, REAL_LT_LMUL_0,
               REAL_LT_RMUL_NEG_0_NEG]
QED

Theorem mul_rzero[simp] :
    !x :extreal. x * 0 = 0
Proof
    Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, REAL_MUL_RZERO]
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
  rpt Cases >> rw[extreal_mul_def]
QED

Theorem le_mul :
    !x y :extreal. 0 <= x /\ 0 <= y ==> 0 <= x * y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                   REAL_LE_MUL, GSYM real_lt]
 >> METIS_TAC [REAL_LT_LE, real_lte]
QED

Theorem let_mul :
    !x y :extreal. 0 <= x /\ 0 < y ==> 0 <= x * y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq, lt_infty,
                    le_infty, le_refl, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]
QED

Theorem lte_mul :
    !x y :extreal. 0 < x /\ 0 <= y ==> 0 <= x * y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_le_def, extreal_lt_eq,
                    lt_infty, le_infty, le_refl, extreal_of_num_def]
 >> METIS_TAC [real_lt, REAL_LT_LE, REAL_LT_IMP_LE, REAL_LE_MUL]
QED

Theorem le_mul_neg :
    !x y :extreal. x <= 0 /\ y <= 0 ==> 0 <= x * y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                   REAL_LE_MUL, GSYM real_lt]
 >> METIS_TAC [REAL_LE_NEG, REAL_NEG_0, REAL_NEG_MUL2, REAL_MUL_RZERO,
               REAL_LE_MUL]
QED

Theorem mul_le :
    !x y :extreal. 0 <= x /\ y <= 0 ==> x * y <= 0
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_le_def, extreal_mul_def, extreal_of_num_def,
                   REAL_LE_MUL, GSYM real_lt]
 >- METIS_TAC [REAL_LT_LE, real_lt]
 >> `0 <= -r'` by METIS_TAC [REAL_LE_NEG, REAL_NEG_0]
 >> METIS_TAC [REAL_LE_NEG, REAL_NEG_0, REAL_LE_MUL, REAL_MUL_RNEG]
QED

Theorem lt_mul :
    !x y:extreal. 0 < x /\ 0 < y ==> 0 < x * y
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                   REAL_LT_MUL, lt_infty]
QED

Theorem lt_mul_neg :
    !x y :extreal. x < 0 /\ y < 0 ==> 0 < x * y
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq, lt_infty, extreal_mul_def]
 >> METIS_TAC [REAL_LT_LE, real_lt, REAL_LT_NEG, REAL_NEG_0, REAL_NEG_MUL2,
               REAL_LT_MUL]
QED

Theorem mul_lt :
    !x y:extreal. 0 < x /\ y < 0 ==> x * y < 0
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                   REAL_LT_MUL, lt_infty]
 >- METIS_TAC [REAL_LT_LE, real_lt]
 >> `0 < -r'` by METIS_TAC [REAL_LT_NEG, REAL_NEG_0]
 >> METIS_TAC [REAL_MUL_RNEG, REAL_LT_MUL, REAL_LT_NEG, REAL_NEG_0]
QED

Theorem mul_let :
    !x y :extreal. 0 <= x /\ y < 0 ==> x * y <= 0
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                    lt_infty, extreal_le_def, le_refl, le_infty]
 >> METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL, real_lt,
               REAL_MUL_RNEG, REAL_NEG_NEG, REAL_LE_NEG, REAL_LT_LE]
QED

Theorem mul_lte :
    !x y :extreal. 0 < x /\ y <= 0 ==> x * y <= 0
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, extreal_of_num_def,
                    lt_infty, extreal_le_def, le_refl, le_infty]
 >> METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE, REAL_NEG_0, REAL_LE_MUL,
               REAL_MUL_RNEG, REAL_NEG_NEG, REAL_LE_NEG, real_lt, REAL_LT_LE]
QED

Theorem lt_rmul :
    !x y z. 0 < z /\ z <> PosInf ==> (x * z < y * z <=> x < y)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_lt_eq, extreal_mul_def, le_infty, lt_infty,
                    REAL_LT_REFL, REAL_LT_RMUL, extreal_of_num_def]
QED

Theorem lt_rmul_imp :
    !x y z. x < y /\ 0 < z /\ z <> PosInf ==> x * z < y * z
Proof
    METIS_TAC [lt_rmul]
QED

Theorem le_rmul :
    !x y z. 0 < z /\ z <> PosInf ==> (x * z <= y * z <=> x <= y)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_le_eq, extreal_mul_def, le_infty, extreal_of_num_def,
                    REAL_LE_REFL, REAL_LE_RMUL, lt_infty, extreal_lt_eq]
QED

Theorem le_rmul_imp :
    !x y z :extreal. 0 <= z /\ x <= y ==> x * z <= y * z
Proof
    RW_TAC std_ss []
 >> Cases_on `z = 0` >- RW_TAC std_ss [mul_rzero, le_refl]
 >> `0 < z` by METIS_TAC [lt_le]
 >> reverse (Cases_on ‘z = PosInf’) >- METIS_TAC [le_rmul]
 >> fs [le_infty, lt_infty, extreal_of_num_def]
 >> Cases_on `x` >> Cases_on `y`
 >> RW_TAC real_ss [extreal_le_def, extreal_lt_eq, extreal_mul_def,
                    REAL_LE_REFL, REAL_LT_REFL, GSYM real_lte, GSYM real_lt,
                    le_infty, lt_infty, extreal_of_num_def, REAL_LT_IMP_LE]
 >> FULL_SIMP_TAC std_ss [le_infty, extreal_not_infty]
 >> METIS_TAC [REAL_LT_LE, REAL_LTE_TRANS, extreal_le_eq, REAL_LET_ANTISYM]
QED

Theorem lt_mul2 :
    !x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\ x1 <> PosInf /\ y1 <> PosInf /\
                  x1 < x2 /\ y1 < y2 ==> x1 * y1 < x2 * y2
Proof
    RW_TAC std_ss []
 >> `0 < x2 /\ 0 < y2` by METIS_TAC [let_trans]
 >> Cases_on `x1` >> Cases_on `y1`
 >> Cases_on `x2` >> Cases_on `y2`
 >> FULL_SIMP_TAC real_ss [extreal_lt_eq, extreal_le_def, extreal_mul_def,
                           le_infty, lt_infty, real_lte, REAL_LT_MUL2,
                           extreal_of_num_def, extreal_not_infty]
 >> METIS_TAC [extreal_not_infty,lt_infty]
QED

Theorem mul_lposinf :
    !x. 0 < x ==> (PosInf * x = PosInf)
Proof
   Cases >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, lt_infty,
                            num_not_infty, extreal_lt_eq]
QED

Theorem mul_rposinf :
    !x. 0 < x ==> (x * PosInf = PosInf)
Proof
   Cases >> RW_TAC real_ss [extreal_mul_def, extreal_of_num_def, lt_infty,
                            num_not_infty, extreal_lt_eq]
QED

Theorem mul_infty :
    !x. 0 < x ==> (PosInf * x = PosInf) /\ (x * PosInf = PosInf) /\
                  (NegInf * x = NegInf) /\ (x * NegInf = NegInf)
Proof
    GEN_TAC >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> DISCH_TAC
 >> CONJ_TAC >- art [Once mul_comm]
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> REWRITE_TAC [Once mul_comm]
QED

Theorem mul_infty' :
    !x. x < 0 ==> (PosInf * x = NegInf) /\ (x * PosInf = NegInf) /\
                  (NegInf * x = PosInf) /\ (x * NegInf = PosInf)
Proof
    GEN_TAC >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> DISCH_TAC
 >> CONJ_TAC >- art [Once mul_comm]
 >> STRONG_CONJ_TAC
 >- (Cases_on ‘x’ >> rw [extreal_mul_def] \\
     fs [lt_infty, extreal_of_num_def, extreal_lt_eq] \\
     PROVE_TAC [REAL_LT_ANTISYM])
 >> REWRITE_TAC [Once mul_comm]
QED

Theorem mul_not_infty :
   (!c y. 0 <= c /\ y <> NegInf ==> Normal (c) * y <> NegInf) /\
   (!c y. 0 <= c /\ y <> PosInf ==> Normal (c) * y <> PosInf) /\
   (!c y. c <= 0 /\ y <> NegInf ==> Normal (c) * y <> PosInf) /\
   (!c y. c <= 0 /\ y <> PosInf ==> Normal (c) * y <> NegInf)
Proof
    RW_TAC std_ss [] >> Cases_on `y`
 >> RW_TAC std_ss [extreal_mul_def, extreal_le_def]
 >> METIS_TAC [real_lte, REAL_LE_ANTISYM]
QED

Theorem mul_not_infty2 :
    !x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
         (x * y <> NegInf) /\ (x * y <> PosInf)
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, extreal_not_infty]
QED

Theorem mul_lt2 :
    !x y :extreal. x < 0 /\ 0 < y ==> x * y < 0
Proof
    METIS_TAC [mul_comm, mul_lt]
QED

Theorem mul_le2 :
    !x y :extreal. x <= 0 /\ 0 <= y ==> x * y <= 0
Proof
    METIS_TAC [mul_comm, mul_le]
QED

Theorem add_ldistrib_pos :
    !x y z. 0 <= y /\ 0 <= z ==> (x * (y + z) = x * y + x * z)
Proof
    NTAC 3 Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_mul_def, extreal_le_def,
                    extreal_of_num_def, real_lt, REAL_LT_ANTISYM,
                    REAL_LE_ANTISYM, REAL_ADD_LID, REAL_ADD_RID, REAL_LT_LE]
 >> FULL_SIMP_TAC real_ss [GSYM real_lt, GSYM real_lte]
 >> METIS_TAC [REAL_LE_ANTISYM, REAL_LT_ADD, REAL_LT_IMP_LE, REAL_LT_IMP_NE,
               REAL_LT_LE, REAL_ADD_LDISTRIB]
QED

Theorem add_ldistrib_neg :
    !x y z. y <= 0 /\ z <= 0 ==> (x * (y + z) = x * y + x * z)
Proof
    NTAC 3 Cases (* 27 sub-goals here *)
 >> RW_TAC real_ss [extreal_add_def, extreal_mul_def, extreal_le_def,
                    extreal_of_num_def, real_lt, REAL_LT_ANTISYM,
                    REAL_LE_ANTISYM, REAL_ADD_LID, REAL_ADD_RID, REAL_LT_LE] (* 17 goals *)
 >> FULL_SIMP_TAC real_ss [GSYM real_lt, GSYM real_lte, REAL_ADD_LDISTRIB]   (*  4 goals *)
 >> (Cases_on `0 < r` >- RW_TAC std_ss [] \\
     Cases_on `0 < r'` >- RW_TAC std_ss [] \\
     `r < 0 /\ r' < 0` by METIS_TAC [real_lte, REAL_LT_LE] \\
     METIS_TAC [REAL_LT_ADD2, REAL_ADD_LID, REAL_LT_IMP_NE, REAL_LT_ANTISYM])
QED

(* changed var name from `x` to `r` *)
Theorem add_ldistrib_normal :
    !r y z. (y <> PosInf /\ z <> PosInf) \/ (y <> NegInf /\ z <> NegInf)
        ==> (Normal r * (y + z) = Normal r * y + Normal r * z)
Proof
    RW_TAC std_ss [] >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_add_def] (* 8 sub-goals here, same tacticals *)
 >> (Cases_on `r = 0`
     >- METIS_TAC [extreal_of_num_def, mul_lzero, add_lzero] \\
     RW_TAC std_ss [extreal_mul_def, extreal_add_def, REAL_ADD_LDISTRIB])
QED

Theorem add_ldistrib_normal2 = add_ldistrib_normal (* backward compatible *)

Theorem add_rdistrib_normal :
    !x y z. (y <> PosInf /\ z <> PosInf) \/ (y <> NegInf /\ z <> NegInf) ==>
            ((y + z) * Normal x = y * Normal x + z * Normal x)
Proof
    RW_TAC std_ss []
 >> Cases_on `y` >> Cases_on `z`
 >> RW_TAC std_ss [extreal_add_def]
 >> (Cases_on `x = 0`
     >- METIS_TAC [extreal_of_num_def, mul_rzero, add_rzero] \\
     RW_TAC std_ss [extreal_mul_def, extreal_add_def, REAL_ADD_RDISTRIB])
QED

Theorem add_rdistrib_normal2 = add_rdistrib_normal (* backward compatible *)

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

Theorem mul_lneg :
    !x y. -x * y = -(x * y)
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_ainv_def, extreal_mul_def, REAL_MUL_LNEG, REAL_NEG_EQ0]
 >> METIS_TAC [REAL_NEG_GT0, REAL_LT_REFL, REAL_LT_TRANS, real_lte, REAL_LE_ANTISYM]
QED

Theorem mul_rneg :
    !x y. x * -y = -(x * y)
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_ainv_def, extreal_mul_def, REAL_MUL_RNEG, REAL_NEG_EQ0]
 >> METIS_TAC [REAL_NEG_GT0, REAL_LT_REFL, REAL_LT_TRANS, real_lte, REAL_LE_ANTISYM]
QED

Theorem neg_mul2 :
    !x y. -x * -y = x * y
Proof
    rpt Cases >> RW_TAC real_ss [extreal_mul_def, extreal_ainv_def, REAL_NEG_EQ0]
 >> METIS_TAC [REAL_LT_NEG, REAL_NEG_0, REAL_LT_ANTISYM, real_lt, REAL_LE_ANTISYM]
QED

(* NOTE: the number of necessary antecedents are reduced *)
Theorem add2_sub2 :
    !a b c d. a <> NegInf /\ b <> PosInf /\ c <> NegInf /\ d <> PosInf
          ==> a - b + (c - d) = a + c - (b + d)
Proof
    rpt Cases >> rw [extreal_sub_def, extreal_add_def, REAL_ADD2_SUB2]
QED

Theorem sub_ldistrib :
    !x y z. x <> NegInf /\ x <> PosInf /\
            y <> NegInf /\ y <> PosInf /\
            z <> NegInf /\ z <> PosInf ==> (x * (y - z) = x * y - x * z)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_sub_def, extreal_mul_def,
                    REAL_SUB_LDISTRIB]
QED

Theorem sub_rdistrib :
    !x y z. x <> NegInf /\ x <> PosInf /\
            y <> NegInf /\ y <> PosInf /\
            z <> NegInf /\ z <> PosInf ==> ((x - y) * z = x * z - y * z)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_sub_def, extreal_mul_def,
                    REAL_SUB_RDISTRIB]
QED

Theorem mul_linv :
    !x. x <> 0 /\ x <> PosInf /\ x <> NegInf ==> (inv x * x = 1)
Proof
    Cases
 >> RW_TAC real_ss [extreal_div_def, extreal_mul_def, extreal_inv_def,
                    extreal_not_infty, extreal_of_num_def, REAL_MUL_LINV]
QED

Theorem mul_linv_pos :
    !x. 0 < x /\ x <> PosInf ==> (inv x * x = 1)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC mul_linv >> fs [lt_le]
 >> MATCH_MP_TAC pos_not_neginf >> art []
QED

Theorem le_lmul :
    !x y z. 0 < x /\ x <> PosInf ==> (x * y <= x * z <=> y <= z)
Proof
    METIS_TAC [mul_comm, le_rmul]
QED

Theorem le_lmul_imp :
    !x y z :extreal. 0 <= z /\ x <= y ==> z * x <= z * y
Proof
    METIS_TAC [mul_comm, le_rmul_imp]
QED

Theorem lt_lmul :
    !x y z. 0 < x /\ x <> PosInf ==> (x * y < x * z <=> y < z)
Proof
    METIS_TAC [mul_comm, lt_rmul]
QED

Theorem lt_lmul_imp :
    !x y z. 0 < x /\ x <> PosInf /\ y < z ==> x * y < x * z
Proof
    METIS_TAC [lt_lmul]
QED

(* cf. REAL_LE_MUL2 *)
Theorem le_mul2 :
    !x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\ x1 <= x2 /\ y1 <= y2 ==> x1 * y1 <= x2 * y2
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘x1 * y2’
 >> CONJ_TAC >- (MATCH_MP_TAC le_lmul_imp >> art [])
 >> MATCH_MP_TAC le_rmul_imp >> art []
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘y1’ >> art []
QED

(* ------------------------------------------------------------------------- *)
(*   Absolute value (abs)                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem abs_0[simp] :
    extreal_abs 0 = 0
Proof
    simp[extreal_abs_def, extreal_of_num_def]
QED

Theorem abs_pos[simp] :
    !x :extreal. 0 <= abs x
Proof
    Cases
 >> RW_TAC std_ss [extreal_abs_def, ABS_POS, extreal_le_def,
                   extreal_of_num_def, le_infty]
QED

Theorem abs_neg :
    !x :extreal. x < 0 ==> (abs x = -x)
Proof
    RW_TAC std_ss [extreal_lt_def]
 >> Cases_on `x`
 >- REWRITE_TAC [extreal_abs_def, extreal_ainv_def]
 >- fs [extreal_of_num_def, le_infty]
 >> fs [extreal_abs_def, extreal_of_num_def, extreal_le_eq, abs, extreal_ainv_def]
QED

(* an enhanced version of abs_neg *)
Theorem abs_neg' :
    !x :extreal. x <= 0 ==> (abs x = -x)
Proof
    RW_TAC std_ss [le_lt]
 >- (MATCH_MP_TAC abs_neg >> art [])
 >> REWRITE_TAC [abs_0, neg_0]
QED

Theorem abs_refl :
    !x :extreal. (abs x = x) <=> (0 <= x)
Proof
    Cases
 >> RW_TAC std_ss [extreal_abs_def, le_infty, extreal_of_num_def,
                   extreal_le_def, ABS_REFL]
QED

Theorem abs_abs[simp]:
    !x :extreal. abs(abs(x)) = abs(x)
Proof
    RW_TAC std_ss [abs_refl, abs_pos]
QED

Theorem abs_real :
    !x. x <> PosInf /\ x <> NegInf ==> abs (real x) = real (abs x)
Proof
    Cases >> rw [extreal_abs_def, real_normal]
QED

Theorem abs_bounds :
    !x k :extreal. abs x <= k <=> -k <= x /\ x <= k
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_abs_def, extreal_le_def, lt_infty,
                   le_infty, extreal_ainv_def, ABS_BOUNDS]
QED

Theorem abs_bounds_lt :
    !x k :extreal. abs x < k <=> -k < x /\ x < k
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_abs_def, extreal_lt_eq, lt_infty, le_infty,
                   extreal_ainv_def, ABS_BOUNDS_LT]
QED

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

Theorem abs_not_infty :
    !x. x <> PosInf /\ x <> NegInf ==> abs x <> PosInf /\ abs x <> NegInf
Proof
    Q.X_GEN_TAC ‘x’ >> STRIP_TAC
 >> `?c. x = Normal c` by PROVE_TAC [extreal_cases]
 >> ASM_REWRITE_TAC [extreal_abs_def, extreal_not_infty]
QED

(* NOTE: cf. le_abs_bounds for a better version without antecedents *)
Theorem abs_unbounds :
    !x k :extreal. 0 <= k ==> (k <= abs x <=> x <= -k \/ k <= x)
Proof
    rw [le_abs_bounds]
QED

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

Theorem abs_not_zero :
    !x. abs x <> 0 <=> x <> 0
Proof
    PROVE_TAC [abs_eq_0]
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

(* NOTE: although is possible that ‘x + y’ may be unspecific, this unspecific
         value is indeed <= PosInf
 *)
Theorem abs_triangle_full :
    !x y. abs(x + y) <= abs(x) + abs(y)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x <> PosInf /\ x <> NegInf’
 >- (Cases_on ‘y <> PosInf /\ y <> NegInf’
     >- (MATCH_MP_TAC abs_triangle >> art []) \\
    ‘abs y = PosInf’ by fs [extreal_abs_def] >> POP_ORW \\
     Suff ‘abs x + PosInf = PosInf’ >- rw [le_infty] \\
     Suff ‘abs x <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> rw [abs_pos])
 >> ‘abs x = PosInf’ by fs [extreal_abs_def] >> POP_ORW
 >> Suff ‘PosInf + abs y = PosInf’ >- rw [le_infty]
 >> Suff ‘abs y <> NegInf’ >- METIS_TAC [add_infty]
 >> MATCH_MP_TAC pos_not_neginf >> rw [abs_pos]
QED

Theorem abs_triangle_sub :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x) <= abs(y) + abs(x - y)
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> Cases_on `y`
 >> rw [extreal_abs_def, extreal_add_def, extreal_sub_def, extreal_le_eq,
        ABS_TRIANGLE_SUB]
QED

Theorem abs_triangle_sub_full :
    !x y. abs(x) <= abs(y) + abs(x - y)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x <> PosInf /\ x <> NegInf’
 >- (Cases_on ‘y <> PosInf /\ y <> NegInf’
     >- (MATCH_MP_TAC abs_triangle_sub >> art []) \\
    ‘abs y = PosInf’ by fs [extreal_abs_def] >> POP_ORW \\
     Suff ‘PosInf + abs (x - y) = PosInf’ >- rw [le_infty] \\
     Suff ‘abs (x - y) <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> rw [abs_pos])
 >> ‘abs x = PosInf’ by fs [extreal_abs_def] >> POP_ORW
 >> Cases_on ‘y’
 >> fs [extreal_abs_def, extreal_sub_def, extreal_add_def] (* 2 subgoals left *)
 >| [ (* goal 1 (of 2) *)
      Suff ‘PosInf + abs (NegInf - NegInf) = PosInf’ >- rw [le_infty] \\
      Suff ‘abs (NegInf - NegInf) <> NegInf’ >- METIS_TAC [add_infty] \\
      MATCH_MP_TAC pos_not_neginf >> rw [abs_pos],
      (* goal 2 (of 2) *)
      Suff ‘PosInf + abs (PosInf - PosInf) = PosInf’ >- rw [le_infty] \\
      Suff ‘abs (PosInf - PosInf) <> NegInf’ >- METIS_TAC [add_infty] \\
      MATCH_MP_TAC pos_not_neginf >> rw [abs_pos] ]
QED

Theorem abs_sub :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x - y) = abs(y - x)
Proof
    RW_TAC std_ss []
 >> Cases_on `x` >> Cases_on `y`
 >> rw [ABS_SUB, extreal_abs_def, extreal_sub_eq]
QED

Theorem abs_sub' :
    !x y. abs(x - y) = abs(y - x)
Proof
    rpt GEN_TAC
 >> Cases_on `x` >> Cases_on `y`
 >> rw [abs_sub, extreal_abs_def, extreal_sub_def, extreal_add_def]
QED

Theorem abs_triangle_sub' :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x) <= abs(y) + abs(y - x)
Proof
    rpt STRIP_TAC
 >> Know ‘abs (y - x) = abs (x - y)’
 >- (MATCH_MP_TAC abs_sub >> art [])
 >> Rewr'
 >> MATCH_MP_TAC abs_triangle_sub >> art []
QED

Theorem abs_triangle_sub_full' :
    !x y. abs(x) <= abs(y) + abs(y - x)
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [abs_sub']
 >> REWRITE_TAC [abs_triangle_sub_full]
QED

Theorem abs_neg_eq[simp] :
    !x :extreal. abs (-x) = abs x
Proof
    GEN_TAC
 >> ‘0 <= x \/ x < 0’ by METIS_TAC [let_total]
 >- (‘abs x = x’ by PROVE_TAC [abs_refl] >> POP_ORW \\
     fs [le_lt] >> MP_TAC (Q.SPEC ‘-x’ abs_neg) \\
    ‘-x < 0’ by METIS_TAC [lt_neg, neg_0] >> rw [neg_neg])
 >> rw [abs_neg, abs_refl]
 >> rw [Once (GSYM le_neg), neg_0]
 >> MATCH_MP_TAC lt_imp_le >> art []
QED

(* cf. realTheory.ABS_TRIANGLE_NEG *)
Theorem abs_triangle_neg :
    !x y. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf ==>
          abs(x - y) <= abs(x) + abs(y)
Proof
    rpt STRIP_TAC
 >> Know ‘x - y = x + -y’
 >- (MATCH_MP_TAC extreal_sub_add >> art [])
 >> Rewr'
 >> ‘abs y = abs (-y)’ by rw [] >> POP_ORW
 >> MATCH_MP_TAC abs_triangle >> art []
 >> Cases_on ‘y’ >> rw [extreal_ainv_def]
QED

Theorem abs_triangle_neg_full :
    !x y. abs(x - y) <= abs(x) + abs(y)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x <> PosInf /\ x <> NegInf’
 >- (Cases_on ‘y <> PosInf /\ y <> NegInf’
     >- (MATCH_MP_TAC abs_triangle_neg >> art []) \\
    ‘abs y = PosInf’ by fs [extreal_abs_def] >> POP_ORW \\
     Suff ‘abs x + PosInf = PosInf’ >- rw [le_infty] \\
     Suff ‘abs x <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> rw [abs_pos])
 >> ‘abs x = PosInf’ by fs [extreal_abs_def] >> POP_ORW
 >> Suff ‘PosInf + abs y = PosInf’ >- rw [le_infty]
 >> Suff ‘abs y <> NegInf’ >- METIS_TAC [add_infty]
 >> MATCH_MP_TAC pos_not_neginf >> rw [abs_pos]
QED

Theorem abs_mul :
    !x y :extreal. abs (x * y) = abs x * abs y
Proof
    rpt STRIP_TAC
 >> Cases_on `x` >> Cases_on `y`
 >> RW_TAC std_ss [extreal_abs_def, extreal_mul_def]
 >> fs []
 >> REWRITE_TAC [ABS_MUL]
QED

(* ------------------------------------------------------------------------- *)
(*   Division and Inversion                                                  *)
(* ------------------------------------------------------------------------- *)

(* added antecedent `y <> 0` *)
Theorem extreal_div_eq :
    !x y. y <> 0 ==> (Normal x / Normal y = Normal (x / y))
Proof
    rpt Cases
 >> RW_TAC std_ss [extreal_div_def, extreal_inv_def, extreal_mul_def, real_div]
QED

(* added antecedent ``m <> 0`` *)
Theorem quotient_normal :
    !n m. m <> 0 ==> (&n / &m = Normal (&n / &m))
Proof
    RW_TAC std_ss [extreal_div_eq, extreal_of_num_def, REAL_OF_NUM_EQ]
QED

Theorem extreal_inv_eq :
    !x. x <> 0 ==> (inv (Normal x) = Normal (inv x))
Proof
    METIS_TAC [extreal_inv_def]
QED

Theorem normal_inv_eq :
    !x. x <> 0 ==> (Normal (inv x) = inv (Normal x))
Proof
    METIS_TAC [extreal_inv_def]
QED

Theorem inv_one[simp] :
    extreal_inv 1 = 1
Proof
    RW_TAC std_ss [extreal_inv_def, extreal_of_num_def, REAL_10, REAL_INV1]
QED

Theorem inv_1over : (* was: div_lone *)
    !x. x <> 0 ==> (inv x = 1 / x)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_inv_def, extreal_div_def, extreal_mul_def,
                    extreal_of_num_def, REAL_10, REAL_INV1]
QED

Theorem div_one[simp] : (* was: div_rone *)
    !x :extreal. x / 1 = x
Proof
    RW_TAC real_ss [extreal_div_def, extreal_of_num_def, extreal_inv_def]
 >> REWRITE_TAC [REAL_INV1, GSYM extreal_of_num_def, mul_rone]
QED

Theorem div_refl :
    !x :extreal. x <> 0 /\ x <> PosInf /\ x <> NegInf ==> (x / x = 1)
Proof
    Cases
 >> RW_TAC real_ss [extreal_div_def, extreal_mul_def, extreal_inv_def,
                    extreal_not_infty, extreal_of_num_def, REAL_MUL_RINV]
QED

Theorem div_refl_pos :
    !x :extreal. 0 < x /\ x <> PosInf ==> (x / x = 1)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC div_refl >> fs [lt_le]
 >> MATCH_MP_TAC pos_not_neginf >> art []
QED

Theorem inv_pos :
    !x. 0 < x /\ x <> PosInf ==> 0 < 1 / x
Proof
    Cases
 >> RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_lt_def,
                    extreal_mul_def, extreal_le_def, lt_infty, le_infty]
 >> FULL_SIMP_TAC real_ss [Once real_lte, Once REAL_LT_LE, extreal_div_eq,
                           extreal_le_def]
 >> METIS_TAC [REAL_LE_DIV, REAL_LE_01, REAL_INV_NZ, REAL_INV_1OVER]
QED

Theorem inv_pos' :
    !x. 0 < x /\ x <> PosInf ==> 0 < inv x
Proof
    RW_TAC std_ss []
 >> `x <> 0` by PROVE_TAC [lt_le]
 >> ASM_SIMP_TAC std_ss [inv_1over]
 >> MATCH_MP_TAC inv_pos >> art []
QED

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

Theorem rinv_uniq :
    !x y. (x * y = 1) ==> (y = inv x)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_inv_def, extreal_mul_def, extreal_of_num_def]
 >> Know `r <> 0`
 >- (CCONTR_TAC >> fs [])
 >> IMP_RES_TAC REAL_RINV_UNIQ >> POP_ORW
 >> METIS_TAC [extreal_inv_def]
QED

Theorem linv_uniq :
    !x y. (x * y = 1) ==> (x = inv y)
Proof
    RW_TAC std_ss [rinv_uniq, mul_comm]
QED

Theorem le_rdiv :
    !x y z. 0 < x ==> (y * Normal x <= z <=> y <= z / Normal x)
Proof
    STRIP_TAC >> rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, extreal_div_def, extreal_inv_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_REFL,
                   REAL_INV_EQ_0, REAL_INV_POS, REAL_LT_IMP_NE]
 >> METIS_TAC [REAL_NEG_NZ, REAL_LE_RDIV_EQ, real_div]
QED

Theorem le_ldiv :
    !x y z. 0 < x ==> (y <= z * Normal x <=> y / Normal x <= z)
Proof
    STRIP_TAC >> rpt Cases
 >> RW_TAC std_ss [extreal_mul_def, extreal_div_def, extreal_inv_def, extreal_le_def,
                   le_infty, extreal_of_num_def, extreal_not_infty, REAL_LT_REFL,
                   REAL_INV_EQ_0, REAL_INV_POS, REAL_LT_IMP_NE]
 >> METIS_TAC [REAL_NEG_NZ, REAL_LE_LDIV_EQ, real_div]
QED

Theorem lt_rdiv :
    !x y z. 0 < z ==> (x < y / Normal z <=> x * Normal z < y)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [REAL_INV_EQ_0, REAL_INV_POS, extreal_lt_eq, REAL_LT_RDIV_EQ,
                   GSYM real_div,  extreal_inv_def,
                   REAL_LT_REFL, lt_refl, lt_infty, le_infty, extreal_div_def,
                   extreal_div_eq, extreal_mul_def, REAL_LT_IMP_NE]
QED

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

Theorem lt_ldiv :
    !x y z. 0 < z ==> (x / Normal z < y <=> x < y * Normal z)
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [REAL_INV_EQ_0, REAL_INV_POS, extreal_lt_eq, REAL_LT_LDIV_EQ,
                   GSYM real_div, extreal_inv_def,
                   REAL_LT_REFL, lt_refl, lt_infty, le_infty, extreal_div_def,
                   extreal_div_eq, extreal_mul_def, REAL_LT_IMP_NE]
QED

Theorem lt_rdiv_neg :
    !x y z. z < 0 ==> (y / Normal z < x <=> x * Normal z < y)
Proof
    NTAC 2 Cases >> RW_TAC std_ss []
 >> RW_TAC std_ss [REAL_INV_POS, REAL_LE_LT, GSYM real_lte, REAL_INV_EQ_0,
                   REAL_INV_POS, REAL_LT_REFL, lt_refl, extreal_div_eq,
                   extreal_lt_eq, REAL_LT_RDIV_EQ_NEG, GSYM real_div,
                   lt_infty, le_infty, extreal_div_def, extreal_inv_def,
                   extreal_mul_def, REAL_LT_REFL, REAL_LT_IMP_NE]
 >> METIS_TAC [REAL_LT_ANTISYM, real_lte, REAL_NEG_NZ, REAL_LT_INV_EQ,
               lt_refl, lt_infty]
QED

(* `x, y` must be reals, `z <> 0` *)
Theorem div_add :
    !x y z. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf /\ z <> 0 ==>
           (x / z + y / z = (x + y) / z)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_div_def, extreal_mul_def,
                    extreal_of_num_def, extreal_inv_def]
 >> REAL_ARITH_TAC
QED

(* `z` must be non-zero normal reals, `x + y` must be defined *)
Theorem div_add2 :
    !x y z. ((x <> PosInf /\ y <> PosInf) \/ (x <> NegInf /\ y <> NegInf)) /\
             z <> 0 /\ z <> PosInf /\ z <> NegInf ==>
            (x / z + y / z = (x + y) / z)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_add_def, extreal_div_def, extreal_mul_def,
                    extreal_of_num_def, extreal_inv_def]
 >> REAL_ARITH_TAC
QED

Theorem div_sub :
    !x y z. x <> PosInf /\ x <> NegInf /\ y <> PosInf /\ y <> NegInf /\ z <> 0 ==>
           (x / z - y / z = (x - y) / z)
Proof
    rpt Cases
 >> RW_TAC real_ss [extreal_sub_def, extreal_div_def, extreal_mul_def,
                    extreal_of_num_def, extreal_inv_def]
 >> REAL_ARITH_TAC
QED

(* NOTE: `0 <= x` is changed to `0 < x` otherwise `inv x` is not defined *)
Theorem le_inv :
    !x. 0 < x ==> 0 <= inv x
Proof
    Cases >> RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_le_def,
                             le_infty, lt_refl, extreal_lt_eq, REAL_LT_IMP_NE]
 >> MATCH_MP_TAC REAL_LE_INV
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

Theorem div_infty :
    !x. x <> PosInf /\ x <> NegInf ==> (x / PosInf = 0) /\ (x / NegInf = 0)
Proof
    Cases
 >> RW_TAC std_ss [extreal_div_def, extreal_inv_def, GSYM extreal_of_num_def, mul_rzero]
QED

Theorem infty_div :
    !r. 0 < r ==> (PosInf / Normal r = PosInf) /\ (NegInf / Normal r = NegInf)
Proof
    GEN_TAC >> DISCH_TAC
 >> IMP_RES_TAC REAL_LT_IMP_NE
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, GSYM extreal_of_num_def,
                    extreal_mul_def, mul_rzero, REAL_INV_POS, REAL_INV_EQ_0]
QED

Theorem zero_div : (* cf. REAL_DIV_LZERO *)
    !x :extreal. x <> 0 ==> (0 / x = 0)
Proof
    Cases
 >> RW_TAC std_ss [extreal_div_def, mul_lzero, extreal_of_num_def]
QED

Theorem ldiv_eq : (* REAL_EQ_LDIV_EQ *)
    !x y z. 0 < z /\ z < PosInf ==> ((x / z = y) <=> (x = y * z))
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_infty, extreal_of_num_def, extreal_lt_eq, extreal_not_infty,
                   extreal_mul_def, infty_div, REAL_LT_REFL, extreal_div_def,
                   extreal_inv_def, extreal_mul_def, GSYM real_div, REAL_LT_IMP_NE]
 >> MATCH_MP_TAC REAL_EQ_LDIV_EQ >> art []
QED

Theorem rdiv_eq : (* REAL_EQ_RDIV_EQ *)
    !x y z. 0 < z /\ z < PosInf ==> ((x = y / z) <=> (x * z = y))
Proof
    NTAC 3 Cases
 >> RW_TAC std_ss [lt_infty, extreal_of_num_def, extreal_lt_eq, extreal_not_infty,
                   extreal_mul_def, infty_div, REAL_LT_REFL, extreal_div_def,
                   extreal_inv_def, extreal_mul_def, GSYM real_div, REAL_POS_NZ]
 >> MATCH_MP_TAC REAL_EQ_RDIV_EQ >> art []
QED

(* NOTE: ‘x <> PosInf /\ x <> NegInf’ cannot be removed when ‘y = PosInf’ *)
Theorem div_eq_mul_linv :
    !x y. x <> PosInf /\ x <> NegInf /\ 0 < y ==> (x / y = (inv y) * x)
Proof
    RW_TAC std_ss []
 >> Cases_on `y = PosInf`
 >- ASM_SIMP_TAC std_ss [div_infty, extreal_inv_def, GSYM extreal_of_num_def, mul_lzero]
 >> Know `0 < y /\ y < PosInf` >- art [GSYM lt_infty]
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP ldiv_eq))
 >> REWRITE_TAC [GSYM mul_assoc, Once mul_comm]
 >> `y * inv y = 1` by PROVE_TAC [mul_comm, mul_linv_pos]
 >> ASM_REWRITE_TAC [mul_rone]
QED

(* |- !x y. x <> PosInf /\ x <> NegInf /\ 0 < y ==> x / y = x * realinv y *)
Theorem div_eq_mul_rinv = ONCE_REWRITE_RULE [mul_comm] div_eq_mul_linv

Theorem inv_lt_antimono: (* new *)
    !x y :extreal. 0 < x /\ 0 < y ==> (inv x < inv y <=> y < x)
Proof
    rpt strip_tac
 >> `x <> 0 /\ y <> 0` by PROVE_TAC [lt_le]
 >> Cases_on `x`
 >> fs [lt_infty, extreal_inv_def, extreal_of_num_def, lt_refl,
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
 >> fs [lt_infty, extreal_inv_def, extreal_of_num_def, lt_refl,
        extreal_lt_eq]
 >> ASM_REWRITE_TAC [real_lt, REAL_LE_LT]
QED

Theorem inv_inj: (* new *)
    !x y :extreal. 0 < x /\ 0 < y ==> ((inv x = inv y) <=> (x = y))
Proof
    rpt STRIP_TAC
 >> `x <> 0 /\ y <> 0` by PROVE_TAC [lt_le]
 >> Cases_on `x` >> Cases_on `y`
 >> fs [extreal_inv_def, extreal_of_num_def, extreal_not_infty,
        lt_infty, extreal_lt_eq]
QED

Theorem inv_le_antimono :
    !x y :extreal. 0 < x /\ 0 < y ==> (inv x <= inv y <=> y <= x)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [le_lt]
 >> EQ_TAC >> STRIP_TAC
 >| [ DISJ1_TAC >> PROVE_TAC [inv_lt_antimono],
      DISJ2_TAC >> PROVE_TAC [inv_inj],
      DISJ1_TAC >> PROVE_TAC [inv_lt_antimono],
      DISJ2_TAC >> PROVE_TAC [inv_inj] ]
QED

Theorem inv_le_antimono_imp :
    !x y :extreal. 0 < y /\ y <= x ==> inv x <= inv y
Proof
    rpt STRIP_TAC
 >> Suff ‘inv x <= inv y <=> y <= x’ >- rw []
 >> MATCH_MP_TAC inv_le_antimono >> art []
 >> MATCH_MP_TAC lte_trans
 >> Q.EXISTS_TAC ‘y’ >> art []
QED

Theorem inv_not_infty :
  !x :extreal. x <> 0 ==> inv x <> PosInf /\ inv x <> NegInf
Proof
  Cases >> rw[extreal_inv_def]
QED

Theorem inv_infty :
    inv PosInf = 0 /\ inv NegInf = 0
Proof
    rw [extreal_of_num_def, extreal_inv_def]
QED

Theorem div_not_infty :
  !x y:extreal. y <> 0 ==> Normal x / y <> PosInf /\ Normal x / y <> NegInf
Proof
  rpt GEN_TAC
  >> Cases_on `y`
  >> rw[extreal_div_def, extreal_inv_def, extreal_not_infty,
        extreal_of_num_def]
  >> simp[extreal_mul_def]
QED

Theorem div_mul_refl :
    !(x :extreal) r. r <> 0 ==> x = x / Normal r * Normal r
Proof
  RW_TAC std_ss [extreal_div_def, extreal_inv_def, GSYM mul_assoc,
                 extreal_mul_def]
  >> RW_TAC real_ss [REAL_MUL_LINV, GSYM extreal_of_num_def, mul_rone]
QED

(* NOTE: removed ‘x <> PosInf /\ x <> NegInf’; changed ‘0 < r’ to ‘r <> 0’ *)
Theorem mul_div_refl :
    !(x :extreal) r. r <> 0 ==> x = x * Normal r / Normal r
Proof
    rpt STRIP_TAC
 >> ‘x * Normal r / Normal r = x * Normal r * inv (Normal r)’
      by rw [extreal_div_def]
 >> POP_ORW
 >> ‘x * Normal r * inv (Normal r) = x * inv (Normal r) * Normal r’
      by PROVE_TAC [mul_comm, mul_assoc]
 >> POP_ORW
 >> ‘x * inv (Normal r) = x / Normal r’ by rw [extreal_div_def]
 >> POP_ORW
 >> MATCH_MP_TAC div_mul_refl >> art []
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

(* cf. REAL_EQ_MUL_LCANCEL *)
Theorem mul_lcancel :
    !x y (z :extreal). x <> PosInf /\ x <> NegInf ==>
                     ((x * y = x * z) <=> (x = 0) \/ (y = z))
Proof
    rpt STRIP_TAC
 >> `?r. x = Normal r` by METIS_TAC [extreal_cases]
 >> POP_ORW >> KILL_TAC
 >> Cases_on `y` >> Cases_on `z`
 >> rw[extreal_mul_def, extreal_not_infty, extreal_of_num_def,
       REAL_MUL_LZERO, REAL_MUL_RZERO]
 >> REWRITE_TAC [REAL_EQ_MUL_LCANCEL]
QED

(* |- !x y z. x <> PosInf /\ x <> NegInf ==> (y * x = z * x <=> x = 0 \/ y = z) *)
Theorem mul_rcancel = ONCE_REWRITE_RULE [mul_comm] mul_lcancel

Theorem inv_mul :
    !x y. x <> 0 /\ y <> 0 ==> (inv (x * y) = inv x * inv y)
Proof
  rpt STRIP_TAC
  >> Cases_on `x` >> Cases_on `y`
  >> fs[extreal_mul_def, extreal_inv_def, extreal_not_infty,
        extreal_of_num_def]
  >> rw[extreal_inv_def]
QED

Theorem abs_div :
  !x y. x <> PosInf /\ x <> NegInf /\ y <> 0 ==> (abs (x / y) = abs x / abs y)
Proof
  rpt STRIP_TAC
  >> Cases_on `x` >> Cases_on `y`
  >> fs[extreal_div_def, extreal_inv_def, extreal_not_infty,
       extreal_of_num_def, extreal_abs_def, extreal_mul_def]
  >> rename1 `s <> 0`
  >> `abs s <> 0` by PROVE_TAC [ABS_ZERO]
  >> simp[extreal_div_eq, ABS_MUL, real_div, ABS_INV]
QED

Theorem abs_div_normal :
    !x y. y <> 0 ==> (abs (x / Normal y) = abs x / Normal (abs y))
Proof
    rpt STRIP_TAC
 >> ‘abs y <> 0’ by PROVE_TAC [ABS_ZERO]
 >> Cases_on `x`
 >> RW_TAC std_ss [extreal_div_def, abs_mul, extreal_inv_def, extreal_abs_def, ABS_INV]
QED

(* cf. REAL_INVINV *)
Theorem inv_inv :
    !x. x <> 0 /\ x <> PosInf /\ x <> NegInf ==> inv (inv x) = x
Proof
    Cases >> rw [extreal_of_num_def, extreal_inv_eq]
 >> ASM_SIMP_TAC std_ss [REAL_INVINV]
QED

(* ------------------------------------------------------------------------- *)
(*         x pow n                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem pow_0[simp] :
    !x. x pow 0 = 1
Proof
    Cases >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, pow]
QED

(* an equivalent "recursive" definition like realTheory.pow *)
Theorem extreal_pow :
   (!x :extreal. x pow 0 = 1) /\ !(x :extreal) n. x pow SUC n = x * x pow n
Proof
    rw [] >> Cases_on ‘x’
 >> RW_TAC arith_ss [extreal_pow_def, extreal_mul_def, GSYM extreal_of_num_def, pow,
                     mul_rone, EVEN] >- fs [EVEN]
 >> PROVE_TAC []
QED

Theorem zero_pow : (* POW_0 *)
    !n. 0 < n ==> (extreal_pow 0 n = 0)
Proof
    rw[extreal_of_num_def, extreal_pow_def]
QED

Theorem pow_1[simp] :
    !x. x pow 1 = x
Proof
    Cases >> RW_TAC std_ss [extreal_pow_def, POW_1]
QED

Theorem one_pow[simp] : (* POW_ONE *)
    !n. extreal_pow 1 n = 1
Proof
  rw[extreal_of_num_def, extreal_pow_def, POW_ONE]
QED

Theorem pow_2 :
    !x. x pow 2 = x * x
Proof
    Cases >> RW_TAC std_ss [extreal_pow_def, extreal_mul_def, POW_2]
QED

Theorem pow_zero[simp] :
    !n x :extreal. (x pow (SUC n) = 0) <=> (x = 0)
Proof
    STRIP_TAC >> Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, POW_ZERO_EQ]
QED

Theorem pow_zero_imp:
  !n x. (x pow n = 0) ==> (x = 0)
Proof
    STRIP_TAC >> Cases
 >> RW_TAC std_ss [extreal_pow_def,extreal_of_num_def,REAL_LT_01,REAL_LT_IMP_NE]
 >> METIS_TAC [POW_ZERO]
QED

Theorem le_pow2 :
    !x. 0 <= x pow 2
Proof
    Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, REAL_LE_POW2]
QED

Theorem abs_pow2[simp] :
    !x. (abs x) pow 2 = x pow 2
Proof
    GEN_TAC
 >> Cases_on `0 <= x` >- fs [GSYM abs_refl]
 >> fs [GSYM extreal_lt_def, abs_neg, pow_2, neg_mul2]
QED

Theorem pow_2_abs :
    !x. x pow 2 = abs x * abs x
Proof
    RW_TAC std_ss [Once (GSYM abs_pow2), pow_2]
QED

(* NOTE: ‘!n’ is moved to top-level *)
Theorem pow_pos_le :
    !n x. 0 <= x ==> 0 <= x pow n
Proof
    Q.X_GEN_TAC ‘n’
 >> Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, POW_POS]
 >> METIS_TAC [le_infty, le_01, REAL_LE_01, extreal_of_num_def]
QED

(* NOTE: ‘!n’ is moved to top-level *)
Theorem pow_pos_lt :
    !n x. 0 < x ==> 0 < x pow n
Proof
    NTAC 2 Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, extreal_lt_eq,
                   POW_POS_LT, REAL_LT_01, lt_infty, extreal_not_infty]
 >> METIS_TAC [pow, REAL_LT_01]
QED

Theorem pow_le :
    !n x y. 0 <= x /\ x <= y ==> x pow n <= y pow n
Proof
    STRIP_TAC >> NTAC 2 Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, POW_LE,
                   lt_infty, le_infty, extreal_not_infty, REAL_LE_REFL, pow]
QED

Theorem pow_lt :
    !n x y. 0 <= x /\ x < y ==> x pow SUC n < y pow SUC n
Proof
    STRIP_TAC >> NTAC 2 Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, REAL_POW_LT2,
                   lt_infty, le_infty, extreal_not_infty, extreal_lt_eq]
QED

Theorem pow_lt2 :
    !n x y. n <> 0 /\ 0 <= x /\ x < y ==> x pow n < y pow n
Proof
    STRIP_TAC >> NTAC 2 Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def, REAL_POW_LT2,
                   lt_infty, le_infty, extreal_not_infty, extreal_lt_eq]
QED

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

Theorem pow_eq :
    !n x y. n <> 0 /\ 0 <= x /\ 0 <= y ==> ((x = y) <=> (x pow n = y pow n))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw []
 >> fs [GSYM le_antisym]
 >> METIS_TAC [pow_le_full]
QED

Theorem pow_le_mono :
    !x n m. 1 <= x /\ n <= m ==> x pow n <= x pow m
Proof
    Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_le_def,
                   lt_infty, le_infty, extreal_not_infty, REAL_LE_REFL]
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
 >> RW_TAC real_ss []
QED

Theorem pow_pos_even :
    !x. x < 0 ==> ((0 < x pow n) <=> (EVEN n))
Proof
    Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_not_infty,
                   le_infty, lt_infty, extreal_lt_eq, REAL_LT_01, POW_POS_EVEN]
QED

Theorem pow_neg_odd :
    !x. x < 0 ==> ((x pow n < 0) <=> (ODD n))
Proof
    Cases
 >> RW_TAC std_ss [extreal_pow_def, extreal_of_num_def, extreal_not_infty,
                   le_infty, lt_infty, extreal_lt_eq, extreal_le_def,
                   REAL_LT_01, EVEN_ODD, extreal_lt_def, extreal_le_def,
                   REAL_LE_01, POW_NEG_ODD, GSYM real_lt]
QED

(* antecedents added due to new definition of `extreal_add` *)
Theorem add_pow2 :
    !x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
          ((x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y)
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_pow_def, extreal_mul_def, extreal_add_def,
                    extreal_of_num_def]
 >> REWRITE_TAC [ADD_POW_2]
QED

Theorem REAL_MUL_POS_LT[local] : (* from intergrationTheory *)
    !x y:real. &0 < x * y <=> &0 < x /\ &0 < y \/ x < &0 /\ y < &0
Proof
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC(SPEC ``x:real`` REAL_LT_NEGTOTAL) THEN
  STRIP_ASSUME_TAC(SPEC ``y:real`` REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL] THEN
  ASSUM_LIST(MP_TAC o MATCH_MP REAL_LT_MUL o end_itlist CONJ) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC
QED

Theorem infty_pow2[simp] :
    (PosInf pow 2 = PosInf) /\ (NegInf pow 2 = PosInf)
Proof
    rw [pow_2, extreal_mul_def]
QED

Theorem add_pow2_pos : (* was: add_pow02 *)
    !x y. 0 < x /\ x <> PosInf /\ 0 <= y ==>
         ((x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y)
Proof
    RW_TAC std_ss []
 >> `x <> NegInf` by METIS_TAC [lt_trans, lt_infty, num_not_infty]
 >> `y <> NegInf` by METIS_TAC [lte_trans, lt_infty, num_not_infty]
 >> ASM_CASES_TAC ``y = PosInf`` >| [ALL_TAC, METIS_TAC [add_pow2]]
 >> ASM_SIMP_TAC std_ss []
 >> `x = Normal (real x)` by METIS_TAC [normal_real]
 >> ONCE_ASM_REWRITE_TAC []
 >> SIMP_TAC std_ss [extreal_add_def, extreal_mul_def, extreal_of_num_def]
 >> ONCE_REWRITE_TAC [infty_pow2]
 >> rpt COND_CASES_TAC
 >> ASM_SIMP_TAC std_ss [extreal_pow_def, extreal_add_def]
 >> POP_ASSUM MP_TAC
 >> ONCE_REWRITE_TAC [MONO_NOT_EQ]
 >> RW_TAC std_ss [real_normal, REAL_MUL_POS_LT]
 >> DISJ1_TAC
 >> ASM_SIMP_TAC real_ss [GSYM extreal_lt_eq, normal_real, GSYM extreal_of_num_def]
QED

Theorem sub_pow2 :
    !x y. x <> NegInf /\ x <> PosInf /\ y <> NegInf /\ y <> PosInf ==>
        ((x - y) pow 2 = x pow 2 + y pow 2 - 2 * x * y)
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [extreal_pow_def, extreal_mul_def, extreal_add_def,
                    extreal_of_num_def, extreal_ainv_def, extreal_sub_def]
 >> REWRITE_TAC [SUB_POW_2]
QED

Theorem pow_add :
    !x n m. x pow (n + m) = x pow n * x pow m
Proof
    Cases
 >> RW_TAC real_ss [extreal_pow_def, POW_ADD, extreal_of_num_def,
                    extreal_mul_def, mul_rone, mul_lone]
 >> METIS_TAC [ADD_CLAUSES, EVEN_ADD]
QED

Theorem pow_mul :
    !n x y. (x * y) pow n = x pow n * y pow n
Proof
    Cases >- RW_TAC std_ss [pow_0,mul_lone]
 >> NTAC 2 Cases
 >> RW_TAC real_ss [extreal_mul_def, extreal_pow_def, pow_zero, POW_ZERO_EQ,
                    POW_POS_LT, POW_MUL]
 >> FULL_SIMP_TAC real_ss [GSYM real_lte]
 >> METIS_TAC [POW_POS_EVEN, POW_NEG_ODD, REAL_LT_LE, POW_POS_LT, real_lt,
               POW_ZERO_EQ, EVEN_ODD]
QED

Theorem pow_minus1[simp] :
    !n. -1 pow (2 * n) = (1 :extreal)
Proof
    RW_TAC std_ss [extreal_of_num_def, extreal_ainv_def, extreal_pow_def, POW_MINUS1]
QED

Theorem pow_not_infty :
    !n x. x <> NegInf /\ x <> PosInf ==> x pow n <> NegInf /\ x pow n <> PosInf
Proof
    Cases
 >> METIS_TAC [extreal_pow_def, extreal_not_infty, extreal_cases]
QED

Theorem pow_inv : (* cf. REAL_POW_INV *)
    !n y. y <> 0 ==> inv (y pow n) = (inv y) pow n
Proof
    rpt STRIP_TAC
 >> Cases_on `n = 0` >- rw [pow_0, inv_one]
 >> `0 < n` by RW_TAC arith_ss []
 >> `0 pow n = (0 :real)` by (Cases_on `n` >> rw [POW_0])
 >> Cases_on `y` >> RW_TAC std_ss [extreal_pow_def, extreal_inv_def]
 >> `r <> 0` by (strip_tac >> gvs[])
 >> `r pow n <> 0` by PROVE_TAC [POW_NZ]
 >> simp[extreal_inv_eq, extreal_pow_def]
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

Theorem pow_pow : (* cf. REAL_POW_POW *)
    !(x :extreal) m n. (x pow m) pow n = x pow (m * n)
Proof
    rpt GEN_TAC
 >> Cases_on ‘x’
 >| [ (* goal 1 (of 3) *)
      Cases_on ‘m = 0’ >- rw [extreal_pow_def] \\
      Cases_on ‘EVEN m’
      >- (rw [extreal_pow_def] >> fs [EVEN_MULT]) \\
      rw [extreal_pow_def] >> gs [EVEN_MULT],
      (* goal 2 (of 3) *)
      Cases_on ‘m = 0’ >- rw [extreal_pow_def] \\
      Cases_on ‘EVEN m’ >- rw [extreal_pow_def] \\
      rw [extreal_pow_def],
      (* goal 3 (of 3) *)
      rw [extreal_pow_def, REAL_POW_POW] ]
QED

Theorem abs_le_square_plus1 :
    !(x :extreal). abs x <= x pow 2 + 1
Proof
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
 >> MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `1` >> art [le_01]
QED

Theorem abs_pow_le_mono :
    !(x :extreal) n m. n <= m ==> (abs x) pow n <= 1 + (abs x) pow m
Proof
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
 >> CONJ_TAC >> MATCH_MP_TAC lt_imp_le >> art []
QED

(* This result is needed for proving Cauchy-Schwarz inequality *)
Theorem abs_le_half_pow2 :
    !x y :extreal. abs (x * y) <= Normal (1 / 2) * (x pow 2 + y pow 2)
Proof
    NTAC 2 Cases
 >> ASM_SIMP_TAC real_ss [extreal_abs_def, extreal_mul_def, pow_2, extreal_add_def,
                          le_refl, le_infty, extreal_le_eq]
 >> REWRITE_TAC [GSYM POW_2, ABS_LE_HALF_POW2]
QED

(* ------------------------------------------------------------------------- *)
(*         SQRT                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem sqrt_pos_le :
    !x. 0 <= x ==> 0 <= sqrt x
Proof
    Cases
 >> RW_TAC std_ss [extreal_sqrt_def, extreal_of_num_def, extreal_le_def, SQRT_POS_LE]
QED

Theorem sqrt_pos_lt :
    !x. 0 < x ==> 0 < sqrt x
Proof
    Cases
 >> RW_TAC std_ss [extreal_sqrt_def, extreal_of_num_def, extreal_le_def,
                   extreal_lt_eq, lt_infty, SQRT_POS_LT]
QED

Theorem sqrt_pos_ne :
    !x. 0 < x ==> sqrt x <> 0
Proof
    Q.X_GEN_TAC ‘x’
 >> DISCH_THEN (ASSUME_TAC o (MATCH_MP sqrt_pos_lt))
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC lt_imp_ne >> art []
QED

Theorem pow2_sqrt :
    !x. 0 <= x ==> (sqrt (x pow 2) = x)
Proof
    Cases
 >> RW_TAC real_ss [extreal_sqrt_def, extreal_pow_def, POW_2_SQRT, extreal_of_num_def,
                    extreal_le_def]
QED

Theorem sqrt_0 :
    sqrt 0 = 0
Proof
    rw [extreal_of_num_def, extreal_sqrt_def, SQRT_0]
QED

Theorem sqrt_1 :
    sqrt 1 = 1
Proof
    rw [extreal_of_num_def, extreal_sqrt_def, SQRT_1]
QED

Theorem sqrt_pow2 :
    !x. ((sqrt x) pow 2 = x) <=> 0 <= x
Proof
    Cases
 >> RW_TAC real_ss [extreal_sqrt_def, extreal_pow_def, SQRT_POW2,
                    extreal_of_num_def, extreal_le_def]
 >> METIS_TAC [le_pow2, lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans]
QED

Theorem sqrt_mono_le :
    !x y. 0 <= x /\ x <= y ==> sqrt x <= sqrt y
Proof
    NTAC 2 Cases
 >> RW_TAC real_ss [SQRT_MONO_LE, extreal_sqrt_def, extreal_pow_def, POW_2_SQRT,
                    extreal_of_num_def, extreal_le_def, le_infty, extreal_not_infty]
QED

Theorem pow2_le_eq :
    !x y. 0 <= x /\ 0 <= y ==> (x <= y <=> x pow 2 <= y pow 2)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> DISCH_TAC >- (MATCH_MP_TAC pow_le >> art [])
 >> `0 <= x pow 2` by PROVE_TAC [le_pow2]
 >> `sqrt (x pow 2) <= sqrt (y pow 2)` by PROVE_TAC [sqrt_mono_le]
 >> METIS_TAC [GSYM pow2_sqrt]
QED

Theorem sqrt_le_x :
    !(x :extreal). 1 <= x ==> sqrt x <= x
Proof
    rpt STRIP_TAC
 >> ‘0 <= x’ by PROVE_TAC [le_01, le_trans]
 >> Know ‘sqrt x <= x <=> (sqrt x) pow 2 <= x pow 2’
 >- (MATCH_MP_TAC pow2_le_eq >> rw [sqrt_pos_le])
 >> Rewr'
 >> ‘(sqrt x) pow 2 = x’ by rw [sqrt_pow2]
 >> POP_ORW
 >> REWRITE_TAC [pow_2]
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone]
 >> MATCH_MP_TAC le_lmul_imp >> art []
QED

(* In sqrt_le_x, if ‘x’ is an integer then ‘1 <= x’ can be dropped. *)
Theorem sqrt_le_n :
    !n. sqrt (&n :extreal) <= &n
Proof
    Q.X_GEN_TAC ‘n’
 >> Cases_on ‘n’ >- (rw [extreal_of_num_def, extreal_sqrt_def, SQRT_0])
 >> MATCH_MP_TAC sqrt_le_x
 >> rw [extreal_of_num_def, extreal_le_eq]
QED

Theorem sqrt_mul :
    !x y. 0 <= x /\ 0 <= y ==> sqrt (x * y) = sqrt x * sqrt y
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x = PosInf’
 >- (‘y = 0 \/ 0 < y’ by PROVE_TAC [le_lt] \\
     fs [extreal_sqrt_def, mul_infty, sqrt_0] \\
     ‘0 < sqrt y’ by PROVE_TAC [sqrt_pos_lt] \\
     METIS_TAC [mul_infty])
 >> Cases_on ‘y = PosInf’
 >- (‘x = 0 \/ 0 < x’ by PROVE_TAC [le_lt] \\
     fs [extreal_sqrt_def, mul_infty, sqrt_0] \\
     ‘0 < sqrt x’ by PROVE_TAC [sqrt_pos_lt] \\
     METIS_TAC [mul_infty])
 >> ‘x <> NegInf /\ y <> NegInf’ by rw [pos_not_neginf]
 >> ‘?X. 0 <= X /\ x = Normal X’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] >> POP_ORW
 >> ‘?Y. 0 <= Y /\ y = Normal Y’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] >> POP_ORW
 >> ‘0 <= X * Y’ by rw [REAL_LE_MUL]
 >> rw [extreal_mul_def, extreal_sqrt_def, SQRT_MUL]
QED

(* ------------------------------------------------------------------------- *)
(*    Special values                                                         *)
(* ------------------------------------------------------------------------- *)

Theorem half_between[simp] :
    (0 < 1 / 2 /\ 1 / 2 < 1) /\ (0 <= 1 / 2 /\ 1 / 2 <= 1)
Proof
    MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
 >> CONJ_TAC >- PROVE_TAC [lt_imp_le]
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, mul_lone, extreal_lt_def,
                    extreal_le_def, extreal_of_num_def, extreal_not_infty,
                    GSYM real_lt, REAL_INV_1OVER, extreal_mul_def]
QED

Theorem half_not_infty[simp] :
    1 / 2 <> PosInf /\ 1 / 2 <> NegInf
Proof
    rw [lt_infty]
 >- (MATCH_MP_TAC lt_trans \\
     Q.EXISTS_TAC `1` >> rw [half_between] \\
     rw [extreal_of_num_def, lt_infty])
 >> MATCH_MP_TAC lt_trans
 >> Q.EXISTS_TAC `0` >> rw [half_between]
 >> rw [extreal_of_num_def, lt_infty]
QED

Theorem thirds_between[simp] :
    ((0 < 1 / 3 /\ 1 / 3 < 1) /\ (0 < 2 / 3 /\ 2 / 3 < 1)) /\
    ((0 <= 1 / 3 /\ 1 / 3 <= 1) /\ (0 <= 2 / 3 /\ 2 / 3 <= 1))
Proof
    MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
 >> CONJ_TAC >- PROVE_TAC [lt_imp_le]
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, mul_lone, extreal_lt_def,
                    extreal_le_def, extreal_of_num_def, extreal_not_infty,
                    GSYM real_lt, extreal_mul_def, REAL_INV_1OVER]
QED

Theorem fourths_between[simp] :
    ((0 < 1 / 4 /\ 1 / 4 < 1) /\ (0 < 3 / 4 /\ 3 / 4 < 1)) /\
    ((0 <= 1 / 4 /\ 1 / 4 <= 1) /\ (0 <= 3 / 4 /\ 3 / 4 <= 1))
Proof
    MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
 >> CONJ_TAC >- PROVE_TAC [lt_imp_le]
 >> RW_TAC real_ss [extreal_div_def, extreal_inv_def, mul_lone, extreal_lt_def,
                    extreal_le_def, extreal_of_num_def, extreal_not_infty,
                    GSYM real_lt, extreal_mul_def, REAL_INV_1OVER]
QED

Theorem half_cancel :
    2 * (1 / 2) = 1
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_mul_def, extreal_div_eq,
                    EVAL ``2 <> 0:real``, REAL_MUL_RINV, real_div]
QED

(* cf. realTheory.REAL_HALF_DOUBLE *)
Theorem half_double :
    !x :extreal. x / 2 + x / 2 = x
Proof
   ‘0 < (2 :real)’ by rw []
 >> Q.X_GEN_TAC ‘x’ >> Cases_on ‘x’
 >> rw [extreal_of_num_def, extreal_div_eq, extreal_add_def]
 >- rw [infty_div, extreal_add_def]
 >- rw [infty_div, extreal_add_def]
 >> REWRITE_TAC [REAL_HALF_DOUBLE]
QED

(* cf. seqTheory.X_HALF_HALF *)
Theorem x_half_half :
    !x :extreal. 1 / 2 * x + 1 / 2 * x = x
Proof
    STRIP_ASSUME_TAC half_between
 >> Q.X_GEN_TAC ‘x’
 >> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_lone]
 >> Know ‘1 * x = (1 / 2 + 1 / 2) * x’
 >- (rw [extreal_double, half_cancel])
 >> Rewr'
 >> MATCH_MP_TAC (GSYM add_rdistrib) >> rw []
QED

Theorem third_cancel :
    3 * (1 / 3) = 1
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_mul_def, extreal_div_eq,
                    EVAL ``3 <> 0:real``, REAL_MUL_RINV, real_div]
QED

Theorem fourth_cancel :
    4 * (1 / 4) = 1
Proof
    RW_TAC real_ss [extreal_of_num_def, extreal_mul_def, extreal_div_eq,
                    EVAL ``4 <> 0:real``, REAL_MUL_RINV, real_div]
QED

(* ------------------------------------------------------------------------- *)
(*   Minimum and maximum                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem min_le :
    !z x y. min x y <= z <=> x <= z \/ y <= z
Proof
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [le_total, le_trans]
QED

Theorem min_le1 :
    !x y. min x y <= x
Proof
    PROVE_TAC [min_le, le_refl]
QED

Theorem min_le2 :
    !x y. min x y <= y
Proof
    PROVE_TAC [min_le, le_refl]
QED

Theorem le_min :
    !z x y. z <= min x y <=> z <= x /\ z <= y
Proof
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [le_total, le_trans]
QED

Theorem min_le2_imp :
    !x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> min x1 x2 <= min y1 y2
Proof
    RW_TAC std_ss [le_min]
 >> RW_TAC std_ss [min_le]
QED

Theorem min_refl :
    !x. min x x = x
Proof
    RW_TAC std_ss [extreal_min_def, le_refl]
QED

Theorem min_comm :
    !x y. min x y = min y x
Proof
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [le_antisym, le_total]
QED

Theorem min_infty :
    !x. (min x PosInf = x) /\ (min PosInf x = x) /\
        (min NegInf x = NegInf) /\ (min x NegInf = NegInf)
Proof
    RW_TAC std_ss [extreal_min_def, le_infty]
QED

Theorem le_max :
    !z x y. z <= max x y <=> z <= x \/ z <= y
Proof
    RW_TAC std_ss [extreal_max_def]
 >> PROVE_TAC [le_total, le_trans]
QED

Theorem le_max1 :
    !x y. x <= max x y
Proof
    PROVE_TAC [le_max, le_refl]
QED

Theorem le_max2 :
    !x y. y <= max x y
Proof
    PROVE_TAC [le_max, le_refl]
QED

Theorem max_le :
    !z x y. max x y <= z <=> x <= z /\ y <= z
Proof
    RW_TAC std_ss [extreal_max_def]
 >> PROVE_TAC [le_total, le_trans]
QED

Theorem max_le2_imp :
    !x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> max x1 x2 <= max y1 y2
Proof
    RW_TAC std_ss [max_le]
 >> RW_TAC std_ss [le_max]
QED

(* cf. REAL_LT_MAX *)
Theorem lt_max :
    !x y z :extreal. x < max y z <=> x < y \/ x < z
Proof
    rw [extreal_lt_def]
 >> METIS_TAC [max_le]
QED

Theorem max_refl[simp] :
    !x. max x x = x
Proof
    RW_TAC std_ss [extreal_max_def, le_refl]
QED

Theorem max_comm :
    !x y. max x y = max y x
Proof
    RW_TAC std_ss [extreal_max_def]
 >> PROVE_TAC [le_antisym, le_total]
QED

Theorem max_infty[simp] :
    !x. (max x PosInf = PosInf) /\ (max PosInf x = PosInf) /\
        (max NegInf x = x) /\ (max x NegInf = x)
Proof
    RW_TAC std_ss [extreal_max_def, le_infty]
QED

Theorem max_reduce :
    !x y :extreal. x <= y \/ x < y ==> (max x y = y) /\ (max y x = y)
Proof
    PROVE_TAC [lt_imp_le, extreal_max_def, max_comm]
QED

Theorem min_reduce :
    !x y :extreal. x <= y \/ x < y ==> (min x y = x) /\ (min y x = x)
Proof
    PROVE_TAC [lt_imp_le, extreal_min_def, min_comm]
QED

Theorem lt_max_between :
    !x b d. x < max b d /\ b <= x ==> x < d
Proof
    RW_TAC std_ss [extreal_max_def]
 >> fs [GSYM extreal_lt_def]
 >> PROVE_TAC [let_antisym]
QED

Theorem min_le_between :
    !x a c. min a c <= x /\ x < a ==> c <= x
Proof
    RW_TAC std_ss [extreal_min_def]
 >> PROVE_TAC [let_antisym]
QED

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

(* ------------------------------------------------------------------------- *)
(*    Completeness of Extended Real Numbers                                  *)
(* ------------------------------------------------------------------------- *)

(* This is proved by REAL_MEAN, SIMP_REAL_ARCH and SIMP_REAL_ARCH_NEG *)
Theorem extreal_mean :
    !x y :extreal. x < y ==> ?z. x < z /\ z < y
Proof
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
 >> Q.EXISTS_TAC `Normal z` >> art [extreal_lt_eq]
QED

Theorem EXTREAL_ARCH :
    !x. 0 < x ==> !y. y <> PosInf ==> ?n. y < &n * x
Proof
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
      RW_TAC real_ss [extreal_lt_eq, REAL_LE_MUL, extreal_of_num_def, extreal_mul_def] ]
QED

Theorem SIMP_EXTREAL_ARCH :
    !x. x <> PosInf ==> ?n. x <= &n
Proof
    Cases
 >> RW_TAC std_ss [le_infty]
 >> `?n. r <= &n` by RW_TAC std_ss [SIMP_REAL_ARCH]
 >> Q.EXISTS_TAC `n`
 >> RW_TAC real_ss [extreal_of_num_def,extreal_le_def]
QED

Theorem SIMP_EXTREAL_ARCH_NEG :
    !x. x <> NegInf ==> ?n. - &n <= x
Proof
    Cases
 >> RW_TAC std_ss [le_infty]
 >> `?n. - &n <= r` by RW_TAC std_ss [SIMP_REAL_ARCH_NEG]
 >> Q.EXISTS_TAC `n`
 >> RW_TAC real_ss [extreal_of_num_def, extreal_le_eq, extreal_ainv_def]
QED

Theorem EXTREAL_ARCH_INV :
    !(x :extreal). 0 < x ==> ?n. inv (&SUC n) < x
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x = PosInf’
 >- (Q.EXISTS_TAC ‘0’ >> rw [inv_one, lt_infty])
 >> ‘x <> 0’ by PROVE_TAC [lt_imp_ne]
 >> Know ‘?n. inv x <= &n’
 >- (MATCH_MP_TAC SIMP_EXTREAL_ARCH \\
     METIS_TAC [inv_not_infty])
 >> STRIP_TAC
 >> ‘&n < &SUC n’ by rw [extreal_of_num_def, extreal_lt_eq]
 >> ‘inv x < &SUC n’ by PROVE_TAC [let_trans]
 >> Q.EXISTS_TAC ‘n’
 >> Know ‘x = inv (inv x)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC inv_inv >> art [] \\
     rw [lt_infty] \\
     MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘0’ >> art [] \\
     rw [extreal_of_num_def, lt_infty])
 >> Rewr'
 >> Suff ‘inv (&SUC n) < inv (inv x) <=> inv x < &SUC n’ >- rw []
 >> MATCH_MP_TAC inv_lt_antimono
 >> CONJ_TAC >- rw [extreal_of_num_def, extreal_lt_eq]
 >> MATCH_MP_TAC inv_pos' >> rw []
QED

Theorem EXTREAL_ARCH_INV' :
    !(x :extreal). 0 < x ==> ?n. inv (&SUC n) <= x
Proof
    rpt STRIP_TAC
 >> ‘?n. inv (&SUC n) < x’ by METIS_TAC [EXTREAL_ARCH_INV]
 >> Q.EXISTS_TAC ‘n’
 >> MATCH_MP_TAC lt_imp_le >> art []
QED

val _ = export_theory();
