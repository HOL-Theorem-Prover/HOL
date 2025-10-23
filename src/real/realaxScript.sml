(*===========================================================================*)
(* Construct reals from positive reals                                       *)
(*===========================================================================*)
Theory realax
Ancestors
  pair arithmetic num normalizer prim_rec hreal
Libs
  numLib reduceLib pairLib jrhUtils mesonLib tautLib
  realPP[qualified]


val _ = ParseExtras.temp_loose_equality()

val TAUT_CONV = jrhUtils.TAUT_CONV; (* conflict with tautLib.TAUT_CONV *)
val TAUT      = tautLib.TAUT_CONV;  (* conflict with tautLib.TAUT *)
val GEN_ALL   = hol88Lib.GEN_ALL;   (* it has old reverted variable order *)

(*---------------------------------------------------------------------------*)
(* Now define the functions over the equivalence classes                     *)
(*---------------------------------------------------------------------------*)

val [REAL_10, REAL_ADD_SYM, REAL_MUL_SYM, REAL_ADD_ASSOC,
     REAL_MUL_ASSOC, REAL_LDISTRIB, REAL_ADD_LID, REAL_MUL_LID,
     REAL_ADD_LINV, REAL_MUL_LINV, REAL_LT_TOTAL, REAL_LT_REFL,
     REAL_LT_TRANS, REAL_LT_IADD, REAL_LT_MUL, REAL_BIJ, REAL_ISO,
     REAL_INV_0] =
 let fun mk_def (d,t,n,f) = {def_name=d, fixity=f, fname=n, func=t}
 in
  quotient.define_equivalence_type
   {name = "real",
    equiv = TREAL_EQ_EQUIV,
    defs = [mk_def("real_0",   “treal_0”,   "real_0",    NONE),
            mk_def("real_1",   “treal_1”,   "real_1",    NONE),
            mk_def("real_neg", “treal_neg”, "real_neg",  NONE),
            mk_def("real_inv", “treal_inv”, "inv",       NONE),
            mk_def("real_add", “$treal_add”, "real_add", SOME(Infixl 500)),
            mk_def("real_mul", “$treal_mul”, "real_mul", SOME(Infixl 600)),
            mk_def("real_lt",  “$treal_lt”,  "real_lt",  NONE),
            mk_def("real_of_hreal", “$treal_of_hreal”, "real_of_hreal", NONE),
            mk_def("hreal_of_real", “$hreal_of_treal”, "hreal_of_real", NONE)],
    welldefs = [TREAL_NEG_WELLDEF, TREAL_INV_WELLDEF, TREAL_LT_WELLDEF,
                TREAL_ADD_WELLDEF, TREAL_MUL_WELLDEF, TREAL_BIJ_WELLDEF],
    old_thms = ([TREAL_10]
                @ (map (GEN_ALL o MATCH_MP TREAL_EQ_AP o SPEC_ALL)
                       [TREAL_ADD_SYM, TREAL_MUL_SYM, TREAL_ADD_ASSOC,
                        TREAL_MUL_ASSOC, TREAL_LDISTRIB])
                @ [TREAL_ADD_LID, TREAL_MUL_LID, TREAL_ADD_LINV,
                   TREAL_MUL_LINV, TREAL_LT_TOTAL, TREAL_LT_REFL,
                   TREAL_LT_TRANS, TREAL_LT_ADD, TREAL_LT_MUL, TREAL_BIJ,
                   TREAL_ISO, TREAL_INV_0])}
 end;

(* Export all 18 primitive theorems in total, without any changes (yet) *)
Theorem REAL_10 = REAL_10;
Theorem REAL_ADD_SYM = REAL_ADD_SYM;
Theorem REAL_MUL_SYM = REAL_MUL_SYM;
Theorem REAL_ADD_ASSOC = REAL_ADD_ASSOC;
Theorem REAL_MUL_ASSOC = REAL_MUL_ASSOC;
Theorem REAL_LDISTRIB = REAL_LDISTRIB;
Theorem REAL_ADD_LID = REAL_ADD_LID;
Theorem REAL_MUL_LID = REAL_MUL_LID;
Theorem REAL_ADD_LINV = REAL_ADD_LINV;
Theorem REAL_MUL_LINV = REAL_MUL_LINV;
Theorem REAL_LT_TOTAL = REAL_LT_TOTAL;
Theorem REAL_LT_REFL = REAL_LT_REFL;
Theorem REAL_LT_TRANS = REAL_LT_TRANS;
Theorem REAL_LT_IADD = REAL_LT_IADD;
Theorem REAL_LT_MUL = REAL_LT_MUL;
Theorem REAL_BIJ = REAL_BIJ;
Theorem REAL_ISO = REAL_ISO;
Theorem REAL_INV_0 = REAL_INV_0;

(*---------------------------------------------------------------------------
       Overload arithmetic operations.
 ---------------------------------------------------------------------------*)

val _ =
   add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
              fixity = Suffix 2100,
              paren_style = OnlyIfNecessary,
              pp_elements = [TOK (UnicodeChars.sup_minus ^ UnicodeChars.sup_1)],
              term_name = "realinv"};

Overload realinv = “inv”

val _ = TeX_notation {hol = "realinv", TeX = ("\\HOLTokenInverse{}", 1)};
val _ = TeX_notation {hol = (UnicodeChars.sup_minus ^ UnicodeChars.sup_1),
                      TeX = ("\\HOLTokenInverse{}", 1)};

val natplus  = Term`$+`;
val natless  = Term`$<`;
val bool_not = “$~ : bool -> bool”
val natmult  = Term`$*`;

Overload "+" = natplus
Overload "*" = natmult
Overload "<" = natless

Overload "~" = “$real_neg”
Overload "~" = bool_not
Overload "¬" = bool_not
Overload "numeric_negate" = “$real_neg”

Overload "+" = Term`$real_add`
Overload "*" = Term`$real_mul`
Overload "<" = Term`real_lt`

(*---------------------------------------------------------------------------*)
(* Transfer of supremum property for all-positive sets - bit painful         *)
(*---------------------------------------------------------------------------*)

Theorem REAL_ISO_EQ:
   !h i. h hreal_lt i = real_of_hreal h < real_of_hreal i
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC REAL_ISO,
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [“h:hreal”, “i:hreal”] HREAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_ISO th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
    REWRITE_TAC[REAL_LT_REFL]]
QED

(* cf. the other REAL_POS exported below *)
Theorem REAL_POS[local]:
   !X. real_0 < real_of_hreal X
Proof
  GEN_TAC THEN REWRITE_TAC[REAL_BIJ]
QED

Theorem SUP_ALLPOS_LEMMA1[local]:  (* no need to export *)
   !P y. (!x. P x ==> real_0 < x) ==>
            ((?x. P x /\ y < x) =
            (?X. P(real_of_hreal X) /\ y < (real_of_hreal X)))
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN “x:real” (fn th => MP_TAC th THEN POP_ASSUM
     (SUBST1_TAC o SYM o REWRITE_RULE[REAL_BIJ] o C MATCH_MP (CONJUNCT1 th))))
    THEN DISCH_TAC THEN EXISTS_TAC “hreal_of_real x” THEN ASM_REWRITE_TAC[],
    DISCH_THEN(X_CHOOSE_THEN “X:hreal” ASSUME_TAC) THEN
    EXISTS_TAC “real_of_hreal X” THEN ASM_REWRITE_TAC[]]
QED

Theorem SUP_ALLPOS_LEMMA2[local]:  (* no need to export *)
   !P X. P(real_of_hreal X) :bool = (\h. P(real_of_hreal h)) X
Proof
  REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC
QED

Theorem SUP_ALLPOS_LEMMA3[local]:  (* no need to export *)
   !P. (!x. P x ==> real_0 < x) /\
          (?x. P x) /\
          (?z. !x. P x ==> x < z)
           ==> (?X. (\h. P(real_of_hreal h)) X) /\
               (?Y. !X. (\h. P(real_of_hreal h)) X ==> X hreal_lt Y)
Proof
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [EXISTS_TAC “hreal_of_real x” THEN BETA_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o REWRITE_RULE[REAL_BIJ] o
                C MATCH_MP (ASSUME “(P:real->bool) x”)) THEN
    FIRST_ASSUM ACCEPT_TAC,
    EXISTS_TAC “hreal_of_real z” THEN BETA_TAC THEN GEN_TAC THEN
    UNDISCH_TAC “(P:real->bool) x” THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(fn th => EVERY_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[REAL_ISO_EQ] THEN
    MP_TAC(SPECL[“real_0”, “real_of_hreal X”, “z:real”] REAL_LT_TRANS) THEN
    ASM_REWRITE_TAC[REAL_BIJ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_ASSUM ACCEPT_TAC]
QED

Theorem SUP_ALLPOS_LEMMA4[local]:  (* no need to export *)
   !y. ~(real_0 < y) ==> !x. y < (real_of_hreal x)
Proof
  GEN_TAC THEN DISCH_THEN(curry op THEN GEN_TAC o MP_TAC) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [“y:real”, “real_0”] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN DISCH_THEN(K ALL_TAC) THEN
  POP_ASSUM(MP_TAC o C CONJ (SPEC “x:hreal” REAL_POS)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
QED

Theorem REAL_SUP_ALLPOS:
   !P. (!x. P x ==> real_0 < x) /\ (?x. P x) /\ (?z. !x. P x ==> x < z)
    ==> (?s. !y. (?x. P x /\ y < x) = y < s)
Proof
  let val lemma = TAUT_CONV “a /\ b ==> (a = b)” in
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC “real_of_hreal(hreal_sup(\h. P(real_of_hreal h)))” THEN
  GEN_TAC THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUP_ALLPOS_LEMMA1(CONJUNCT1 th)]) THEN
  ASM_CASES_TAC “real_0 < y” THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[REAL_BIJ]) THEN
    REWRITE_TAC[GSYM REAL_ISO_EQ] THEN
    GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
                    [SUP_ALLPOS_LEMMA2] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HREAL_SUP o MATCH_MP SUP_ALLPOS_LEMMA3)
    THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC lemma THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP SUP_ALLPOS_LEMMA3) THEN
      BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC “X:hreal” o CONJUNCT1) THEN
      EXISTS_TAC “X:hreal” THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SUP_ALLPOS_LEMMA4)] end
QED

(*---------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism &:num->real. (was in realTheory)    *)
(*---------------------------------------------------------------------------*)

Definition real_of_num[nocompute]:
  (real_of_num 0 = real_0) /\
  (real_of_num(SUC n) = real_of_num n + real_1)
End

val _ = add_numeral_form(#"r", SOME "real_of_num");

Theorem REAL_0:
   real_0 = &0
Proof
  REWRITE_TAC[real_of_num]
QED

Theorem REAL_1:
   real_1 = &1
Proof
  REWRITE_TAC[num_CONV “1:num”, real_of_num, REAL_ADD_LID]
QED

(* NOTE: Only theorems involving ‘real_0’ and ‘real_1’ need to be re-educated.
   A "prime" is added into some exported names to make sure that the original
   theorems are still accessible.
 *)
local val reeducate = REWRITE_RULE[REAL_0, REAL_1] in
Theorem REAL_10' = reeducate(REAL_10)
Theorem REAL_ADD_LID' = reeducate(REAL_ADD_LID)
Theorem REAL_ADD_LINV' = reeducate(REAL_ADD_LINV)
Theorem REAL_INV_0' = reeducate(REAL_INV_0)
Theorem REAL_LT_MUL' = reeducate(REAL_LT_MUL)
Theorem REAL_MUL_LID' = reeducate(REAL_MUL_LID)
Theorem REAL_MUL_LINV' = reeducate(REAL_MUL_LINV)
Theorem REAL_SUP_ALLPOS' = reeducate(REAL_SUP_ALLPOS);
end;

(*---------------------------------------------------------------------------*)
(* Define subtraction, division and the other orderings (was in realTheory)  *)
(*---------------------------------------------------------------------------*)

Definition real_sub[nocompute]: real_sub x y = x + ~y
End
Definition real_lte[nocompute]: real_lte x y = ~(y < x)
End
Definition real_gt[nocompute]:  real_gt x y = y < x
End
Definition real_ge[nocompute]:  real_ge x y = (real_lte y x)
End

Definition real_div[nocompute]: $/ x y = x * inv y
End
val _ = set_fixity "/" (Infixl 600);
val _ = overload_on(GrammarSpecials.decimal_fraction_special, “$/”);
Overload "/" = “$/”

val _ = add_ML_dependency "realPP"
val _ = add_user_printer ("real.decimalfractions",
                          “&(NUMERAL x) : real / &(NUMERAL y)”);

Overload "-" = “$-”(* natsub *)
Overload "<=" = “$<=”(* natlte *)
Overload ">" = “$>”(* natgt *)
Overload ">=" = “$>=”(* natge *)

Overload "-" = “$real_sub”
Overload "<=" = “$real_lte”
Overload ">" = “$real_gt”
Overload ">=" = “$real_ge”

Definition real_abs[nocompute]: abs(x) = (if (0 <= x) then x else ~x)
End

Definition real_pow[nocompute]:
  ($pow x 0 = &1) /\ ($pow x (SUC n) = x * ($pow x n))
End
val _ = set_fixity "pow" (Infixr 700);

Definition real_max[nocompute]: max (x :real) y = if x <= y then y else x
End

Definition real_min[nocompute]: min (x :real) y = if x <= y then x else y
End

(* |- !y x. x < y <=> ~(y <= x) *)
Theorem real_lt[allow_rebind]:
  !y x. x < y <=> ~(y <= x)
Proof
  let
    val th1 = TAUT_PROVE (“!t u:bool. (t = ~u) ==> (u = ~t)”)
    val th2 = SPECL [``y <= x``,``x < y``] th1
    val th3 = SPECL [``y:real``,``x:real``] real_lte
  in
    ACCEPT_TAC (GENL [``y:real``, ``x:real``] (MP th2 th3))
  end
QED

(* Floor and ceiling (nums) *)
Definition NUM_FLOOR_def[nocompute] :
   NUM_FLOOR (x:real) = LEAST (n:num). real_of_num (n+1) > x
End

Definition NUM_CEILING_def[nocompute] :
   NUM_CEILING (x:real) = LEAST (n:num). x <= real_of_num n
End

Overload flr = “NUM_FLOOR”
Overload clg = “NUM_CEILING”

(* ------------------------------------------------------------------------- *)
(* Some elementary "bootstrapping" lemmas needed by RealArith.sml            *)
(*                                                                           *)
(* NOTE: The following theorems were from HOL-Light's calc_int.sml, line 66  *)
(* afterwards. The precise order of theorems are preserved, which is a bit   *)
(* different with their orders when they were also in realTheory. Thus, as   *)
(* a result, some of their proofs are directly ported from HOL-Light, which  *)
(* uses a lot of MESON_TAC instead of manual proof steps.      -- Chun Tian  *)
(*                                                                           *)
(* NOTE2: any updates here must be also put in "prove_real_assumsScript.sml" *)
(* ------------------------------------------------------------------------- *)

(* HOL-Light compatible (Don't add quantifiers!), was in iterateTheory

   NOTE: This theorem is not very useful in HOL4, because whenever in proofs
         from HOL-Light one has something like this:

      AC REAL_ADD_AC `(a + b) + (c + d) = (a + c) + (b + d)`

   In HOL4, we must change it to the following code instead:

      jrhUtils.AC (REAL_ADD_ASSOC,REAL_ADD_SYM)
         “(a + b) + (c + d) = (a + c) + (b + d):real”

   NOTE2: in the follow scripts (until the end of this file), all terms “&n”
          must be written as “real_of_num n”, while literals “&0” and “&1”
          must be written as “0r” and “1r”. This is because these code has
          a copy in "prove_real_assumsScript.sml" where “real_of_num” is
          interpreted differently.
 *)
Theorem REAL_ADD_AC :
   (m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))
Proof
  MESON_TAC[REAL_ADD_ASSOC, REAL_ADD_SYM]
QED

Theorem REAL_MUL_AC :
   (m * n = n * m) /\
   ((m * n) * p = m * (n * p)) /\
   (m * (n * p) = n * (m * p))
Proof
  MESON_TAC[REAL_MUL_ASSOC, REAL_MUL_SYM]
QED

Theorem REAL_ADD_RINV:
   !x:real. x + ~x = 0r
Proof
  MESON_TAC[REAL_ADD_SYM, REAL_ADD_LINV']
QED

(* HOL-Light compatible *)
Theorem REAL_EQ_ADD_LCANCEL:
   !x y z. (x + y = x + z) <=> (y = z)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM “$+ ~x”) THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV', REAL_ADD_LID']
QED

(* HOL-Light compatible *)
Theorem REAL_EQ_ADD_RCANCEL:
   !x y z. (x + z = y + z) <=> (x = y)
Proof
  MESON_TAC[REAL_ADD_SYM, REAL_EQ_ADD_LCANCEL]
QED

(* HOL-Light compatible name
   |- !x y z. x * (y + z) = x * y + x * z
 *)
Theorem REAL_ADD_LDISTRIB = REAL_LDISTRIB

Theorem REAL_RDISTRIB:
   !x y z. (x + y) * z = (x * z) + (y * z)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LDISTRIB
QED

(* HOL-Light compatible name of the above theorem *)
Theorem REAL_ADD_RDISTRIB = REAL_RDISTRIB

Theorem REAL_MUL_RZERO:
   !x. x * 0r = 0r
Proof
  MESON_TAC[REAL_EQ_ADD_RCANCEL, REAL_ADD_LDISTRIB, REAL_ADD_LID']
QED

Theorem REAL_MUL_LZERO:
   !x. 0r * x = 0r
Proof
  MESON_TAC[REAL_MUL_SYM, REAL_MUL_RZERO]
QED

Theorem REAL_NEG_NEG:
   !x:real. ~~x = x
Proof
  MESON_TAC
   [REAL_EQ_ADD_RCANCEL, REAL_ADD_LINV', REAL_ADD_SYM, REAL_ADD_LINV']
QED

Theorem REAL_MUL_RNEG:
   !x y. x * ~y = ~(x * y)
Proof
  MESON_TAC[REAL_EQ_ADD_RCANCEL, REAL_ADD_LDISTRIB, REAL_ADD_LINV',
            REAL_MUL_RZERO]
QED

Theorem REAL_MUL_LNEG:
    !x y. ~x * y = ~(x * y)
Proof
  MESON_TAC[REAL_MUL_SYM, REAL_MUL_RNEG]
QED

Theorem REAL_NEG_ADD:
   !x y. ~(x + y) = ~x + ~y
Proof
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL REAL_EQ_ADD_RCANCEL)))) THEN
  Q.EXISTS_TAC `x + y` THEN REWRITE_TAC[REAL_ADD_LINV'] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    “(a + b) + (c + d) = (a + c) + (b + d):real”] THEN
  REWRITE_TAC[REAL_ADD_LINV', REAL_ADD_LID']
QED

Theorem REAL_ADD_RID:
   !x. x + 0r = x
Proof MESON_TAC[REAL_ADD_SYM, REAL_ADD_LID']
QED

Theorem REAL_NEG_0:
   ~0r = 0r
Proof MESON_TAC[REAL_ADD_LINV', REAL_ADD_RID]
QED

(* NOTE: REAL_LE_LADD_IMP (and many others below) is primative in HOL Light, i.e.
   directly come from the quotient process, but in HOL4 it must be derived from
   other primitives.
 *)
Theorem REAL_LT_LADD:
   !x y z. (x + y) < (x + z) <=> y < z
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o Q.SPEC ‘~x’ o MATCH_MP REAL_LT_IADD) THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV', REAL_ADD_LID'],
    MATCH_ACCEPT_TAC REAL_LT_IADD]
QED

(* HOL-Light compatible name *)
Theorem REAL_LT_LADD_IMP = REAL_LT_IADD

Theorem REAL_LE_LADD:
   !x y z. (x + y) <= (x + z) <=> y <= z
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LADD
QED

(* |- !x y z. y <= z ==> x + y <= x + z *)
Theorem REAL_LE_LADD_IMP = (
  let
    val th1 = GSYM (SPEC_ALL REAL_LE_LADD)
    val th2 = TAUT_PROVE ``(x:bool = y) ==> (x ==> y)``
  in
    Q.GENL [‘x’, ‘y’, ‘z’] (MATCH_MP th2 th1)
  end)

Theorem REAL_LE_LNEG:
  !x y. ~x <= y <=> 0r <= x + y
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THENL
   [DISCH_THEN(MP_TAC o Q.SPEC `x:real`) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LINV'],
    DISCH_THEN(MP_TAC o Q.SPEC `~x`) THEN
    REWRITE_TAC[REAL_ADD_LINV', REAL_ADD_ASSOC, REAL_ADD_LID',
        ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID']]
QED

Theorem REAL_LE_NEG2:
   !x y. ~x <= ~y <=> y <= x
Proof
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) empty_rewrites [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_ADD_SYM
QED

Theorem REAL_LE_RNEG:
    !x y. x <= ~y <=> x + y <= 0r
Proof
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG, GSYM REAL_NEG_ADD] THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_LE_NEG2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_LINV'] THEN
  REWRITE_TAC[REAL_NEG_ADD, REAL_NEG_NEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM
QED

Theorem REAL:
   !n. real_of_num (SUC n) = real_of_num n + 1r
Proof
  GEN_TAC THEN REWRITE_TAC[real_of_num] THEN
  REWRITE_TAC[REAL_1]
QED

Theorem REAL_ADD:
   !m n. real_of_num m + real_of_num n = real_of_num(m + n)
Proof
  INDUCT_TAC THEN REWRITE_TAC[REAL, ADD, REAL_ADD_LID'] THEN
  RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM))
QED

(* HOL-Light compatible name of the above theorem *)
Theorem REAL_OF_NUM_ADD = REAL_ADD;

Theorem REAL_OF_NUM_SUB:
  !m n. m <= n ==> (&(n-m):real = &n - &m)
Proof
  rw[] >> ‘?d. n=m+d’ by (irule LESS_EQUAL_ADD >> simp[])
  >> simp[SUB_RIGHT_EQ]
  >> once_rewrite_tac[GSYM REAL_ADD]
  >> simp[REAL_ADD_RINV, bossLib.AC REAL_ADD_ASSOC REAL_ADD_SYM,
          real_sub, REAL_ADD_LID']
QED

Theorem REAL_MUL:
   !m n. real_of_num m * real_of_num n = real_of_num(m * n)
Proof
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, MULT_CLAUSES, REAL,
    GSYM REAL_ADD, REAL_RDISTRIB] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[REAL_MUL_LID']
QED

(* HOL-Light compatible name of the above theorem *)
Theorem REAL_OF_NUM_MUL = REAL_MUL;

Theorem REAL_OF_NUM_POW :
    !x n. (real_of_num x) pow n = real_of_num(x EXP n)
Proof
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow, EXP, REAL_OF_NUM_MUL]
QED

(* NOTE: realTheory.REAL_POW_NEG has different statements! *)
Theorem REAL_POW_NEG :
   !x n. (~x) pow n = if EVEN n then x pow n else ~(x pow n)
Proof
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[real_pow, EVEN] THEN
  ASM_CASES_TAC “EVEN n” THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_NEG_NEG]
QED

Theorem REAL_NOT_LE:
   !x y. ~(x <= y) <=> y < x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte]
QED

Theorem REAL_LT_ADDR:
  !x y. x < x + y <=> 0r < y
Proof
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [“x:real”, “0r”, “y:real”] REAL_LT_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]
QED

Theorem REAL_LT_ANTISYM:
   !x y. ~(x < y /\ y < x)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
  REWRITE_TAC[REAL_LT_REFL]
QED

Theorem REAL_LT_GT:
   !x y. x < y ==> ~(y < x)
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
  REWRITE_TAC[REAL_LT_ANTISYM]
QED

Theorem REAL_LE_LT:
   !x y. x <= y <=> x < y \/ (x = y)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [“x:real”, “y:real”] REAL_LT_TOTAL) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(DISJ_CASES_THEN2
     (curry op THEN (MATCH_MP_TAC REAL_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC REAL_LT_REFL]
QED

Theorem REAL_LT_LE:
   !x y. x < y <=> x <= y /\ ~(x = y)
Proof
  let val lemma = TAUT_CONV “~(a /\ ~a)” in
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR, lemma]
  THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL] end
QED

Theorem REAL_LT_IMP_LE:
   !x y. x < y ==> x <= y
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_LT]
QED

Theorem REAL_LET_TRANS:
   !x y z. x <= y /\ y < z ==> x < z
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
    (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC))
QED

Theorem REAL_LE_TRANS:
   !x y z. x <= y /\ y <= z ==> x <= z
Proof
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
  THEN REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME “y < z”)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_IMP_LE o MATCH_MP REAL_LET_TRANS)
QED

Theorem REAL_LE_MUL:
   !x y. 0r <= x /\ 0r <= y ==> 0r <= (x * y)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  MAP_EVERY ASM_CASES_TAC [“0r = x”, “0r = y”] THEN
  ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL' THEN
  ASM_REWRITE_TAC[]
QED

Theorem REAL_LT_RADD:
   !x y z. (x + z) < (y + z) <=> x < y
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LADD
QED

Theorem REAL_LE_RADD:
   !x y z. (x + z) <= (y + z) <=> x <= y
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_RADD
QED

Theorem REAL_NEG_LT0 :
  !x. ~x < 0r <=> 0r < x
Proof
  GEN_TAC THEN
  SUBST1_TAC(SYM(Q.SPECL [‘~x’, ‘0r’, ‘x’] REAL_LT_RADD))
  THEN REWRITE_TAC[REAL_ADD_LINV', REAL_ADD_LID']
QED

Theorem REAL_LT_NEGTOTAL:
  !x. (x = 0r) \/ 0r < x \/ 0r < -x
Proof
  GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (Q.SPECL [‘x’, ‘0r’] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[SYM(REWRITE_RULE[REAL_NEG_NEG] (Q.SPEC ‘~x’ REAL_NEG_LT0))]
QED

Theorem REAL_LE_NEGTOTAL :
  !x. 0r <= x \/ 0r <= ~x
Proof
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
          (SPEC “x:real” REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[]
QED

Theorem REAL_LNEG_UNIQ:
   !x y. (x + y = 0r) <=> (x = ~y)
Proof
  REPEAT GEN_TAC THEN SUBST1_TAC (SYM(SPEC “y:real” REAL_ADD_LINV')) THEN
  MATCH_ACCEPT_TAC REAL_EQ_ADD_RCANCEL
QED

Theorem REAL_RNEG_UNIQ:
   !x y. (x + y = 0r) <=> (y = ~x)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LNEG_UNIQ
QED

Theorem REAL_NEG_LMUL:
   !x y. ~(x * y) = ~x * y
Proof
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ, GSYM REAL_RDISTRIB,
              REAL_ADD_LINV', REAL_MUL_LZERO]
QED

Theorem REAL_NEG_RMUL:
   !x y. ~(x * y) = x * ~y
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_NEG_LMUL
QED

Theorem REAL_LE_SQUARE:
   !x. 0r <= x * x
Proof
  GEN_TAC THEN DISJ_CASES_TAC (SPEC “x:real” REAL_LE_NEGTOTAL) THEN
  POP_ASSUM(MP_TAC o MATCH_MP REAL_LE_MUL o W CONJ) THEN
  REWRITE_TAC[GSYM REAL_NEG_RMUL, GSYM REAL_NEG_LMUL, REAL_NEG_NEG]
QED

Theorem REAL_LE_01:
    0r <= 1r
Proof
  SUBST1_TAC(SYM(SPEC “1r” REAL_MUL_LID')) THEN
  MATCH_ACCEPT_TAC REAL_LE_SQUARE
QED

Theorem REAL_LT_01:
    0r < 1r
Proof
  REWRITE_TAC[REAL_LT_LE, REAL_LE_01] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_10']
QED

Theorem REAL_LE_ADDR :
  !x y. x <= x + y <=> 0r <= y
Proof
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [“x:real”, “0r”, “y:real”] REAL_LE_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]
QED

Theorem REAL_LE_REFL:
   !x. x <= x
Proof
  GEN_TAC THEN REWRITE_TAC[real_lte, REAL_LT_REFL]
QED

(* NOTE: previous the other REAL_POS above was exported in realaxTheory *)
Theorem REAL_POS:
   !n. 0r <= real_of_num n
Proof
  INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC “real_of_num n” THEN ASM_REWRITE_TAC[REAL] THEN
  REWRITE_TAC[REAL_LE_ADDR, REAL_LE_01]
QED

Theorem REAL_LE:
   !m n. real_of_num m <= real_of_num n <=> m <= n
Proof
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
   [REAL, REAL_LE_RADD, ZERO_LESS_EQ, LESS_EQ_MONO, REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM NOT_LESS, LESS_0] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “real_of_num n” THEN
    ASM_REWRITE_TAC[ZERO_LESS_EQ, REAL_LE_ADDR, REAL_LE_01],
    DISCH_THEN(MP_TAC o C CONJ (SPEC “m:num” REAL_POS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
    REWRITE_TAC[REAL_NOT_LE, REAL_LT_ADDR, REAL_LT_01]]
QED

(* HOL-Light compatible name of the above theorem *)
Theorem REAL_OF_NUM_LE = REAL_LE;

(* |- !n. 0 <= n *)
val LE_0 = ZERO_LESS_EQ; (* arithmeticTheory *)

Theorem REAL_ABS_NUM :
   !n. abs(real_of_num n) = real_of_num n
Proof
  REWRITE_TAC[real_abs, REAL_OF_NUM_LE, LE_0]
QED

Theorem REAL_LTE_TOTAL:
   !x y. x < y \/ y <= x
Proof
  REWRITE_TAC[real_lt] THEN CONV_TAC TAUT
QED

Theorem REAL_LET_TOTAL:
   !x y. x <= y \/ y < x
Proof
  REWRITE_TAC[real_lt] THEN CONV_TAC TAUT
QED

Theorem REAL_LTE_TRANS:
   !x y z. x < y /\ y <= z ==> x < z
Proof
  MESON_TAC[real_lt, REAL_LE_TRANS]
QED

Theorem REAL_LE_ADD:
   !x y. 0r <= x /\ 0r <= y ==> 0r <= (x + y)
Proof
  MESON_TAC[REAL_LE_LADD_IMP, REAL_ADD_RID, REAL_LE_TRANS]
QED

Theorem REAL_LTE_ANTISYM:
   !x y. ~(x <= y /\ y < x)
Proof
  MESON_TAC[real_lt]
QED

Theorem REAL_SUB_LE:
   !x y. 0r <= (x - y) <=> y <= x
Proof
  REWRITE_TAC[real_sub, GSYM REAL_LE_LNEG, REAL_LE_NEG2]
QED

Theorem REAL_NEG_SUB:
   !x y. ~(x - y) = y - x
Proof
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEG_NEG] THEN
  REWRITE_TAC[Once REAL_ADD_AC]
QED

Theorem REAL_SUB_LT:
   !x y. 0r < x - y <=> y < x
Proof
  REWRITE_TAC[real_lt] THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[REAL_LE_LNEG, REAL_ADD_RID, REAL_SUB_LE]
QED

Theorem REAL_LE_ANTISYM:
   !x y. x <= y /\ y <= x <=> (x = y)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[real_lte] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (SPECL [“x:real”, “y:real”] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]]
QED

Theorem REAL_NOT_LT:
   !x y. ~(x < y) <=> y <= x
Proof
  REWRITE_TAC[real_lte]
QED

Theorem REAL_SUB_0:
   !x y. (x - y = 0r) <=> (x = y)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites
                  [GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_SUB_LE, REAL_SUB_LT] THEN REWRITE_TAC[REAL_NOT_LT]
QED

Theorem REAL_LTE_ADD:
   !x y. 0r < x /\ 0r <= y ==> 0r < (x + y)
Proof
  MESON_TAC[REAL_LE_LADD_IMP, REAL_ADD_RID, REAL_LTE_TRANS]
QED

Theorem REAL_LET_ADD:
   !x y. 0r <= x /\ 0r < y ==> 0r < (x + y)
Proof
  MESON_TAC[REAL_LTE_ADD, REAL_ADD_SYM]
QED

Theorem REAL_LT_ADD:
   !x y. 0r < x /\ 0r < y ==> 0r < (x + y)
Proof
  MESON_TAC[REAL_LT_IMP_LE, REAL_LTE_ADD]
QED

Theorem REAL_ENTIRE:
   !x y. (x * y = 0r) <=> (x = 0r) \/ (y = 0r)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC “x = 0r” THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(MATCH_MP REAL_MUL_LINV') THEN
    DISCH_THEN(MP_TAC o AP_TERM “$* (inv x)”) THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC, REAL_MUL_LID', REAL_MUL_RZERO],
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO]]
QED

Theorem REAL_MUL_RID:
   !x. x * 1r = x
Proof
  MESON_TAC[REAL_MUL_LID', REAL_MUL_SYM]
QED

Theorem REAL_POW_2:
   !x. x pow 2 = x * x
Proof
  REWRITE_TAC[num_CONV “2:num”, num_CONV “1:num”] THEN
  REWRITE_TAC[real_pow, REAL_MUL_RID]
QED

(* This actually shows that real numbers and (+,*,0,1) form a semi-ring *)
Triviality REAL_POLY_CLAUSES :
   (!x y z. x + (y + z) = (x + y) + z) /\
   (!x y. x + y = y + x) /\
   (!x. 0r + x = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x y. x * y = y * x) /\
   (!x. 1r * x = x) /\
   (!x. 0r * x = 0r) /\
   (!x y z. x * (y + z) = x * y + x * z) /\
   (!x. x pow 0 = 1r) /\
   (!x n. x pow (SUC n) = x * x pow n)
Proof
  REWRITE_TAC[real_pow, REAL_ADD_LDISTRIB, REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_ASSOC, REAL_ADD_ASSOC, REAL_ADD_LID', REAL_MUL_LID'] THEN
  REWRITE_TAC[Once REAL_ADD_AC] THEN REWRITE_TAC[Once REAL_MUL_SYM]
QED
Theorem REAL_POLY_CLAUSES = MATCH_MP SEMIRING_PTHS REAL_POLY_CLAUSES;

Theorem REAL_POLY_NEG_CLAUSES :
   (!x. ~x = ~(1r) * x) /\
   (!x y. x - y = x + ~(1r) * y)
Proof
  REWRITE_TAC[REAL_MUL_LNEG, real_sub, REAL_MUL_LID']
QED

Theorem REAL_LE_TOTAL:
   !x y. x <= y \/ y <= x
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_lte, GSYM DE_MORGAN_THM, REAL_LT_ANTISYM]
QED

(* NOTE: MESON_TAC (original proof) doesn't work here. METIS_TAC is used *)
Theorem REAL_ABS_NEG :
   !x. abs(~x) = abs x
Proof
  GEN_TAC THEN
  REWRITE_TAC[real_abs, REAL_LE_RNEG, REAL_NEG_NEG, REAL_ADD_LID'] THEN
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_ANTISYM, REAL_NEG_0]
QED

Theorem REAL_LT_NZ:
   !n. ~(real_of_num n = 0r) <=> (0r < real_of_num n)
Proof
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_CASES_TAC “real_of_num n = 0r” THEN
  ASM_REWRITE_TAC[REAL_LE_REFL, REAL_POS]
QED

Theorem REAL_INJ:
   !m n. (real_of_num m = real_of_num n) <=> (m = n)
Proof
  let val th = prove(“(m:num = n) <=> m <= n /\ n <= m”,
                 EQ_TAC THENL
                  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LESS_EQ_REFL],
                   MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[th, GSYM REAL_LE_ANTISYM, REAL_LE] end
QED

(* HOL-Light compatible name *)
Theorem REAL_OF_NUM_EQ = REAL_INJ;

(* This theorem is mainly for RealArith.REAL_LINEAR_PROVER *)
Theorem REAL_POS_LT :
    !n. 0r < real_of_num (SUC n)
Proof
    GEN_TAC
 >> REWRITE_TAC [Q.SPEC ‘SUC n’ (GSYM REAL_LT_NZ), REAL_INJ]
 >> ARITH_TAC
QED

Theorem REAL_INT_LE_CONV_tth[unlisted] = TAUT_PROVE
  “(F /\ F = F) /\ (F /\ T = F) /\ (T /\ F = F) /\ (T /\ T = T)”;
Theorem REAL_INT_LE_CONV_nth[unlisted] = TAUT_PROVE “(~T = F) /\ (~F = T)”;

Theorem REAL_INT_LE_CONV_pth[unlisted]:
  (~(&m) <= &n = T) /\
  (&m <= (&n : real) = m <= n) /\
  (~(&m) <= ~(&n) = n <= m) /\
  (&m <= ~(&n) = (m = 0) /\ (n = 0))
Proof
  REWRITE_TAC[REAL_LE_NEG2]
  >> REWRITE_TAC[REAL_LE_LNEG, REAL_LE_RNEG]
  >> REWRITE_TAC[REAL_ADD, REAL_OF_NUM_LE, LE_0]
  >> REWRITE_TAC[LE, ADD_EQ_0]
QED

Theorem REAL_INT_LT_CONV_pth[unlisted]:
  (&m < ~(&n) = F) /\
  (&m < (&n :real) = m < n) /\
  (~(&m) < ~(&n) = n < m) /\
  (~(&m) < &n = ~((m = 0) /\ (n = 0)))
Proof
  REWRITE_TAC[REAL_INT_LE_CONV_pth, GSYM NOT_LE, real_lt]
  >> CONV_TAC tautLib.TAUT_CONV
QED

Theorem REAL_INT_GE_CONV_pth[unlisted]:
  (&m >= ~(&n) = T) /\
  (&m >= (&n :real) = n <= m) /\
  (~(&m) >= ~(&n) = m <= n) /\
  (~(&m) >= &n = (m = 0) /\ (n = 0))
Proof
  REWRITE_TAC[REAL_INT_LE_CONV_pth, real_ge]
  >> CONV_TAC tautLib.TAUT_CONV
QED

Theorem REAL_INT_GT_CONV_pth[unlisted]:
  (~(&m) > &n = F) /\
  (&m > (&n :real) = n < m) /\
  (~(&m) > ~(&n) = m < n) /\
  (&m > ~(&n) = ~((m = 0) /\ (n = 0)))
Proof
  REWRITE_TAC[REAL_INT_LT_CONV_pth, real_gt]
  >> CONV_TAC tautLib.TAUT_CONV
QED

Theorem REAL_INT_EQ_CONV_pth[unlisted]:
  ((&m = (&n :real)) = (m = n)) /\
  ((~(&m) = ~(&n)) = (m = n)) /\
  ((~(&m) = &n) = (m = 0) /\ (n = 0)) /\
  ((&m = ~(&n)) = (m = 0) /\ (n = 0))
Proof
  REWRITE_TAC[GSYM REAL_LE_ANTISYM, GSYM LE_ANTISYM]
  \\ REWRITE_TAC[REAL_INT_LE_CONV_pth, LE, LE_0]
  \\ CONV_TAC tautLib.TAUT_CONV
QED

Theorem REAL_INT_NEG_CONV_pth[unlisted]:
  (~(&0) = &0) /\ (~(~(&x)) = &x)
Proof
  REWRITE_TAC[REAL_NEG_NEG, REAL_NEG_0]
QED

Theorem REAL_INT_MUL_CONV_pth0[unlisted]:
  (&0 * (&x :real) = &0) /\
  (&0 * ~(&x) = &0) /\
  ((&x :real) * &0 = &0) /\
  (~(&x :real) * &0 = &0)
Proof
  REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO]
QED

Theorem REAL_INT_MUL_CONV_pth1[unlisted]:
  ((&m * &n = &(m * n) :real) /\ (~(&m) * ~(&n) = &(m * n) :real)) /\
  ((~(&m) * &n = ~(&(m * n) :real)) /\ (&m * ~(&n) = ~(&(m * n) :real)))
Proof
  REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG]
  >> REWRITE_TAC[REAL_OF_NUM_MUL]
QED

Theorem REAL_PROD_NORM_CONV_pth1[unlisted] = SYM(SPEC ``x:real`` REAL_MUL_RID)
Theorem REAL_PROD_NORM_CONV_pth2[unlisted] = SYM(SPEC ``x:real`` REAL_MUL_LID')

Theorem REAL_INT_ADD_CONV_pth0[unlisted]:
  (~(&m) + &m = &0) /\ (&m + ~(&m) = &0)
Proof
  REWRITE_TAC[REAL_ADD_LINV', REAL_ADD_RINV]
QED

Theorem REAL_INT_ADD_CONV_pth1[unlisted]:
  (~(&m) + ~(&n :real) = ~(&(m + n))) /\
  (~(&m) + &(m + n) = &n) /\
  (~(&(m + n)) + &m = ~(&n)) /\
  (&(m + n) + ~(&m) = &n) /\
  (&m + ~(&(m + n)) = ~(&n)) /\
  (&m + &n = &(m + n) :real)
Proof
  REWRITE_TAC[GSYM REAL_ADD, REAL_NEG_ADD] THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV', REAL_ADD_LID'] THEN
  REWRITE_TAC[REAL_ADD_RINV, REAL_ADD_LID'] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV', REAL_ADD_LID'] THEN
  REWRITE_TAC[REAL_ADD_RINV, REAL_ADD_LID']
QED

Theorem LINEAR_ADD_pth0a[unlisted]:
  &0 + x = x :real
Proof
  REWRITE_TAC[REAL_ADD_LID']
QED

Theorem LINEAR_ADD_pth0b[unlisted]:
  x + &0 = x :real
Proof
  REWRITE_TAC[REAL_ADD_RID]
QED

Theorem LINEAR_ADD_pth1[unlisted]:
  ((l1 + r1) + (l2 + r2) = (l1 + l2) + (r1 + r2):real) /\
  ((l1 + r1) + tm2 = l1 + (r1 + tm2):real) /\
  (tm1 + (l2 + r2) = l2 + (tm1 + r2)) /\
  ((l1 + r1) + tm2 = (l1 + tm2) + r1) /\
  (tm1 + tm2 = tm2 + tm1) /\
  (tm1 + (l2 + r2) = (tm1 + l2) + r2)
Proof
  REPEAT CONJ_TAC
  THEN REWRITE_TAC[REAL_ADD_ASSOC]
  THEN TRY (MATCH_ACCEPT_TAC REAL_ADD_SYM) THENL
  [REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN AP_TERM_TAC
    THEN ONCE_REWRITE_TAC [REAL_ADD_SYM]
    THEN Ho_Rewrite.GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM]
    THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN AP_TERM_TAC
    THEN MATCH_ACCEPT_TAC REAL_ADD_SYM,
  ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN AP_TERM_TAC
    THEN MATCH_ACCEPT_TAC REAL_ADD_SYM,
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN AP_TERM_TAC
    THEN MATCH_ACCEPT_TAC REAL_ADD_SYM]
QED

Theorem REAL_SUM_NORM_CONV_pth1[unlisted]:
  ~x = ~(&1) * x
Proof
  REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_LID']
QED

Theorem REAL_SUM_NORM_CONV_pth2[unlisted]:
  x - y:real = x + ~(&1) * y
Proof
  REWRITE_TAC[real_sub, GSYM REAL_SUM_NORM_CONV_pth1]
QED

Theorem REAL_NEGATE_CANON_pth1[unlisted]:
  ((a:real <= b = &0 <= X) = (b < a = &0 < ~X)) /\
  ((a:real < b = &0 < X) = (b <= a = &0 <= ~X))
Proof
  REWRITE_TAC[real_lt, REAL_LE_LNEG, REAL_LE_RNEG] THEN
  REWRITE_TAC[REAL_ADD_RID, REAL_ADD_LID'] THEN
  CONV_TAC tautLib.TAUT_CONV
QED

Theorem REAL_NEGATE_CANON_pth2[unlisted]:
  ~((~a) * x + z :real) = a * x + ~z
Proof
  REWRITE_TAC[GSYM REAL_MUL_LNEG, REAL_NEG_ADD, REAL_NEG_NEG]
QED

Theorem REAL_NEGATE_CANON_pth3[unlisted]:
  ~(a * x + z :real) = ~a * x + ~z
Proof
  REWRITE_TAC[REAL_NEG_ADD, GSYM REAL_MUL_LNEG]
QED

Theorem REAL_NEGATE_CANON_pth4[unlisted]:
  ~(~a * x :real) = a * x
Proof
  REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG]
QED

Theorem REAL_NEGATE_CANON_pth5[unlisted]:
  ~(a * x :real) = ~a * x
Proof
  REWRITE_TAC[REAL_MUL_LNEG]
QED

Theorem REAL_ATOM_NORM_CONV_pth2[unlisted]:
  (a:real < b = c < d:real) = (b <= a = d <= c)
Proof
  REWRITE_TAC[real_lt] THEN CONV_TAC tautLib.TAUT_CONV
QED

Theorem REAL_ATOM_NORM_CONV_pth3[unlisted]:
  (a:real <= b = c <= d:real) = (b < a = d < c)
Proof
  REWRITE_TAC[real_lt] THEN CONV_TAC tautLib.TAUT_CONV
QED

Theorem REAL_INT_POW_CONV_pth1[unlisted]:
  (&x pow n = &(x EXP n)) /\
     ((~(&x)) pow n = if EVEN n then &(x EXP n) else ~(&(x EXP n)))
Proof
  REWRITE_TAC[REAL_OF_NUM_POW, REAL_POW_NEG]
QED

Theorem REAL_INT_POW_CONV_tth[unlisted]:
  ((if T then x:real else y) = x) /\ ((if F then x:real else y) = y)
Proof
  REWRITE_TAC[]
QED

Theorem REAL_INT_ABS_CONV_pth[unlisted]:
  (abs(~(&x)) = &x) /\
  (abs(&x) = &x)
Proof
  REWRITE_TAC[REAL_ABS_NEG, REAL_ABS_NUM]
QED

Theorem LINEAR_MULT_pth[unlisted]:
  x * &0 = &0 :real
Proof
  REWRITE_TAC[REAL_MUL_RZERO]
QED

Theorem ADD_INEQS_pth[unlisted]:
  ((&0 = a) /\ (&0 = b) ==> (&0 = a + b :real)) /\
  ((&0 = a) /\ (&0 <= b) ==> (&0 <= a + b :real)) /\
  ((&0 = a) /\ (&0 < b) ==> (&0 < a + b :real)) /\
  ((&0 <= a) /\ (&0 = b) ==> (&0 <= a + b :real)) /\
  ((&0 <= a) /\ (&0 <= b) ==> (&0 <= a + b :real)) /\
  ((&0 <= a) /\ (&0 < b) ==> (&0 < a + b :real)) /\
  ((&0 < a) /\ (&0 = b) ==> (&0 < a + b :real)) /\
  ((&0 < a) /\ (&0 <= b) ==> (&0 < a + b :real)) /\
  ((&0 < a) /\ (&0 < b) ==> (&0 < a + b :real))
Proof
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_ADD_LID', REAL_ADD_RID] THENL
  [MATCH_MP_TAC REAL_LE_TRANS,
  MATCH_MP_TAC REAL_LET_TRANS,
  MATCH_MP_TAC REAL_LTE_TRANS,
  MATCH_MP_TAC REAL_LT_TRANS] THEN
  EXISTS_TAC ``a:real`` THEN ASM_REWRITE_TAC[] THEN
  Ho_Rewrite.GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
    (MATCH_MP_TAC REAL_LE_LADD_IMP ORELSE MATCH_MP_TAC REAL_LT_LADD_IMP)
  THEN ASM_REWRITE_TAC[]
QED

Theorem MULTIPLY_INEQS_pth[unlisted]:
  ((&0 = y) ==> (&0 = x * y :real)) /\
  (&0 <= y ==> &0 <= x ==> &0 <= x * y :real) /\
  (&0 < y ==> &0 < x ==> &0 < x * y :real)
Proof
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THENL
  [MATCH_MP_TAC REAL_LE_MUL,
  MATCH_MP_TAC REAL_LT_MUL'] THEN
  ASM_REWRITE_TAC[]
QED

Theorem REAL_SIMPLE_ARITH_REFUTER_trivthm[unlisted]:
  &0 < &0 :real = F
Proof
  REWRITE_TAC[REAL_LE_REFL, real_lt]
QED

Theorem ZERO_LEFT_CONV_pth[unlisted]:
  ((x = y) = (&0 = y + ~x)) /\
  (x <= y = &0 <= y + ~x) /\
  (x < y = &0 < y + ~x)
Proof
  REWRITE_TAC[real_lt, GSYM REAL_LE_LNEG, REAL_LE_NEG2] THEN
  REWRITE_TAC[GSYM REAL_LE_RNEG, REAL_NEG_NEG] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM, GSYM REAL_LE_LNEG,
              GSYM REAL_LE_RNEG, REAL_LE_NEG2, REAL_NEG_NEG]
QED

Theorem ABS_ELIM_THM[unlisted]:
  (&0 <= ~(abs(x)) + y = &0 <= x + y /\ &0 <= ~x + y) /\
  (&0 < ~(abs(x)) + y = &0 < x + y /\ &0 < ~x + y)
Proof
  REWRITE_TAC[real_abs] THEN COND_CASES_TAC
  THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  REWRITE_TAC [
    TAUT_PROVE ``(a = a /\ b) = (a ==> b)``,
    TAUT_PROVE ``(b = a /\ b) = (b ==> a)``
  ]
  THEN REPEAT STRIP_TAC THEN
  MAP_FIRST MATCH_MP_TAC [REAL_LE_TRANS, REAL_LTE_TRANS] THEN
  FIRST_ASSUM(fn th => EXISTS_TAC(rand(concl th)) THEN
  CONJ_TAC THENL [ACCEPT_TAC th, ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_MP_TAC REAL_LE_LADD_IMP THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ``&0 :real`` THEN
  REWRITE_TAC[REAL_LE_LNEG, REAL_LE_RNEG] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID, REAL_ADD_LID'] THEN
  MP_TAC (SPEC(Term`&0 :real`) (SPEC (Term`x:real`)
          REAL_LE_TOTAL))
  THEN ASM_REWRITE_TAC[]
QED

Theorem ABS_CASES_THM[unlisted]:
  (abs(x) = x) \/ (abs(x) = ~x)
Proof
  REWRITE_TAC[real_abs] THEN COND_CASES_TAC
  THEN REWRITE_TAC[]
QED

Theorem ABS_STRONG_CASES_THM[unlisted]:
  &0 <= x /\ (abs(x) = x) \/ (&0 <= ~x) /\ (abs(x) = ~x)
Proof
  REWRITE_TAC[real_abs] THEN COND_CASES_TAC
  THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LE_RNEG, REAL_ADD_LID'] THEN
  MP_TAC (SPECL [``&0 :real``, ``x:real``] REAL_LE_TOTAL)
  THEN ASM_REWRITE_TAC[]
QED

Theorem atom_CONV_pth[unlisted]:
  (~(x:real <= y) = y < x) /\
  (~(x:real < y) = y <= x) /\
  (~(x = y) = (x:real) < y \/ y < x)
Proof
  REWRITE_TAC[real_lt] THEN REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
  REWRITE_TAC[REAL_LE_ANTISYM] THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC EQ_SYM_EQ
QED

Theorem REAL_LINEAR_PROVER_pth[unlisted] = (* |- &n >= 0 *)
  REWRITE_RULE [GSYM real_ge] (SPEC “n:num” REAL_POS);
Theorem REAL_LINEAR_PROVER_pth'[unlisted] = (* |- &SUC n > 0 *)
  REWRITE_RULE [GSYM real_gt] (SPEC “n:num” REAL_POS_LT);

Theorem GEN_REAL_ARITH0_pth_init[unlisted]:
  (x < y <=> y - x > &0) /\
  (x <= y <=> y - x >= &0) /\
  (x > y <=> x - y > &0) /\
  (x >= y <=> x - y >= &0) /\
  ((x = y) <=> (x - y = &0)) /\
  (~(x < y) <=> x - y >= &0) /\
  (~(x <= y) <=> x - y > &0) /\
  (~(x > y) <=> y - x >= &0) /\
  (~(x >= y) <=> y - x > &0) /\
  (~(x = y) <=> x - y > &0 \/ ~(x - y) > &0)
Proof
  REWRITE_TAC[real_gt, real_ge, REAL_SUB_LT, REAL_SUB_LE, REAL_NEG_SUB] >>
  REWRITE_TAC[REAL_SUB_0, real_lt] >>
  EQ_TAC THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC bool_ss [REAL_LE_REFL] >>
  CCONTR_TAC THEN FULL_SIMP_TAC bool_ss [] >>
  drule_all $ iffLR REAL_LE_ANTISYM >> ASM_SIMP_TAC bool_ss []
QED

Theorem GEN_REAL_ARITH0_pth_final[unlisted] = tautLib.TAUT `(~p ==> F) ==> p`;
Theorem GEN_REAL_ARITH0_pth_add[unlisted]:
  ((x = &0) /\ (y = &0) ==> (x + y = &0 :real)) /\
  ((x = &0) /\ y >= &0 ==> x + y >= &0) /\
  ((x = &0) /\ y > &0 ==> x + y > &0) /\
  (x >= &0 /\ (y = &0) ==> x + y >= &0) /\
  (x >= &0 /\ y >= &0 ==> x + y >= &0) /\
  (x >= &0 /\ y > &0 ==> x + y > &0) /\
  (x > &0 /\ (y = &0) ==> x + y > &0) /\
  (x > &0 /\ y >= &0 ==> x + y > &0) /\
  (x > &0 /\ y > &0 ==> x + y > &0)
Proof
  SIMP_TAC arith_ss [REAL_ADD_LID', REAL_ADD_RID, real_ge, real_gt] THEN
  REWRITE_TAC[REAL_LE_LT] THEN
  REPEAT STRIP_TAC >>
  RW_TAC bool_ss [REAL_LT_ADD, REAL_ADD_RID, REAL_ADD_LID']
QED

Theorem GEN_REAL_ARITH0_pth_mul[unlisted]:
  ((x = &0) /\ (y = &0) ==> (x * y = &0 :real)) /\
  ((x = &0) /\ y >= &0 ==> (x * y = &0)) /\
  ((x = &0) /\ y > &0 ==> (x * y = &0)) /\
  (x >= &0 /\ (y = &0) ==> (x * y = &0)) /\
  (x >= &0 /\ y >= &0 ==> x * y >= &0) /\
  (x >= &0 /\ y > &0 ==> x * y >= &0) /\
  (x > &0 /\ (y = &0) ==> (x * y = &0)) /\
  (x > &0 /\ y >= &0 ==> x * y >= &0) /\
  (x > &0 /\ y > &0 ==> x * y > &0)
Proof
  SIMP_TAC arith_ss [REAL_MUL_LZERO, REAL_MUL_RZERO, real_ge, real_gt] THEN
  SIMP_TAC arith_ss [REAL_LT_LE, REAL_LE_MUL, REAL_ENTIRE]
QED

Theorem GEN_REAL_ARITH0_pth_emul[unlisted]:
  (y = &0) ==> !x. x * y = &0 :real
Proof
  SIMP_TAC arith_ss [REAL_MUL_RZERO]
QED

Theorem GEN_REAL_ARITH0_pth_square[unlisted]:
  !x. x * x >= &0 :real
Proof
  REWRITE_TAC[real_ge, REAL_POW_2, REAL_LE_SQUARE]
QED

Theorem ABSMAXMIN_ELIM_CONV2_pth_abs[unlisted]:
  P(abs x) <=> (x >= &0 /\ P x) \/ (&0 > x /\ P (~x))
Proof
  REWRITE_TAC[real_abs, real_gt, real_ge] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[real_lt]
QED

Theorem ABSMAXMIN_ELIM_CONV2_pth_max[unlisted]:
  P(max x y) <=> (y >= x /\ P y) \/ (x > y /\ P x)
Proof
  REWRITE_TAC[real_max, real_gt, real_ge] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[real_lt]
QED

Theorem ABSMAXMIN_ELIM_CONV2_pth_min[unlisted]:
  P(min x y) <=> (y >= x /\ P x) \/ (x > y /\ P y)
Proof
  REWRITE_TAC[real_min, real_gt, real_ge] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[real_lt]
QED
