(*===========================================================================*)
(* Construct reals from positive reals                                       *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open numLib reduceLib pairLib pairTheory arithmeticTheory numTheory
     prim_recTheory jrhUtils hrealTheory mesonLib tautLib;

val _ = new_theory "realax";
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
val _ = save_thm ("REAL_10",        REAL_10);
val _ = save_thm ("REAL_ADD_SYM",   REAL_ADD_SYM);
val _ = save_thm ("REAL_MUL_SYM",   REAL_MUL_SYM);
val _ = save_thm ("REAL_ADD_ASSOC", REAL_ADD_ASSOC);
val _ = save_thm ("REAL_MUL_ASSOC", REAL_MUL_ASSOC);
val _ = save_thm ("REAL_LDISTRIB",  REAL_LDISTRIB);
val _ = save_thm ("REAL_ADD_LID",   REAL_ADD_LID);
val _ = save_thm ("REAL_MUL_LID",   REAL_MUL_LID);
val _ = save_thm ("REAL_ADD_LINV",  REAL_ADD_LINV);
val _ = save_thm ("REAL_MUL_LINV",  REAL_MUL_LINV);
val _ = save_thm ("REAL_LT_TOTAL",  REAL_LT_TOTAL);
val _ = save_thm ("REAL_LT_REFL",   REAL_LT_REFL);
val _ = save_thm ("REAL_LT_TRANS",  REAL_LT_TRANS);
val _ = save_thm ("REAL_LT_IADD",   REAL_LT_IADD);
val _ = save_thm ("REAL_LT_MUL",    REAL_LT_MUL);
val _ = save_thm ("REAL_BIJ",       REAL_BIJ);
val _ = save_thm ("REAL_ISO",       REAL_ISO);
val _ = save_thm ("REAL_INV_0",     REAL_INV_0);

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

val _ = overload_on ("+", natplus);
val _ = overload_on ("*", natmult);
val _ = overload_on ("<", natless);

Overload "~" = “$real_neg”
Overload "~" = bool_not
Overload "¬" = bool_not                                               (* UOK *)
Overload "numeric_negate" = “$real_neg”

val _ = overload_on ("+", Term`$real_add`);
val _ = overload_on ("*", Term`$real_mul`);
val _ = overload_on ("<", Term`real_lt`);

(*---------------------------------------------------------------------------*)
(* Transfer of supremum property for all-positive sets - bit painful         *)
(*---------------------------------------------------------------------------*)

val REAL_ISO_EQ = store_thm("REAL_ISO_EQ",
  “!h i. h hreal_lt i = real_of_hreal h < real_of_hreal i”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_ACCEPT_TAC REAL_ISO,
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [“h:hreal”, “i:hreal”] HREAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_ISO th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
    REWRITE_TAC[REAL_LT_REFL]]);

(* cf. the other REAL_POS exported below *)
val REAL_POS = prove (
  “!X. real_0 < real_of_hreal X”,
  GEN_TAC THEN REWRITE_TAC[REAL_BIJ]);

val SUP_ALLPOS_LEMMA1 = prove ((* no need to export *)
  “!P y. (!x. P x ==> real_0 < x) ==>
            ((?x. P x /\ y < x) =
            (?X. P(real_of_hreal X) /\ y < (real_of_hreal X)))”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN “x:real” (fn th => MP_TAC th THEN POP_ASSUM
     (SUBST1_TAC o SYM o REWRITE_RULE[REAL_BIJ] o C MATCH_MP (CONJUNCT1 th))))
    THEN DISCH_TAC THEN EXISTS_TAC “hreal_of_real x” THEN ASM_REWRITE_TAC[],
    DISCH_THEN(X_CHOOSE_THEN “X:hreal” ASSUME_TAC) THEN
    EXISTS_TAC “real_of_hreal X” THEN ASM_REWRITE_TAC[]]);

val SUP_ALLPOS_LEMMA2 = prove ((* no need to export *)
  “!P X. P(real_of_hreal X) :bool = (\h. P(real_of_hreal h)) X”,
  REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);

val SUP_ALLPOS_LEMMA3 = prove ((* no need to export *)
  “!P. (!x. P x ==> real_0 < x) /\
          (?x. P x) /\
          (?z. !x. P x ==> x < z)
           ==> (?X. (\h. P(real_of_hreal h)) X) /\
               (?Y. !X. (\h. P(real_of_hreal h)) X ==> X hreal_lt Y)”,
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
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

val SUP_ALLPOS_LEMMA4 = prove ((* no need to export *)
  “!y. ~(real_0 < y) ==> !x. y < (real_of_hreal x)”,
  GEN_TAC THEN DISCH_THEN(curry op THEN GEN_TAC o MP_TAC) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [“y:real”, “real_0”] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN DISCH_THEN(K ALL_TAC) THEN
  POP_ASSUM(MP_TAC o C CONJ (SPEC “x:hreal” REAL_POS)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_TRANS));

val REAL_SUP_ALLPOS = store_thm
  ("REAL_SUP_ALLPOS",
  “!P. (!x. P x ==> real_0 < x) /\ (?x. P x) /\ (?z. !x. P x ==> x < z)
    ==> (?s. !y. (?x. P x /\ y < x) = y < s)”,
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
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP SUP_ALLPOS_LEMMA4)] end);

(*---------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism &:num->real. (was in realTheory)    *)
(*---------------------------------------------------------------------------*)

val real_of_num = new_recursive_definition
  {name = "real_of_num",
   def = “(real_of_num 0 = real_0) /\
     (real_of_num(SUC n) = real_of_num n + real_1)”,
   rec_axiom = num_Axiom}

val _ = add_numeral_form(#"r", SOME "real_of_num");

val REAL_0 = store_thm("REAL_0",
  “real_0 = &0”,
  REWRITE_TAC[real_of_num]);

val REAL_1 = store_thm("REAL_1",
  “real_1 = &1”,
  REWRITE_TAC[num_CONV “1:num”, real_of_num, REAL_ADD_LID]);

(* NOTE: Only theorems involving ‘real_0’ and ‘real_1’ need to be re-educated.
   A "prime" is added into some exported names to make sure that the original
   theorems are still accessible.
 *)
local val reeducate = REWRITE_RULE[REAL_0, REAL_1]
in
  val REAL_10         = save_thm("REAL_10'",        reeducate(REAL_10));
  val REAL_ADD_LID    = save_thm("REAL_ADD_LID'",   reeducate(REAL_ADD_LID));
  val REAL_ADD_LINV   = save_thm("REAL_ADD_LINV'",  reeducate(REAL_ADD_LINV));
  val REAL_INV_0      = save_thm("REAL_INV_0'",     reeducate(REAL_INV_0));
  val REAL_LT_MUL     = save_thm("REAL_LT_MUL'",    reeducate(REAL_LT_MUL));
  val REAL_MUL_LID    = save_thm("REAL_MUL_LID'",   reeducate(REAL_MUL_LID));
  val REAL_MUL_LINV   = save_thm("REAL_MUL_LINV'",  reeducate(REAL_MUL_LINV));
  val REAL_SUP_ALLPOS = save_thm("REAL_SUP_ALLPOS'",reeducate(REAL_SUP_ALLPOS));
end;

(*---------------------------------------------------------------------------*)
(* Define subtraction, division and the other orderings (was in realTheory)  *)
(*---------------------------------------------------------------------------*)

val real_sub = new_definition("real_sub", “real_sub x y = x + ~y”);
val real_lte = new_definition("real_lte", “real_lte x y = ~(y < x)”);
val real_gt  = new_definition("real_gt",  “real_gt x y = y < x”);
val real_ge  = new_definition("real_ge",  “real_ge x y = (real_lte y x)”);

val real_div = new_definition("real_div", “$/ x y = x * inv y”);
val _ = set_fixity "/" (Infixl 600);
val _ = overload_on(GrammarSpecials.decimal_fraction_special, “$/”);
val _ = overload_on("/", “$/”);

local open realPP in end
val _ = add_ML_dependency "realPP"
val _ = add_user_printer ("real.decimalfractions",
                          “&(NUMERAL x) : real / &(NUMERAL y)”);

val _ = overload_on ("-",  “$-”);  (* natsub *)
val _ = overload_on ("<=", “$<=”); (* natlte *)
val _ = overload_on (">",  “$>”);  (* natgt *)
val _ = overload_on (">=", “$>=”); (* natge *)

val _ = overload_on ("-",  “$real_sub”);
val _ = overload_on ("<=", “$real_lte”);
val _ = overload_on (">",  “$real_gt”);
val _ = overload_on (">=", “$real_ge”);

val real_abs = new_definition
  ("real_abs", “abs(x) = (if (0 <= x) then x else ~x)”);

val real_pow = new_recursive_definition
   {name = "real_pow",
    def = “($pow x 0 = &1) /\ ($pow x (SUC n) = x * ($pow x n))”,
    rec_axiom = num_Axiom};
val _ = set_fixity "pow" (Infixr 700);

val real_max = new_definition
  ("real_max", “max (x :real) y = if x <= y then y else x”);

val real_min = new_definition
  ("real_min", “min (x :real) y = if x <= y then x else y”);

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

val REAL_ADD_RINV = store_thm("REAL_ADD_RINV",
  “!x:real. x + ~x = 0r”,
  MESON_TAC[REAL_ADD_SYM, REAL_ADD_LINV]);

(* HOL-Light compatible *)
val REAL_EQ_ADD_LCANCEL = store_thm
  ("REAL_EQ_ADD_LCANCEL",
  “!x y z. (x + y = x + z) <=> (y = z)”,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM “$+ ~x”) THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID]);

(* HOL-Light compatible *)
val REAL_EQ_ADD_RCANCEL = store_thm
  ("REAL_EQ_ADD_RCANCEL",
  “!x y z. (x + z = y + z) <=> (x = y)”,
  MESON_TAC[REAL_ADD_SYM, REAL_EQ_ADD_LCANCEL]);

(* HOL-Light compatible name
   |- !x y z. x * (y + z) = x * y + x * z
 *)
Theorem REAL_ADD_LDISTRIB = REAL_LDISTRIB

val REAL_RDISTRIB = store_thm("REAL_RDISTRIB",
  “!x y z. (x + y) * z = (x * z) + (y * z)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LDISTRIB);

(* HOL-Light compatible name of the above theorem *)
Theorem REAL_ADD_RDISTRIB = REAL_RDISTRIB

val REAL_MUL_RZERO = store_thm("REAL_MUL_RZERO",
  “!x. x * 0r = 0r”,
  MESON_TAC[REAL_EQ_ADD_RCANCEL, REAL_ADD_LDISTRIB, REAL_ADD_LID]);

val REAL_MUL_LZERO = store_thm("REAL_MUL_LZERO",
  “!x. 0r * x = 0r”,
  MESON_TAC[REAL_MUL_SYM, REAL_MUL_RZERO]);

val REAL_NEG_NEG = store_thm("REAL_NEG_NEG",
  “!x:real. ~~x = x”,
  MESON_TAC
   [REAL_EQ_ADD_RCANCEL, REAL_ADD_LINV, REAL_ADD_SYM, REAL_ADD_LINV]);

val REAL_MUL_RNEG = store_thm("REAL_MUL_RNEG",
  “!x y. x * ~y = ~(x * y)”,
  MESON_TAC[REAL_EQ_ADD_RCANCEL, REAL_ADD_LDISTRIB, REAL_ADD_LINV,
            REAL_MUL_RZERO]);

val REAL_MUL_LNEG = store_thm("REAL_MUL_LNEG",
   “!x y. ~x * y = ~(x * y)”,
  MESON_TAC[REAL_MUL_SYM, REAL_MUL_RNEG]);

val REAL_NEG_ADD = store_thm("REAL_NEG_ADD",
  “!x y. ~(x + y) = ~x + ~y”,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL REAL_EQ_ADD_RCANCEL)))) THEN
  Q.EXISTS_TAC `x + y` THEN REWRITE_TAC[REAL_ADD_LINV] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    “(a + b) + (c + d) = (a + c) + (b + d):real”] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_ADD_RID = store_thm("REAL_ADD_RID",
  “!x. x + 0r = x”, MESON_TAC[REAL_ADD_SYM, REAL_ADD_LID]);

val REAL_NEG_0 = store_thm("REAL_NEG_0",
  “~0r = 0r”, MESON_TAC[REAL_ADD_LINV, REAL_ADD_RID]);

(* NOTE: REAL_LE_LADD_IMP (and many others below) is primative in HOL Light, i.e.
   directly come from the quotient process, but in HOL4 it must be derived from
   other primitives.
 *)
val REAL_LT_LADD = store_thm("REAL_LT_LADD",
  “!x y z. (x + y) < (x + z) <=> y < z”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o Q.SPEC ‘~x’ o MATCH_MP REAL_LT_IADD) THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID],
    MATCH_ACCEPT_TAC REAL_LT_IADD]);

(* HOL-Light compatible name *)
Theorem REAL_LT_LADD_IMP = REAL_LT_IADD

val REAL_LE_LADD = store_thm("REAL_LE_LADD",
  “!x y z. (x + y) <= (x + z) <=> y <= z”,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LADD);

(* |- !x y z. y <= z ==> x + y <= x + z *)
val REAL_LE_LADD_IMP = save_thm("REAL_LE_LADD_IMP",
  let
    val th1 = GSYM (SPEC_ALL REAL_LE_LADD)
    val th2 = TAUT_PROVE ``(x:bool = y) ==> (x ==> y)``
  in
    Q.GENL [‘x’, ‘y’, ‘z’] (MATCH_MP th2 th1)
  end);

Theorem REAL_LE_LNEG:
  !x y. ~x <= y <=> 0r <= x + y
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THENL
   [DISCH_THEN(MP_TAC o Q.SPEC `x:real`) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LINV],
    DISCH_THEN(MP_TAC o Q.SPEC `~x`) THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_ASSOC, REAL_ADD_LID,
        ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID]]
QED

val REAL_LE_NEG2 = store_thm("REAL_LE_NEG2",
  “!x y. ~x <= ~y <=> y <= x”,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) empty_rewrites [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL_LE_RNEG = store_thm("REAL_LE_RNEG",
  ``!x y. x <= ~y <=> x + y <= 0r``,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG, GSYM REAL_NEG_ADD] THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_LE_NEG2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_LINV] THEN
  REWRITE_TAC[REAL_NEG_ADD, REAL_NEG_NEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL = store_thm("REAL",
  “!n. real_of_num (SUC n) = real_of_num n + 1r”,
  GEN_TAC THEN REWRITE_TAC[real_of_num] THEN
  REWRITE_TAC[REAL_1]);

val REAL_ADD = store_thm("REAL_ADD",
  “!m n. real_of_num m + real_of_num n = real_of_num(m + n)”,
  INDUCT_TAC THEN REWRITE_TAC[REAL, ADD, REAL_ADD_LID] THEN
  RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

(* HOL-Light compatible name of the above theorem *)
Theorem REAL_OF_NUM_ADD = REAL_ADD;

Theorem REAL_OF_NUM_SUB:
  !m n. m <= n ==> (&(n-m):real = &n - &m)
Proof
  rw[] >> ‘?d. n=m+d’ by (irule LESS_EQUAL_ADD >> simp[])
  >> simp[SUB_RIGHT_EQ]
  >> once_rewrite_tac[GSYM REAL_ADD]
  >> simp[REAL_ADD_RINV, bossLib.AC REAL_ADD_ASSOC REAL_ADD_SYM,
          real_sub, REAL_ADD_LID]
QED

val REAL_MUL = store_thm("REAL_MUL",
  “!m n. real_of_num m * real_of_num n = real_of_num(m * n)”,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, MULT_CLAUSES, REAL,
    GSYM REAL_ADD, REAL_RDISTRIB] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

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

val REAL_NOT_LE = store_thm("REAL_NOT_LE",
  “!x y. ~(x <= y) <=> y < x”,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte]);

Theorem REAL_LT_ADDR:
  !x y. x < x + y <=> 0r < y
Proof
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [“x:real”, “0r”, “y:real”] REAL_LT_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]
QED

val REAL_LT_ANTISYM = store_thm("REAL_LT_ANTISYM",
  “!x y. ~(x < y /\ y < x)”,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
  REWRITE_TAC[REAL_LT_REFL]);

val REAL_LT_GT = store_thm("REAL_LT_GT",
  “!x y. x < y ==> ~(y < x)”,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
  REWRITE_TAC[REAL_LT_ANTISYM]);

val REAL_LE_LT = store_thm("REAL_LE_LT",
  “!x y. x <= y <=> x < y \/ (x = y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [“x:real”, “y:real”] REAL_LT_TOTAL) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(DISJ_CASES_THEN2
     (curry op THEN (MATCH_MP_TAC REAL_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC REAL_LT_REFL]);

val REAL_LT_LE = store_thm("REAL_LT_LE",
  “!x y. x < y <=> x <= y /\ ~(x = y)”,
  let val lemma = TAUT_CONV “~(a /\ ~a)” in
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR, lemma]
  THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL] end);

val REAL_LT_IMP_LE = store_thm("REAL_LT_IMP_LE",
  “!x y. x < y ==> x <= y”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_LT]);

val REAL_LET_TRANS = store_thm("REAL_LET_TRANS",
  “!x y z. x <= y /\ y < z ==> x < z”,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
    (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)));

val REAL_LE_TRANS = store_thm("REAL_LE_TRANS",
  “!x y z. x <= y /\ y <= z ==> x <= z”,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
  THEN REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME “y < z”)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_IMP_LE o MATCH_MP REAL_LET_TRANS));

val REAL_LE_MUL = store_thm("REAL_LE_MUL",
  “!x y. 0r <= x /\ 0r <= y ==> 0r <= (x * y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  MAP_EVERY ASM_CASES_TAC [“0r = x”, “0r = y”] THEN
  ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[]);

val REAL_LT_RADD = store_thm("REAL_LT_RADD",
  “!x y z. (x + z) < (y + z) <=> x < y”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LADD);

val REAL_LE_RADD = store_thm("REAL_LE_RADD",
  “!x y z. (x + z) <= (y + z) <=> x <= y”,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_RADD);

Theorem REAL_NEG_LT0 :
  !x. ~x < 0r <=> 0r < x
Proof
  GEN_TAC THEN
  SUBST1_TAC(SYM(Q.SPECL [‘~x’, ‘0r’, ‘x’] REAL_LT_RADD))
  THEN REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]
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

val REAL_LNEG_UNIQ = store_thm("REAL_LNEG_UNIQ",
  “!x y. (x + y = 0r) <=> (x = ~y)”,
  REPEAT GEN_TAC THEN SUBST1_TAC (SYM(SPEC “y:real” REAL_ADD_LINV)) THEN
  MATCH_ACCEPT_TAC REAL_EQ_ADD_RCANCEL);

val REAL_RNEG_UNIQ = store_thm("REAL_RNEG_UNIQ",
  “!x y. (x + y = 0r) <=> (y = ~x)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LNEG_UNIQ);

val REAL_NEG_LMUL = store_thm("REAL_NEG_LMUL",
  “!x y. ~(x * y) = ~x * y”,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ, GSYM REAL_RDISTRIB,
              REAL_ADD_LINV, REAL_MUL_LZERO]);

val REAL_NEG_RMUL = store_thm("REAL_NEG_RMUL",
  “!x y. ~(x * y) = x * ~y”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_NEG_LMUL);

val REAL_LE_SQUARE = store_thm("REAL_LE_SQUARE",
  “!x. 0r <= x * x”,
  GEN_TAC THEN DISJ_CASES_TAC (SPEC “x:real” REAL_LE_NEGTOTAL) THEN
  POP_ASSUM(MP_TAC o MATCH_MP REAL_LE_MUL o W CONJ) THEN
  REWRITE_TAC[GSYM REAL_NEG_RMUL, GSYM REAL_NEG_LMUL, REAL_NEG_NEG]);

val REAL_LE_01 = store_thm("REAL_LE_01",
   “0r <= 1r”,
  SUBST1_TAC(SYM(SPEC “1r” REAL_MUL_LID)) THEN
  MATCH_ACCEPT_TAC REAL_LE_SQUARE);

val REAL_LT_01 = store_thm("REAL_LT_01",
   “0r < 1r”,
  REWRITE_TAC[REAL_LT_LE, REAL_LE_01] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_10]);

Theorem REAL_LE_ADDR :
  !x y. x <= x + y <=> 0r <= y
Proof
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [“x:real”, “0r”, “y:real”] REAL_LE_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]
QED

val REAL_LE_REFL = store_thm("REAL_LE_REFL",
  “!x. x <= x”,
  GEN_TAC THEN REWRITE_TAC[real_lte, REAL_LT_REFL]);

(* NOTE: previous the other REAL_POS above was exported in realaxTheory *)
val REAL_POS = store_thm("REAL_POS",
  “!n. 0r <= real_of_num n”,
  INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC “real_of_num n” THEN ASM_REWRITE_TAC[REAL] THEN
  REWRITE_TAC[REAL_LE_ADDR, REAL_LE_01]);

val REAL_LE = store_thm("REAL_LE",
  “!m n. real_of_num m <= real_of_num n <=> m <= n”,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
   [REAL, REAL_LE_RADD, ZERO_LESS_EQ, LESS_EQ_MONO, REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM NOT_LESS, LESS_0] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “real_of_num n” THEN
    ASM_REWRITE_TAC[ZERO_LESS_EQ, REAL_LE_ADDR, REAL_LE_01],
    DISCH_THEN(MP_TAC o C CONJ (SPEC “m:num” REAL_POS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
    REWRITE_TAC[REAL_NOT_LE, REAL_LT_ADDR, REAL_LT_01]]);

(* HOL-Light compatible name of the above theorem *)
Theorem REAL_OF_NUM_LE = REAL_LE;

(* |- !n. 0 <= n *)
val LE_0 = ZERO_LESS_EQ; (* arithmeticTheory *)

Theorem REAL_ABS_NUM :
   !n. abs(real_of_num n) = real_of_num n
Proof
  REWRITE_TAC[real_abs, REAL_OF_NUM_LE, LE_0]
QED

val REAL_LTE_TOTAL = store_thm("REAL_LTE_TOTAL",
  “!x y. x < y \/ y <= x”,
  REWRITE_TAC[real_lt] THEN CONV_TAC TAUT);

val REAL_LET_TOTAL = store_thm("REAL_LET_TOTAL",
  “!x y. x <= y \/ y < x”,
  REWRITE_TAC[real_lt] THEN CONV_TAC TAUT);

val REAL_LTE_TRANS = store_thm("REAL_LTE_TRANS",
  “!x y z. x < y /\ y <= z ==> x < z”,
  MESON_TAC[real_lt, REAL_LE_TRANS]);

val REAL_LE_ADD = store_thm("REAL_LE_ADD",
  “!x y. 0r <= x /\ 0r <= y ==> 0r <= (x + y)”,
  MESON_TAC[REAL_LE_LADD_IMP, REAL_ADD_RID, REAL_LE_TRANS]);

val REAL_LTE_ANTISYM = store_thm("REAL_LTE_ANTISYM",
  “!x y. ~(x <= y /\ y < x)”,
  MESON_TAC[real_lt]);

val REAL_SUB_LE = store_thm("REAL_SUB_LE",
  “!x y. 0r <= (x - y) <=> y <= x”,
  REWRITE_TAC[real_sub, GSYM REAL_LE_LNEG, REAL_LE_NEG2]);

val REAL_NEG_SUB = store_thm("REAL_NEG_SUB",
  “!x y. ~(x - y) = y - x”,
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEG_NEG] THEN
  REWRITE_TAC[Once REAL_ADD_AC]);

val REAL_SUB_LT = store_thm("REAL_SUB_LT",
  “!x y. 0r < x - y <=> y < x”,
  REWRITE_TAC[real_lt] THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[REAL_LE_LNEG, REAL_ADD_RID, REAL_SUB_LE]);

val REAL_LE_ANTISYM = store_thm("REAL_LE_ANTISYM",
  “!x y. x <= y /\ y <= x <=> (x = y)”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[real_lte] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (SPECL [“x:real”, “y:real”] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]]);

val REAL_NOT_LT = store_thm("REAL_NOT_LT",
  “!x y. ~(x < y) <=> y <= x”,
  REWRITE_TAC[real_lte]);

val REAL_SUB_0 = store_thm("REAL_SUB_0",
  “!x y. (x - y = 0r) <=> (x = y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites
                  [GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_SUB_LE, REAL_SUB_LT] THEN REWRITE_TAC[REAL_NOT_LT]);

val REAL_LTE_ADD = store_thm("REAL_LTE_ADD",
  “!x y. 0r < x /\ 0r <= y ==> 0r < (x + y)”,
  MESON_TAC[REAL_LE_LADD_IMP, REAL_ADD_RID, REAL_LTE_TRANS]);

val REAL_LET_ADD = store_thm("REAL_LET_ADD",
  “!x y. 0r <= x /\ 0r < y ==> 0r < (x + y)”,
  MESON_TAC[REAL_LTE_ADD, REAL_ADD_SYM]);

val REAL_LT_ADD = store_thm("REAL_LT_ADD",
  “!x y. 0r < x /\ 0r < y ==> 0r < (x + y)”,
  MESON_TAC[REAL_LT_IMP_LE, REAL_LTE_ADD]);

val REAL_ENTIRE = store_thm("REAL_ENTIRE",
  “!x y. (x * y = 0r) <=> (x = 0r) \/ (y = 0r)”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC “x = 0r” THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(MATCH_MP REAL_MUL_LINV) THEN
    DISCH_THEN(MP_TAC o AP_TERM “$* (inv x)”) THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RZERO],
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO]]);

val REAL_MUL_RID = store_thm("REAL_MUL_RID",
  “!x. x * 1r = x”,
  MESON_TAC[REAL_MUL_LID, REAL_MUL_SYM]);

val REAL_POW_2 = store_thm("REAL_POW_2",
  “!x. x pow 2 = x * x”,
  REWRITE_TAC[num_CONV “2:num”, num_CONV “1:num”] THEN
  REWRITE_TAC[real_pow, REAL_MUL_RID]);

(* This actually shows that real numbers and (+,*,0,1) form a semi-ring *)
Theorem REAL_POLY_CLAUSES :
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
  REWRITE_TAC[REAL_MUL_ASSOC, REAL_ADD_ASSOC, REAL_ADD_LID, REAL_MUL_LID] THEN
  REWRITE_TAC[Once REAL_ADD_AC] THEN REWRITE_TAC[Once REAL_MUL_SYM]
QED

Theorem REAL_POLY_NEG_CLAUSES :
   (!x. ~x = ~(1r) * x) /\
   (!x y. x - y = x + ~(1r) * y)
Proof
  REWRITE_TAC[REAL_MUL_LNEG, real_sub, REAL_MUL_LID]
QED

val REAL_LE_TOTAL = store_thm("REAL_LE_TOTAL",
  “!x y. x <= y \/ y <= x”,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_lte, GSYM DE_MORGAN_THM, REAL_LT_ANTISYM]);

(* NOTE: MESON_TAC (original proof) doesn't work here. METIS_TAC is used *)
Theorem REAL_ABS_NEG :
   !x. abs(~x) = abs x
Proof
  GEN_TAC THEN
  REWRITE_TAC[real_abs, REAL_LE_RNEG, REAL_NEG_NEG, REAL_ADD_LID] THEN
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_ANTISYM, REAL_NEG_0]
QED

val REAL_LT_NZ = store_thm("REAL_LT_NZ",
  “!n. ~(real_of_num n = 0r) <=> (0r < real_of_num n)”,
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_CASES_TAC “real_of_num n = 0r” THEN
  ASM_REWRITE_TAC[REAL_LE_REFL, REAL_POS]);

val REAL_INJ = store_thm("REAL_INJ",
  “!m n. (real_of_num m = real_of_num n) <=> (m = n)”,
  let val th = prove(“(m:num = n) <=> m <= n /\ n <= m”,
                 EQ_TAC THENL
                  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LESS_EQ_REFL],
                   MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[th, GSYM REAL_LE_ANTISYM, REAL_LE] end);

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

val _ = export_theory();
