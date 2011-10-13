(*---------------------------------------------------------------------------*)
(* Develop the theory of reals                                               *)
(*---------------------------------------------------------------------------*)

structure realScript =
struct

(*
app load ["numLib",
          "pairLib",
          "mesonLib",
          "tautLib",
          "simpLib",
          "Ho_Rewrite",
          "AC",
          "hol88Lib",
          "jrhUtils",
          "realaxTheory"];
*)

open HolKernel Parse boolLib hol88Lib numLib reduceLib pairLib
     arithmeticTheory numTheory prim_recTheory whileTheory
     mesonLib tautLib simpLib Ho_Rewrite Arithconv
     jrhUtils Canon_Port hratTheory hrealTheory realaxTheory
     BasicProvers TotalDefn metisLib bossLib;

val _ = new_theory "real";

val AC = AC.AC;

val num_EQ_CONV = Arithconv.NEQ_CONV;

(*---------------------------------------------------------------------------*)
(* Now define the inclusion homomorphism &:num->real.                        *)
(*---------------------------------------------------------------------------*)

val real_of_num = new_recursive_definition
  {name = "real_of_num",
   def = --`(real_of_num 0 = real_0) /\
     (real_of_num(SUC n) = real_of_num n + real_1)`--,
   rec_axiom = num_Axiom}

val _ = add_numeral_form(#"r", SOME "real_of_num");

val REAL_0 = store_thm("REAL_0",
  (--`real_0 = &0`--),
  REWRITE_TAC[real_of_num]);

val REAL_1 = store_thm("REAL_1",
  (--`real_1 = & 1`--),
  REWRITE_TAC[num_CONV (--`1:num`--), real_of_num, REAL_ADD_LID]);

local val reeducate = REWRITE_RULE[REAL_0, REAL_1]
in
  val REAL_10 = save_thm("REAL_10",reeducate(REAL_10))
  val REAL_ADD_SYM = save_thm("REAL_ADD_SYM",reeducate(REAL_ADD_SYM))
  val REAL_ADD_COMM = save_thm("REAL_ADD_COMM", REAL_ADD_SYM)
  val REAL_ADD_ASSOC = save_thm("REAL_ADD_ASSOC",reeducate(REAL_ADD_ASSOC))
  val REAL_ADD_LID = save_thm("REAL_ADD_LID",reeducate(REAL_ADD_LID))
  val REAL_ADD_LINV = save_thm("REAL_ADD_LINV",reeducate(REAL_ADD_LINV))
  val REAL_LDISTRIB = save_thm("REAL_LDISTRIB",reeducate(REAL_LDISTRIB))
  val REAL_LT_TOTAL = save_thm("REAL_LT_TOTAL",reeducate(REAL_LT_TOTAL))
  val REAL_LT_REFL = save_thm("REAL_LT_REFL",reeducate(REAL_LT_REFL))
  val REAL_LT_TRANS = save_thm("REAL_LT_TRANS",reeducate(REAL_LT_TRANS))
  val REAL_LT_IADD = save_thm("REAL_LT_IADD",reeducate(REAL_LT_IADD))
  val REAL_SUP_ALLPOS = save_thm("REAL_SUP_ALLPOS",reeducate(REAL_SUP_ALLPOS))
  val REAL_MUL_SYM = save_thm("REAL_MUL_SYM",reeducate(REAL_MUL_SYM))
  val REAL_MUL_COMM = save_thm("REAL_MUL_COMM", REAL_MUL_SYM)
  val REAL_MUL_ASSOC = save_thm("REAL_MUL_ASSOC",reeducate(REAL_MUL_ASSOC))
  val REAL_MUL_LID = save_thm("REAL_MUL_LID",reeducate(REAL_MUL_LID))
  val REAL_MUL_LINV = save_thm("REAL_MUL_LINV",reeducate(REAL_MUL_LINV))
  val REAL_LT_MUL = save_thm("REAL_LT_MUL",reeducate(REAL_LT_MUL))
  val REAL_INV_0 = save_thm("REAL_INV_0",reeducate REAL_INV_0)
end;

val _ = export_rewrites
        ["REAL_ADD_LID", "REAL_ADD_LINV", "REAL_LT_REFL", "REAL_MUL_LID"]

(*---------------------------------------------------------------------------*)
(* Define subtraction, division and the other orderings                      *)
(*---------------------------------------------------------------------------*)

val real_sub = new_definition("real_sub", ``real_sub x y = x + ~y``);
val real_lte = new_definition("real_lte", ``real_lte x y = ~(y < x)``);
val real_gt = new_definition("real_gt", ``real_gt x y = y < x``);
val real_ge = new_definition("real_ge", ``real_ge x y = (real_lte y x)``);

val real_div = new_definition("real_div", ``$/ x y = x * inv y``);
val _ = set_fixity "/" (Infixl 600);
val _ = overload_on(GrammarSpecials.decimal_fraction_special, ``$/``)
val _ = overload_on("/", ``$/``)
val _ = add_user_printer
            ("(DecimalFractionPP.fraction{Thy=\"real\",Division=\"/\",\
             \fromNum=\"real_of_num\"})",
             ``&(NUMERAL x) / &(NUMERAL y)``,
             DecimalFractionPP.fraction{Thy="real",Division="/",
                                        fromNum="real_of_num"})

val natsub = Term`$-`;
val natlte = Term`$<=`;
val natgt = Term`$>`;
val natge = Term`$>=`;

val _ = overload_on ("-",  natsub);
val _ = overload_on ("<=", natlte);
val _ = overload_on (">",  natgt);
val _ = overload_on (">=", natge);

val _ = overload_on ("-",  Term`$real_sub`);
val _ = overload_on ("<=", Term`$real_lte`);
val _ = overload_on (">",  Term`$real_gt`);
val _ = overload_on (">=", Term`$real_ge`);

(*---------------------------------------------------------------------------*)
(* Prove lots of boring field theorems                                       *)
(*---------------------------------------------------------------------------*)

val REAL_ADD_RID = store_thm("REAL_ADD_RID",
  (--`!x. x + 0 = x`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_ADD_LID);
val _ = export_rewrites ["REAL_ADD_RID"]

val REAL_ADD_RINV = store_thm("REAL_ADD_RINV",
  (--`!x:real. x + ~x = 0`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_ADD_LINV);
val _ = export_rewrites ["REAL_ADD_RINV"]

val REAL_MUL_RID = store_thm("REAL_MUL_RID",
  (--`!x. x * 1 = x`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LID);
val _ = export_rewrites ["REAL_MUL_RID"]

val REAL_MUL_RINV = store_thm("REAL_MUL_RINV",
  (--`!x. ~(x = 0) ==> (x * inv x = 1)`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LINV);

val REAL_RDISTRIB = store_thm("REAL_RDISTRIB",
  (--`!x y z. (x + y) * z = (x * z) + (y * z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LDISTRIB);

val REAL_EQ_LADD = store_thm("REAL_EQ_LADD",
  (--`!x y z. (x + y = x + z) = (y = z)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$+ ~x`--)) THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);
val _ = export_rewrites ["REAL_EQ_LADD"]

val REAL_EQ_RADD = store_thm("REAL_EQ_RADD",
  (--`!x y z. (x + z = y + z) = (x = y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_EQ_LADD);
val _ = export_rewrites ["REAL_EQ_RADD"]

val REAL_ADD_LID_UNIQ = store_thm("REAL_ADD_LID_UNIQ",
  (--`!x y. (x + y = y) = (x = 0)`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ADD_LID] THEN
  MATCH_ACCEPT_TAC REAL_EQ_RADD);

val REAL_ADD_RID_UNIQ = store_thm("REAL_ADD_RID_UNIQ",
  (--`!x y. (x + y = x) = (y = 0)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_ADD_LID_UNIQ);

val REAL_LNEG_UNIQ = store_thm("REAL_LNEG_UNIQ",
  (--`!x y. (x + y = 0) = (x = ~y)`--),
  REPEAT GEN_TAC THEN SUBST1_TAC (SYM(SPEC (--`y:real`--) REAL_ADD_LINV)) THEN
  MATCH_ACCEPT_TAC REAL_EQ_RADD);

val REAL_RNEG_UNIQ = store_thm("REAL_RNEG_UNIQ",
  (--`!x y. (x + y = 0) = (y = ~x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LNEG_UNIQ);

val REAL_NEG_ADD = store_thm("REAL_NEG_ADD",
  (--`!x y. ~(x + y) = ~x + ~y`--),
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + (c + d) = (a + c) + (b + d):real`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_MUL_LZERO = store_thm("REAL_MUL_LZERO",
  (--`!x. 0 * x = 0`--),
  GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`&0 * x`--), (--`&0 * x`--)] REAL_ADD_LID_UNIQ))
  THEN REWRITE_TAC[GSYM REAL_RDISTRIB, REAL_ADD_LID]);
val _ = export_rewrites ["REAL_MUL_LZERO"]

val REAL_MUL_RZERO = store_thm("REAL_MUL_RZERO",
  (--`!x. x * 0 = 0`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_MUL_LZERO);
val _ = export_rewrites ["REAL_MUL_RZERO"]

val REAL_NEG_LMUL = store_thm("REAL_NEG_LMUL",
  (--`!x y. ~(x * y) = ~x * y`--),
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ, GSYM REAL_RDISTRIB,
              REAL_ADD_LINV, REAL_MUL_LZERO]);

val REAL_NEG_RMUL = store_thm("REAL_NEG_RMUL",
  (--`!x y. ~(x * y) = x * ~y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_NEG_LMUL);

val REAL_NEGNEG = store_thm("REAL_NEGNEG",
  (--`!x. ~~x = x`--),
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM REAL_LNEG_UNIQ, REAL_ADD_RINV]);
val _ = export_rewrites ["REAL_NEGNEG"]

val REAL_NEG_MUL2 = store_thm("REAL_NEG_MUL2",
  (--`!x y. ~x * ~y = x * y`--),
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL, REAL_NEGNEG]);

val REAL_ENTIRE = store_thm("REAL_ENTIRE",
  (--`!x y. (x * y = 0) = (x = 0) \/ (y = 0)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC (--`x = 0`--) THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(MATCH_MP REAL_MUL_LINV) THEN
    DISCH_THEN(MP_TAC o AP_TERM (--`$* (inv x)`--)) THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RZERO],
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO]]);
val _ = export_rewrites ["REAL_ENTIRE"]

val REAL_LT_LADD = store_thm("REAL_LT_LADD",
  (--`!x y z. (x + y) < (x + z) = y < z`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC (--`~x`--) o MATCH_MP REAL_LT_IADD) THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID],
    MATCH_ACCEPT_TAC REAL_LT_IADD]);
val _ = export_rewrites ["REAL_LT_LADD"]

val REAL_LT_RADD = store_thm("REAL_LT_RADD",
  (--`!x y z. (x + z) < (y + z) = x < y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LADD);
val _ = export_rewrites ["REAL_LT_RADD"]

val REAL_NOT_LT = store_thm("REAL_NOT_LT",
  (--`!x y. ~(x < y) = y <= x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte]);

val REAL_LT_ANTISYM = store_thm("REAL_LT_ANTISYM",
  (--`!x y. ~(x < y /\ y < x)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_TRANS) THEN
  REWRITE_TAC[REAL_LT_REFL]);

val REAL_LT_GT = store_thm("REAL_LT_GT",
  (--`!x y. x < y ==> ~(y < x)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
  REWRITE_TAC[REAL_LT_ANTISYM]);

val REAL_NOT_LE = store_thm("REAL_NOT_LE",
  (--`!x y. ~(x <= y) = y < x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte]);

val REAL_LE_TOTAL = store_thm("REAL_LE_TOTAL",
  (--`!x y. x <= y \/ y <= x`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_lte, GSYM DE_MORGAN_THM, REAL_LT_ANTISYM]);

val REAL_LET_TOTAL = store_thm("REAL_LET_TOTAL",
  (--`!x y. x <= y \/ y < x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  BOOL_CASES_TAC (--`y < x`--) THEN REWRITE_TAC[]);

val REAL_LTE_TOTAL = store_thm("REAL_LTE_TOTAL",
  (--`!x y. x < y \/ y <= x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  BOOL_CASES_TAC (--`x < y`--) THEN REWRITE_TAC[]);

val REAL_LE_REFL = store_thm("REAL_LE_REFL",
  (--`!x. x <= x`--),
  GEN_TAC THEN REWRITE_TAC[real_lte, REAL_LT_REFL]);
val _ = export_rewrites ["REAL_LE_REFL"]

val REAL_LE_LT = store_thm("REAL_LE_LT",
  (--`!x y. x <= y = x < y \/ (x = y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(DISJ_CASES_THEN2
     (curry op THEN (MATCH_MP_TAC REAL_LT_GT) o ACCEPT_TAC) SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC REAL_LT_REFL]);

val REAL_LT_LE = store_thm("REAL_LT_LE",
  (--`!x y. x < y = x <= y /\ ~(x = y)`--),
  let val lemma = TAUT_CONV (--`~(a /\ ~a)`--) in
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR, lemma]
  THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL] end);

val REAL_LT_IMP_LE = store_thm("REAL_LT_IMP_LE",
  (--`!x y. x < y ==> x <= y`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_LT]);

val REAL_LTE_TRANS = store_thm("REAL_LTE_TRANS",
  (--`!x y z. x < y /\ y <= z ==> x < z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, LEFT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN REWRITE_TAC[]);

val REAL_LET_TRANS = store_thm("REAL_LET_TRANS",
  (--`!x y z. x <= y /\ y < z ==> x < z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT, RIGHT_AND_OVER_OR] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (ACCEPT_TAC o MATCH_MP REAL_LT_TRANS)
    (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC)));

val REAL_LE_TRANS = store_thm("REAL_LE_TRANS",
  (--`!x y z. x <= y /\ y <= z ==> x <= z`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC))
  THEN REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C CONJ (ASSUME (--`y < z`--))) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP REAL_LT_IMP_LE o MATCH_MP REAL_LET_TRANS));

val REAL_LE_ANTISYM = store_thm("REAL_LE_ANTISYM",
  (--`!x y. x <= y /\ y <= x = (x = y)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[real_lte] THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]]);

val REAL_LET_ANTISYM = store_thm("REAL_LET_ANTISYM",
  (--`!x y. ~(x < y /\ y <= x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  BOOL_CASES_TAC (--`x < y`--) THEN REWRITE_TAC[]);

val REAL_LTE_ANTSYM = store_thm("REAL_LTE_ANTSYM",
  (--`!x y. ~(x <= y /\ y < x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LET_ANTISYM);

val REAL_NEG_LT0 = store_thm("REAL_NEG_LT0",
  (--`!x. ~x < 0 = 0 < x`--),
  GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`~x`--), (--`0`--), (--`x:real`--)] REAL_LT_RADD))
  THEN REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);
val _ = export_rewrites ["REAL_NEG_LT0"]

val REAL_NEG_GT0 = store_thm("REAL_NEG_GT0",
  (--`!x. 0 < ~x = x < 0`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LT0, REAL_NEGNEG]);
val _ = export_rewrites ["REAL_NEG_GT0"]

val REAL_NEG_LE0 = store_thm("REAL_NEG_LE0",
  (--`!x. ~x <= 0 = 0 <= x`--),
  GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  REWRITE_TAC[REAL_NEG_GT0]);
val _ = export_rewrites ["REAL_NEG_LE0"]

val REAL_NEG_GE0 = store_thm("REAL_NEG_GE0",
  (--`!x. 0 <= ~x = x <= 0`--),
  GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  REWRITE_TAC[REAL_NEG_LT0]);
val _ = export_rewrites ["REAL_NEG_GE0"]

val REAL_LT_NEGTOTAL = store_thm("REAL_LT_NEGTOTAL",
  (--`!x. (x = 0) \/ (0 < x) \/ (0 < ~x)`--),
  GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [(--`x:real`--), (--`0`--)] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[SYM(REWRITE_RULE[REAL_NEGNEG]
                         (SPEC (--`~x`--) REAL_NEG_LT0))]);

val REAL_LE_NEGTOTAL = store_thm("REAL_LE_NEGTOTAL",
  (--`!x. 0 <= x \/ 0 <= ~x`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
          (SPEC (--`x:real`--) REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[]);

val REAL_LE_MUL = store_thm("REAL_LE_MUL",
  (--`!x y. 0 <= x /\ 0 <= y ==> 0 <= (x * y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  MAP_EVERY ASM_CASES_TAC [(--`0 = x`--), (--`0 = y`--)] THEN
  ASM_REWRITE_TAC[] THEN TRY(FIRST_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  DISCH_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[]);

val REAL_LE_SQUARE = store_thm("REAL_LE_SQUARE",
  (--`!x. 0 <= x * x`--),
  GEN_TAC THEN DISJ_CASES_TAC (SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THEN
  POP_ASSUM(MP_TAC o MATCH_MP REAL_LE_MUL o W CONJ) THEN
  REWRITE_TAC[GSYM REAL_NEG_RMUL, GSYM REAL_NEG_LMUL, REAL_NEGNEG]);

val REAL_LE_01 = store_thm("REAL_LE_01",
  (--`0 <= &1`--),
  SUBST1_TAC(SYM(SPEC (--`&1`--) REAL_MUL_LID)) THEN
  MATCH_ACCEPT_TAC REAL_LE_SQUARE);

val REAL_LT_01 = store_thm("REAL_LT_01",
  (--`0 < &1`--),
  REWRITE_TAC[REAL_LT_LE, REAL_LE_01] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_10]);

val REAL_LE_LADD = store_thm("REAL_LE_LADD",
  (--`!x y z. (x + y) <= (x + z) = y <= z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LADD);
val _ = export_rewrites ["REAL_LE_LADD"]

val REAL_LE_RADD = store_thm("REAL_LE_RADD",
  (--`!x y z. (x + z) <= (y + z) = x <= y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_lte] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_LT_RADD);
val _ = export_rewrites ["REAL_LE_RADD"]

val REAL_LT_ADD2 = store_thm("REAL_LT_ADD2",
  (--`!w x y z. w < x /\ y < z ==> (w + y) < (x + z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`w + z`--) THEN
  ASM_REWRITE_TAC[REAL_LT_LADD, REAL_LT_RADD]);

val REAL_LE_ADD2 = store_thm("REAL_LE_ADD2",
  (--`!w x y z. w <= x /\ y <= z ==> (w + y) <= (x + z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`w + z`--) THEN
  ASM_REWRITE_TAC[REAL_LE_LADD, REAL_LE_RADD]);

val REAL_LE_ADD = store_thm("REAL_LE_ADD",
  (--`!x y. 0 <= x /\ 0 <= y ==> 0 <= (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2) THEN
  REWRITE_TAC[REAL_ADD_LID]);

val REAL_LT_ADD = store_thm("REAL_LT_ADD",
  (--`!x y. 0 < x /\ 0 < y ==> 0 < (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
  REWRITE_TAC[REAL_ADD_LID]);

val REAL_LT_ADDNEG = store_thm("REAL_LT_ADDNEG",
  (--`!x y z. y < x + ~z = y+z < x`--),
  REPEAT GEN_TAC THEN  SUBST1_TAC
  (SYM(SPECL [(--`y:real`--), (--`x + ~z`--), (--`z:real`--)] REAL_LT_RADD))
  THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID]);

val REAL_LT_ADDNEG2 = store_thm("REAL_LT_ADDNEG2",
  (--`!x y z. (x + ~y) < z = x < (z + y)`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x + ~y`--), (--`z:real`--), (--`y:real`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID]);

val REAL_LT_ADD1 = store_thm("REAL_LT_ADD1",
  (--`!x y. x <= y ==> x < (y + &1)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [POP_ASSUM(MP_TAC o MATCH_MP REAL_LT_ADD2 o C CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_ADD_RID],
    POP_ASSUM SUBST1_TAC THEN
    GEN_REWR_TAC LAND_CONV  [GSYM REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_LT_LADD, REAL_LT_01]]);

val REAL_SUB_ADD = store_thm("REAL_SUB_ADD",
  (--`!x y. (x - y) + y = x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC,
    REAL_ADD_LINV, REAL_ADD_RID]);

val REAL_SUB_ADD2 = store_thm("REAL_SUB_ADD2",
  (--`!x y. y + (x - y) = x`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_SUB_ADD);

val REAL_SUB_REFL = store_thm("REAL_SUB_REFL",
  (--`!x. x - x = 0`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, REAL_ADD_RINV]);
val _ = export_rewrites ["REAL_SUB_REFL"]

val REAL_SUB_0 = store_thm("REAL_SUB_0",
  (--`!x y. (x - y = 0) = (x = y)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C AP_THM (--`y:real`--) o AP_TERM (--`$+`--)) THEN
    REWRITE_TAC[REAL_SUB_ADD, REAL_ADD_LID],
    DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_SUB_REFL]);
val _ = export_rewrites ["REAL_SUB_0"]

val REAL_LE_DOUBLE = store_thm("REAL_LE_DOUBLE",
  (--`!x. 0 <= x + x = 0 <= x`--),
  GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2 o W CONJ),
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2 o W CONJ)] THEN
  REWRITE_TAC[REAL_ADD_LID]);

val REAL_LE_NEGL = store_thm("REAL_LE_NEGL",
  (--`!x. (~x <= x) = (0 <= x)`--),
  GEN_TAC THEN SUBST1_TAC
  (SYM(SPECL [(--`x:real`--), (--`~x`--), (--`x:real`--)] REAL_LE_LADD))
  THEN REWRITE_TAC[REAL_ADD_RINV, REAL_LE_DOUBLE]);

val REAL_LE_NEGR = store_thm("REAL_LE_NEGR",
  (--`!x. (x <= ~x) = (x <= 0)`--),
  GEN_TAC THEN SUBST1_TAC(SYM(SPEC (--`x:real`--) REAL_NEGNEG)) THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV) [REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_LE_NEGL] THEN REWRITE_TAC[REAL_NEG_GE0] THEN
  REWRITE_TAC[REAL_NEGNEG]);

val REAL_NEG_EQ0 = store_thm("REAL_NEG_EQ0",
  (--`!x. (~x = 0) = (x = 0)`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$+ x`--)),
    DISCH_THEN(MP_TAC o AP_TERM (--`$+ ~x`--))] THEN
  REWRITE_TAC[REAL_ADD_RINV, REAL_ADD_LINV, REAL_ADD_RID] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);

val REAL_NEG_0 = store_thm("REAL_NEG_0",
  (--`~0 = 0`--),
  REWRITE_TAC[REAL_NEG_EQ0]);
val _ = export_rewrites ["REAL_NEG_0"]

val REAL_NEG_SUB = store_thm("REAL_NEG_SUB",
  (--`!x y. ~(x - y) = y - x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL_SUB_LT = store_thm("REAL_SUB_LT",
  (--`!x y. 0 < x - y = y < x`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`0`--), (--`x - y`--), (--`y:real`--)]
                       REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD, REAL_ADD_LID]);

val REAL_SUB_LE = store_thm("REAL_SUB_LE",
  (--`!x y. 0 <= (x - y) = y <= x`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`0`--), (--`x - y`--), (--`y:real`--)]
                      REAL_LE_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD, REAL_ADD_LID]);

val REAL_ADD_SUB = store_thm("REAL_ADD_SUB",
  (--`!x y. (x + y) - x = y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_RID]);

val REAL_EQ_LMUL = store_thm("REAL_EQ_LMUL",
  (--`!x y z. (x * y = x * z) = (x = 0) \/ (y = z)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$* (inv x)`--)) THEN
    ASM_CASES_TAC (--`x = 0`--) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM(fn th => REWRITE_TAC[REAL_MUL_ASSOC, MATCH_MP REAL_MUL_LINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID],
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LZERO]]);
val _ = export_rewrites ["REAL_EQ_LMUL"]

val REAL_EQ_RMUL = store_thm("REAL_EQ_RMUL",
  (--`!x y z. (x * z = y * z) = (z = 0) \/ (x = y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_EQ_LMUL);
val _ = export_rewrites ["REAL_EQ_RMUL"]

val REAL_SUB_LDISTRIB = store_thm("REAL_SUB_LDISTRIB",
  (--`!x y z. x * (y - z) = (x * y) - (x * z)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_LDISTRIB, REAL_NEG_RMUL]);

val REAL_SUB_RDISTRIB = store_thm("REAL_SUB_RDISTRIB",
  (--`!x y z. (x - y) * z = (x * z) - (y * z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_SUB_LDISTRIB);

val REAL_NEG_EQ = store_thm("REAL_NEG_EQ",
  (--`!x y. (~x = y) = (x = ~y)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_NEGNEG]);

val REAL_NEG_MINUS1 = store_thm("REAL_NEG_MINUS1",
  (--`!x. ~x = ~1 * x`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_INV_NZ = store_thm("REAL_INV_NZ",
  (--`!x. ~(x = 0) ==> ~(inv x = 0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM (--`x:real`--) o AP_TERM (--`$*`--)) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_10]);

val REAL_INVINV = store_thm("REAL_INVINV",
  (--`!x. ~(x = 0) ==> (inv (inv x) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_MUL_RINV) THEN
  ASM_CASES_TAC (--`inv x = 0`--) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO, GSYM REAL_10] THEN
  MP_TAC(SPECL [(--`inv(inv x)`--), (--`x:real`--), (--`inv x`--)] REAL_EQ_RMUL)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
  FIRST_ASSUM ACCEPT_TAC);

val REAL_LT_IMP_NE = store_thm("REAL_LT_IMP_NE",
  (--`!x y. x < y ==> ~(x = y)`--),
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_LT_REFL]);

val REAL_INV_POS = store_thm("REAL_INV_POS",
  (--`!x. 0 < x ==> 0 < inv x`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT_TCL DISJ_CASES_THEN
   MP_TAC (SPECL [(--`inv x`--), (--`0`--)] REAL_LT_TOTAL) THENL
   [POP_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_NZ o
              GSYM o MATCH_MP REAL_LT_IMP_NE) THEN ASM_REWRITE_TAC[],
    ONCE_REWRITE_TAC[GSYM REAL_NEG_GT0] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL o C CONJ (ASSUME (--`0 < x`--))) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    POP_ASSUM(fn th => REWRITE_TAC
     [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_NEG_GT0] THEN DISCH_THEN(MP_TAC o CONJ REAL_LT_01) THEN
    REWRITE_TAC[REAL_LT_ANTISYM],
    REWRITE_TAC[]]);

val REAL_LT_LMUL_0 = store_thm("REAL_LT_LMUL_0",
  (--`!x y. 0 < x ==> (0 < (x * y) = 0 < y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [FIRST_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ (MATCH_MP REAL_INV_POS th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC
      [MATCH_MP REAL_MUL_LINV (GSYM (MATCH_MP REAL_LT_IMP_NE th))]) THEN
    REWRITE_TAC[REAL_MUL_LID],
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);

val REAL_LT_RMUL_0 = store_thm("REAL_LT_RMUL_0",
  (--`!x y. 0 < y ==> (0 < (x * y) = 0 < x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL_0);

val REAL_LT_LMUL = store_thm("REAL_LT_LMUL",
  (--`!x y z. 0 < x ==> ((x * y) < (x * z) = y < z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_LT_LMUL_0);

val REAL_LT_RMUL = store_thm("REAL_LT_RMUL",
  (--`!x y z. 0 < z ==> ((x * z) < (y * z) = x < y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_LMUL);

val REAL_LT_RMUL_IMP = store_thm("REAL_LT_RMUL_IMP",
  (--`!x y z. x < y /\ 0 < z ==> (x * z) < (y * z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fn th => REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_RMUL th)]));

val REAL_LT_LMUL_IMP = store_thm("REAL_LT_LMUL_IMP",
  (--`!x y z. y < z  /\ 0 < x ==> (x * y) < (x * z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  POP_ASSUM(fn th => REWRITE_TAC[GEN_ALL(MATCH_MP REAL_LT_LMUL th)]));

val REAL_LINV_UNIQ = store_thm("REAL_LINV_UNIQ",
  (--`!x y. (x * y = &1) ==> (x = inv y)`--),
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`x = 0`--) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO, GSYM REAL_10] THEN
  DISCH_THEN(MP_TAC o AP_TERM (--`$* (inv x)`--)) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC REAL_INVINV);

val REAL_RINV_UNIQ = store_thm("REAL_RINV_UNIQ",
  (--`!x y. (x * y = &1) ==> (y = inv x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LINV_UNIQ);

val REAL_INV_INV = store_thm("REAL_INV_INV",
 Term`!x. inv(inv x) = x`,
  GEN_TAC THEN ASM_CASES_TAC (Term `x = 0`) THEN
  ASM_REWRITE_TAC[REAL_INV_0] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC REAL_RINV_UNIQ THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  ASM_REWRITE_TAC[]);;

val REAL_INV_EQ_0 = store_thm("REAL_INV_EQ_0",
 Term`!x. (inv(x) = 0) = (x = 0)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN ASM_REWRITE_TAC[REAL_INV_0]);;

val REAL_NEG_INV = store_thm("REAL_NEG_INV",
  (--`!x. ~(x = 0) ==> (~inv x = inv (~x))`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_NEGNEG]);

val REAL_INV_1OVER = store_thm("REAL_INV_1OVER",
  (--`!x. inv x = &1 / x`--),
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_LID]);

val REAL_LT_INV_EQ = store_thm("REAL_LT_INV_EQ",
 Term`!x. 0 < inv x = 0 < x`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[REAL_INV_POS] THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[REAL_INV_POS]);;

val REAL_LE_INV_EQ = store_thm("REAL_LE_INV_EQ",
 Term`!x. 0 <= inv x = 0 <= x`,
  REWRITE_TAC[REAL_LE_LT, REAL_LT_INV_EQ, REAL_INV_EQ_0] THEN
  MESON_TAC[REAL_INV_EQ_0]);;

val REAL_LE_INV = store_thm("REAL_LE_INV",
 Term `!x. 0 <= x ==> 0 <= inv(x)`,
  REWRITE_TAC[REAL_LE_INV_EQ]);;

val REAL_LE_ADDR = store_thm("REAL_LE_ADDR",
  (--`!x y. x <= x + y = 0 <= y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`0`--), (--`y:real`--)] REAL_LE_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]);

val REAL_LE_ADDL = store_thm("REAL_LE_ADDL",
  (--`!x y. y <= x + y = 0 <= x`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LE_ADDR);

val REAL_LT_ADDR = store_thm("REAL_LT_ADDR",
  (--`!x y. x < x + y = 0 < y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`0`--), (--`y:real`--)] REAL_LT_LADD)) THEN
  REWRITE_TAC[REAL_ADD_RID]);

val REAL_LT_ADDL = store_thm("REAL_LT_ADDL",
  (--`!x y. y < x + y = 0 < x`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_ADDR);

(*---------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                 *)
(*---------------------------------------------------------------------------*)

val REAL = store_thm("REAL",
  (--`!n. &(SUC n) = &n + &1`--),
  GEN_TAC THEN REWRITE_TAC[real_of_num] THEN
  REWRITE_TAC[REAL_1]);

val REAL_POS = store_thm("REAL_POS",
  (--`!n. 0 <= &n`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`&n`--) THEN ASM_REWRITE_TAC[REAL] THEN
  REWRITE_TAC[REAL_LE_ADDR, REAL_LE_01]);
val _ = export_rewrites ["REAL_POS"]

val REAL_LE = store_thm("REAL_LE",
  (--`!m n. &m <= &n = m <= n`--),
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
   [REAL, REAL_LE_RADD, ZERO_LESS_EQ, LESS_EQ_MONO, REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM NOT_LESS, LESS_0] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&n`--) THEN
    ASM_REWRITE_TAC[ZERO_LESS_EQ, REAL_LE_ADDR, REAL_LE_01],
    DISCH_THEN(MP_TAC o C CONJ (SPEC (--`m:num`--) REAL_POS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
    REWRITE_TAC[REAL_NOT_LE, REAL_LT_ADDR, REAL_LT_01]]);
val _ = export_rewrites ["REAL_LE"]

val REAL_LT = store_thm("REAL_LT",
  (--`!m n. &m < &n = m < n`--),
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC
    ((REWRITE_RULE[] o AP_TERM (--`$~:bool->bool`--) o
    REWRITE_RULE[GSYM NOT_LESS, GSYM REAL_NOT_LT]) (SPEC_ALL REAL_LE)));
val _ = export_rewrites ["REAL_LT"]

val REAL_INJ = store_thm("REAL_INJ",
  (--`!m n. (&m = &n) = (m = n)`--),
  let val th = prove((--`(m:num = n) = m <= n /\ n <= m`--),
                 EQ_TAC THENL
                  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LESS_EQ_REFL],
                   MATCH_ACCEPT_TAC LESS_EQUAL_ANTISYM]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[th, GSYM REAL_LE_ANTISYM, REAL_LE] end);
val _ = export_rewrites ["REAL_INJ"]

val REAL_ADD = store_thm("REAL_ADD",
  (--`!m n. &m + &n = &(m + n)`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL, ADD, REAL_ADD_LID] THEN
  RULE_ASSUM_TAC GSYM THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));
val _ = export_rewrites ["REAL_ADD"]

val REAL_MUL = store_thm("REAL_MUL",
  (--`!m n. &m * &n = &(m * n)`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, MULT_CLAUSES, REAL,
    GSYM REAL_ADD, REAL_RDISTRIB] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);
val _ = export_rewrites ["REAL_MUL"]

(*---------------------------------------------------------------------------*)
(* Now more theorems                                                         *)
(*---------------------------------------------------------------------------*)

val REAL_INV1 = store_thm("REAL_INV1",
  (--`inv(&1) = &1`--),
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_OVER1 = store_thm("REAL_OVER1",
  (--`!x. x / &1 = x`--),
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_INV1, REAL_MUL_RID]);
val _ = export_rewrites ["REAL_OVER1"]

val REAL_DIV_REFL = store_thm("REAL_DIV_REFL",
  (--`!x. ~(x = 0) ==> (x / x = &1)`--),
  GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_RINV]);

val REAL_DIV_LZERO = store_thm("REAL_DIV_LZERO",
  (--`!x. 0 / x = 0`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_LZERO]);

val REAL_LT_NZ = store_thm("REAL_LT_NZ",
  (--`!n. ~(&n = 0) = (0 < &n)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_CASES_TAC (--`&n = 0`--) THEN ASM_REWRITE_TAC[REAL_LE_REFL, REAL_POS]);

val REAL_NZ_IMP_LT = store_thm("REAL_NZ_IMP_LT",
  (--`!n. ~(n = 0) ==> 0 < &n`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_INJ, REAL_LT_NZ]);

val REAL_LT_RDIV_0 = store_thm("REAL_LT_RDIV_0",
  (--`!y z. 0 < z ==> (0 < (y / z) = 0 < y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL_0 THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);

val REAL_LT_RDIV = store_thm("REAL_LT_RDIV",
  (--`!x y z. 0 < z ==> ((x / z) < (y / z) = x < y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
  MATCH_MP_TAC REAL_INV_POS THEN POP_ASSUM ACCEPT_TAC);

val REAL_LT_FRACTION_0 = store_thm("REAL_LT_FRACTION_0",
  (--`!n d. ~(n = 0) ==> (0 < (d / &n) = 0 < d)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_RDIV_0 THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_NZ, REAL_INJ]);

val REAL_LT_MULTIPLE = store_thm("REAL_LT_MULTIPLE",
  (--`!(n:num) d. 1 < n ==> (d < (&n * d) = 0 < d)`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[num_CONV (--`1:num`--), NOT_LESS_0],
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC (--`1 < n:num`--) THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[REAL, REAL_LDISTRIB, REAL_MUL_RID, REAL_LT_ADDL] THEN
      MATCH_MP_TAC REAL_LT_RMUL_0 THEN REWRITE_TAC[REAL_LT] THEN
      MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`1:num`--) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[num_CONV (--`1:num`--), LESS_0],
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LESS_LEMMA1) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL, REAL_LDISTRIB, REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_LT_ADDL]]]);

val REAL_LT_FRACTION = store_thm("REAL_LT_FRACTION",
  (--`!(n:num) d. 1<n ==> ((d / &n) < d = 0 < d)`--),
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`n = 0:num`--) THEN
  ASM_REWRITE_TAC[NOT_LESS_0] THEN DISCH_TAC THEN
  UNDISCH_TAC (--`1 < n:num`--) THEN
  FIRST_ASSUM(fn th => let val th1 = REWRITE_RULE[GSYM REAL_INJ] th in
    MAP_EVERY ASSUME_TAC [th1, REWRITE_RULE[REAL_LT_NZ] th1] end) THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o LAND_CONV)
                                    [GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LT_MULTIPLE);

val REAL_LT_HALF1 = store_thm("REAL_LT_HALF1",
  (--`!d. 0 < (d / &2) = 0 < d`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION_0 THEN
  REWRITE_TAC[num_CONV (--`2:num`--), NOT_SUC]);

val REAL_LT_HALF2 = store_thm("REAL_LT_HALF2",
  (--`!d. (d / &2) < d = 0 < d`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_FRACTION THEN
  CONV_TAC(RAND_CONV num_CONV) THEN
  REWRITE_TAC[LESS_SUC_REFL]);

val REAL_DOUBLE = store_thm("REAL_DOUBLE",
  (--`!x. x + x = &2 * x`--),
  GEN_TAC THEN REWRITE_TAC[num_CONV (--`2:num`--), REAL] THEN
  REWRITE_TAC[REAL_RDISTRIB, REAL_MUL_LID]);

val REAL_DIV_LMUL = store_thm("REAL_DIV_LMUL",
  (--`!x y. ~(y = 0) ==> (y * (x / y) = x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[REAL_MUL_RID]);

val REAL_DIV_RMUL = store_thm("REAL_DIV_RMUL",
  (--`!x y. ~(y = 0) ==> ((x / y) * y = x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC REAL_DIV_LMUL);

val REAL_HALF_DOUBLE = store_thm("REAL_HALF_DOUBLE",
  (--`!x. (x / &2) + (x / &2) = x`--),
  GEN_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV num_EQ_CONV) THEN REWRITE_TAC[]);

val REAL_DOWN = store_thm("REAL_DOWN",
  (--`!x. 0 < x ==> ?y. 0 < y /\ y < x`--),
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (--`x / &2`--) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1, REAL_LT_HALF2]);

val REAL_DOWN2 = store_thm("REAL_DOWN2",
  (--`!x y. 0 < x /\ 0 < y ==> ?z. 0 < z /\ z < x /\ z < y`--),
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THENL
   [ASM_REWRITE_TAC[REAL_DOWN],
    DISCH_THEN(X_CHOOSE_TAC (--`z:real`--) o MATCH_MP REAL_DOWN o CONJUNCT1),
    DISCH_THEN(X_CHOOSE_TAC (--`z:real`--) o MATCH_MP REAL_DOWN o CONJUNCT2)] THEN
  EXISTS_TAC (--`z:real`--) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_TRANS THENL
   [EXISTS_TAC (--`x:real`--), EXISTS_TAC (--`y:real`--)] THEN
  ASM_REWRITE_TAC[]);

val REAL_SUB_SUB = store_thm("REAL_SUB_SUB",
  (--`!x y. (x - y) - x = ~y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + c = (c + a) + b`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_LT_ADD_SUB = store_thm("REAL_LT_ADD_SUB",
  (--`!x y z. (x + y) < z = x < (z - y)`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`z - y`--), (--`y:real`--)]
                       REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD]);

val REAL_LT_SUB_RADD = store_thm("REAL_LT_SUB_RADD",
  (--`!x y z. (x - y) < z = x < z + y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x - y`--), (--`z:real`--), (--`y:real`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_SUB_ADD]);

val REAL_LT_SUB_LADD = store_thm("REAL_LT_SUB_LADD",
  (--`!x y z. x < (y - z) = (x + z) < y`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`x + z`--), (--`y:real`--), (--`~z`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_RID]);

val REAL_LE_SUB_LADD = store_thm("REAL_LE_SUB_LADD",
  (--`!x y z. x <= (y - z) = (x + z) <= y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT, REAL_LT_SUB_RADD]);

val REAL_LE_SUB_RADD = store_thm("REAL_LE_SUB_RADD",
  (--`!x y z. (x - y) <= z = x <= z + y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT, REAL_LT_SUB_LADD]);

val REAL_LT_NEG = store_thm("REAL_LT_NEG",
  (--`!x y. ~x < ~y = y < x`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL[(--`~x`--), (--`~y`--), (--`x + y`--)] REAL_LT_RADD)) THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_LID]);
val _ = export_rewrites ["REAL_LT_NEG"]

val REAL_LE_NEG = store_thm("REAL_LE_NEG",
  (--`!x y. ~x <= ~y = y <= x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_LT_NEG]);
val _ = export_rewrites ["REAL_LE_NEG"]

val REAL_ADD2_SUB2 = store_thm("REAL_ADD2_SUB2",
  (--`!a b c d. (a + b) - (c + d) = (a - c) + (b - d)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val REAL_SUB_LZERO = store_thm("REAL_SUB_LZERO",
  (--`!x. 0 - x = ~x`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, REAL_ADD_LID]);
val _ = export_rewrites ["REAL_SUB_LZERO"]

val REAL_SUB_RZERO = store_thm("REAL_SUB_RZERO",
  (--`!x. x - 0 = x`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_0, REAL_ADD_RID]);
val _ = export_rewrites ["REAL_SUB_RZERO"]

val REAL_LET_ADD2 = store_thm("REAL_LET_ADD2",
  (--`!w x y z. w <= x /\ y < z ==> (w + y) < (x + z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC (--`w + z`--) THEN
  ASM_REWRITE_TAC[REAL_LE_RADD, REAL_LT_LADD]);

val REAL_LTE_ADD2 = store_thm("REAL_LTE_ADD2",
  (--`!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_ACCEPT_TAC REAL_LET_ADD2);

val REAL_LET_ADD = store_thm("REAL_LET_ADD",
  (--`!x y. 0 <= x /\ 0 < y ==> 0 < (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(SPEC (--`0`--) REAL_ADD_LID)) THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN
  ASM_REWRITE_TAC[]);

val REAL_LTE_ADD = store_thm("REAL_LTE_ADD",
  (--`!x y. 0 < x /\ 0 <= y ==> 0 < (x + y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBST1_TAC(SYM(SPEC (--`0`--) REAL_ADD_LID)) THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN
  ASM_REWRITE_TAC[]);

val REAL_LT_MUL2 = store_thm("REAL_LT_MUL2",
  (--`!x1 x2 y1 y2. 0 <= x1 /\ 0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN (--`!a b c d.
    (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))`--)
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      (--`(a + b) + (c + d) = (b + c) + (a + d)`--)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID],
    DISCH_THEN(fn th => ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, GSYM REAL_SUB_RDISTRIB] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x1:real`--) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);

val REAL_LT_INV = store_thm("REAL_LT_INV",
  (--`!x y. 0 < x /\ x < y ==> inv y < inv x`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN (--`0 < y`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`0 < (x * y)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`(inv y) < (inv x) =
                ((x * y) * (inv y)) < ((x * y) * (inv x))`--) SUBST1_TAC
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN (--`(x * (inv x) = &1) /\ (y * (inv y) = &1)`--)
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`x * (y * z) = (x * z) * y`--)] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);

val REAL_SUB_LNEG = store_thm("REAL_SUB_LNEG",
  (--`!x y. ~x - y = ~(x + y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD]);

val REAL_SUB_RNEG = store_thm("REAL_SUB_RNEG",
  (--`!x y. x - ~y = x + y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, REAL_NEGNEG]);

val REAL_SUB_NEG2 = store_thm("REAL_SUB_NEG2",
  (--`!x y. ~x - ~y = y - x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SUB_LNEG] THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL_SUB_TRIANGLE = store_thm("REAL_SUB_TRIANGLE",
  (--`!a b c. (a - b) + (b - c) = a - c`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + (c + d) = (b + c) + (a + d)`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val REAL_EQ_SUB_LADD = store_thm("REAL_EQ_SUB_LADD",
  (--`!x y z. (x = y - z) = (x + z = y)`--),
  REPEAT GEN_TAC THEN (SUBST1_TAC o SYM o C SPECL REAL_EQ_RADD)
   [(--`x:real`--), (--`y - z`--), (--`z:real`--)] THEN REWRITE_TAC[REAL_SUB_ADD]);

val REAL_EQ_SUB_RADD = store_thm("REAL_EQ_SUB_RADD",
  (--`!x y z. (x - y = z) = (x = z + y)`--),
  REPEAT GEN_TAC THEN CONV_TAC(SUB_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC REAL_EQ_SUB_LADD);

val REAL_INV_MUL = store_thm("REAL_INV_MUL",
  (--`!x y. ~(x = 0) /\ ~(y = 0) ==>
             (inv(x * y) = inv(x) * inv(y))`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`(a * b) * (c * d) = (c * a) * (d * b)`--)] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  BINOP_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]);

(* Stronger version
val REAL_INV_MUL = store_thm("REAL_INV_MUL",
 Term`!x y. inv(x * y) = inv(x) * inv(y)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [Term`x = 0`, Term`y = 0`] THEN
  ASM_REWRITE_TAC[REAL_INV_0, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
  ONCE_REWRITE_TAC
     [AC REAL_MUL_AC (Term`(a * b) * (c * d) = (a * c) * (b * d)`)] THEN
  EVERY_ASSUM(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[REAL_MUL_LID])
*)

val REAL_LE_LMUL = store_thm("REAL_LE_LMUL",
  (--`!x y z. 0 < x ==> ((x * y) <= (x * z) = y <= z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]);

val REAL_LE_RMUL = store_thm("REAL_LE_RMUL",
  (--`!x y z. 0 < z ==> ((x * z) <= (y * z) = x <= y)`--),
   REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MATCH_ACCEPT_TAC REAL_LE_LMUL);

val REAL_SUB_INV2 = store_thm("REAL_SUB_INV2",
  (--`!x y. ~(x = 0) /\ ~(y = 0) ==>
                (inv(x) - inv(y) = (y - x) / (x * y))`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div, REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN (--`inv(x * y) = inv(x) * inv(y)`--) SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  EVERY_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_SUB_SUB2 = store_thm("REAL_SUB_SUB2",
  (--`!x y. x - (x - y) = y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEGNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_NEG_SUB, REAL_SUB_SUB]);

val REAL_ADD_SUB2 = store_thm("REAL_ADD_SUB2",
  (--`!x y. x - (x + y) = ~y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_ADD_SUB]);

val REAL_MEAN = store_thm("REAL_MEAN",
  (--`!x y. x < y ==> ?z. x < z /\ z < y`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_DOWN o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT])
  THEN DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`x + d`--) THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ASM_REWRITE_TAC[GSYM REAL_LT_SUB_LADD]);

val REAL_EQ_LMUL2 = store_thm("REAL_EQ_LMUL2",
  (--`!x y z. ~(x = 0) ==> ((y = z) = (x * y = x * z))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`x:real`--), (--`y:real`--), (--`z:real`--)] REAL_EQ_LMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN REFL_TAC);

val REAL_LE_MUL2 = store_thm("REAL_LE_MUL2",
  (--`!x1 x2 y1 y2.
    (& 0) <= x1 /\ (& 0) <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
    (x1 * y1) <= (x2 * y2)`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LE_LT) THEN
  ASM_CASES_TAC (--`x1:real = x2`--) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [UNDISCH_TAC (--`0 <= x2`--) THEN
    DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
     [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]),
      SUBST1_TAC(SYM(ASSUME (--`0 = x2`--))) THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]], ALL_TAC] THEN
  UNDISCH_TAC (--`y1 <= y2`--) THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC (--`0 <= y1`--) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    SUBST1_TAC(SYM(ASSUME (--`0 = y2`--))) THEN
    REWRITE_TAC[REAL_MUL_RZERO, REAL_LE_REFL]]);

val REAL_LE_LDIV = store_thm("REAL_LE_LDIV",
  (--`!x y z. 0 < x /\ y <= (z * x) ==> (y / x) <= z`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  SUBGOAL_THEN (--`y = (y / x) * x`--) MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
    DISCH_THEN(fn t => GEN_REWR_TAC (funpow 2 LAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL THEN POP_ASSUM ACCEPT_TAC]);

val REAL_LE_RDIV = store_thm("REAL_LE_RDIV",
  (--`!x y z. 0 < x /\ (y * x) <= z ==> y <= (z / x)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  SUBGOAL_THEN (--`z = (z / x) * x`--) MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC,
    DISCH_THEN(fn t => GEN_REWR_TAC (LAND_CONV o RAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL THEN POP_ASSUM ACCEPT_TAC]);

val REAL_LT_DIV = store_thm("REAL_LT_DIV",
 Term`!x y. 0 < x /\ 0 < y ==> 0 < x / y`,
 REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ]);

val REAL_LE_DIV = store_thm("REAL_LE_DIV",
 Term`!x y. 0 <= x /\ 0 <= y ==> 0 <= x / y`,
 REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ]);

val REAL_LT_1 = store_thm("REAL_LT_1",
  (--`!x y. 0 <= x /\ x < y ==> (x / y) < &1`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(x / y) < &1 = ((x / y) * y) < (&1 * y)`--) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[],
    SUBGOAL_THEN (--`(x / y) * y = x`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[REAL_MUL_LID]]]);

val REAL_LE_LMUL_IMP = store_thm("REAL_LE_LMUL_IMP",
  (--`!x y z. 0 <= x /\ y <= z ==> (x * y) <= (x * z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]),
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_ACCEPT_TAC REAL_LE_REFL]);

val REAL_LE_RMUL_IMP = store_thm("REAL_LE_RMUL_IMP",
  (--`!x y z. 0 <= x /\ y <= z ==> (y * x) <= (z * x)`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_LE_LMUL_IMP);

val REAL_EQ_IMP_LE = store_thm("REAL_EQ_IMP_LE",
  (--`!x y. (x = y) ==> x <= y`--),
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC REAL_LE_REFL);

val REAL_INV_LT1 = store_thm("REAL_INV_LT1",
  (--`!x. 0 < x /\ x < &1 ==> &1 < inv(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_INV_POS) THEN
  GEN_REWR_TAC I [TAUT_CONV (--`a = ~~a:bool`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [(--`inv(x)`--), (--`&1`--), (--`x:real`--), (--`&1`--)] REAL_LT_MUL2) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`0 < 0`--) THEN
      REWRITE_TAC[REAL_LT_REFL]],
    DISCH_THEN(MP_TAC o AP_TERM (--`inv`--)) THEN REWRITE_TAC[REAL_INV1] THEN
    SUBGOAL_THEN (--`inv(inv x) = x`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`&1 < &1`--) THEN
      REWRITE_TAC[REAL_LT_REFL]]]);

val REAL_POS_NZ = store_thm("REAL_POS_NZ",
  (--`!x. 0 < x ==> ~(x = 0)`--),
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_LT_IMP_NE) THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN POP_ASSUM ACCEPT_TAC);

val REAL_EQ_RMUL_IMP = store_thm("REAL_EQ_RMUL_IMP",
  (--`!x y z. ~(z = 0) /\ (x * z = y * z) ==> (x = y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[REAL_EQ_RMUL]);

val REAL_EQ_LMUL_IMP = store_thm("REAL_EQ_LMUL_IMP",
  (--`!x y z. ~(x = 0) /\ (x * y = x * z) ==> (y = z)`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EQ_RMUL_IMP);

val REAL_FACT_NZ = store_thm("REAL_FACT_NZ",
  (--`!n. ~(&(FACT n) = 0)`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
  REWRITE_TAC[REAL_LT, FACT_LESS]);

val REAL_DIFFSQ = store_thm("REAL_DIFFSQ",
  (--`!x y. (x + y) * (x - y) = (x * x) - (y * y)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_LDISTRIB, REAL_RDISTRIB, real_sub, GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`a + (b + (c + d)) = (b + c) + (a + d)`--)] THEN
  REWRITE_TAC[REAL_ADD_LID_UNIQ, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_LNEG_UNIQ] THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);

val REAL_POSSQ = store_thm("REAL_POASQ",
  (--`!x. 0 < (x * x) = ~(x = 0)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C CONJ (SPEC (--`x:real`--) REAL_LE_SQUARE)) THEN
    REWRITE_TAC[REAL_LE_ANTISYM, REAL_ENTIRE],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]]);

val REAL_SUMSQ = store_thm("REAL_SUMSQ",
  (--`!x y. ((x * x) + (y * y) = 0) = (x = 0) /\ (y = 0)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISCH_THEN DISJ_CASES_TAC THEN MATCH_MP_TAC REAL_POS_NZ THENL
     [MATCH_MP_TAC REAL_LTE_ADD, MATCH_MP_TAC REAL_LET_ADD] THEN
    ASM_REWRITE_TAC[REAL_POSSQ, REAL_LE_SQUARE],
    DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID]]);

val REAL_EQ_NEG = store_thm("REAL_EQ_NEG",
  (--`!x y. (~x = ~y) = (x = y)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM, REAL_LE_NEG] THEN
  MATCH_ACCEPT_TAC CONJ_SYM);

val REAL_DIV_MUL2 = store_thm("REAL_DIV_MUL2",
  (--`!x z. ~(x = 0) /\ ~(z = 0) ==> !y. y / z = (x * y) / (x * z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`(a * b) * (c * d) = (c * a) * (b * d)`--)] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID]);

val REAL_MIDDLE1 = store_thm("REAL_MIDDLE1",
  (--`!a b. a <= b ==> a <= (a + b) / &2`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_RDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE, REAL_LE_LADD] THEN
  REWRITE_TAC[num_CONV (--`2:num`--), REAL_LT, LESS_0]);

val REAL_MIDDLE2 = store_thm("REAL_MIDDLE2",
  (--`!a b. a <= b ==> ((a + b) / &2) <= b`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LDIV THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_DOUBLE] THEN
  ASM_REWRITE_TAC[GSYM REAL_DOUBLE, REAL_LE_RADD] THEN
  REWRITE_TAC[num_CONV (--`2:num`--), REAL_LT, LESS_0]);

(*---------------------------------------------------------------------------*)
(* Define usual norm (absolute distance) on the real line                    *)
(*---------------------------------------------------------------------------*)

val abs = new_definition("abs",
  (--`abs(x) = (if (0 <= x) then x else ~x)`--));

val ABS_ZERO = store_thm("ABS_ZERO",
  (--`!x. (abs(x) = 0) = (x = 0)`--),
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_NEG_EQ0]);

val ABS_0 = store_thm("ABS_0",
  (--`abs(0) = 0`--),
  REWRITE_TAC[ABS_ZERO]);

val ABS_1 = store_thm("ABS_1",
  (--`abs(&1) = &1`--),
  REWRITE_TAC[abs, REAL_LE, ZERO_LESS_EQ]);

val ABS_NEG = store_thm("ABS_NEG",
  (--`!x. abs~x = abs(x)`--),
  GEN_TAC THEN REWRITE_TAC[abs, REAL_NEGNEG, REAL_NEG_GE0] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MP_TAC(CONJ (ASSUME (--`0 <= x`--)) (ASSUME (--`x <= 0`--))) THEN
    REWRITE_TAC[REAL_LE_ANTISYM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_NEG_0],
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    W(MP_TAC o end_itlist CONJ o map ASSUME o fst) THEN
    REWRITE_TAC[REAL_LT_ANTISYM]]);

val ABS_TRIANGLE = store_thm("ABS_TRIANGLE",
  (--`!x y. abs(x + y) <= abs(x) + abs(y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[abs] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_NEG_ADD, REAL_LE_REFL, REAL_LE_LADD, REAL_LE_RADD] THEN
  ASM_REWRITE_TAC[GSYM REAL_NEG_ADD, REAL_LE_NEGL, REAL_LE_NEGR] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(UNDISCH_TAC (--`(x + y) < 0`--)) THEN SUBST1_TAC(SYM(SPEC (--`0`--) REAL_ADD_LID))
  THEN REWRITE_TAC[REAL_NOT_LT] THEN
  MAP_FIRST MATCH_MP_TAC [REAL_LT_ADD2, REAL_LE_ADD2] THEN
  ASM_REWRITE_TAC[]);

val ABS_POS = store_thm("ABS_POS",
  (--`!x. 0 <= abs(x)`--),
  GEN_TAC THEN ASM_CASES_TAC (--`0 <= x`--) THENL
   [ALL_TAC,
    MP_TAC(SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[abs]);

val ABS_MUL = store_thm("ABS_MUL",
  (--`!x y. abs(x * y) = abs(x) * abs(y)`--),
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`0 <= x`--) THENL
   [ALL_TAC,
    MP_TAC(SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
    GEN_REWR_TAC LAND_CONV  [GSYM ABS_NEG] THEN
    GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [GSYM ABS_NEG]
    THEN REWRITE_TAC[REAL_NEG_LMUL]] THEN
  (ASM_CASES_TAC (--`0 <= y`--) THENL
    [ALL_TAC,
     MP_TAC(SPEC (--`y:real`--) REAL_LE_NEGTOTAL) THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
     GEN_REWR_TAC LAND_CONV  [GSYM ABS_NEG] THEN
     GEN_REWR_TAC (RAND_CONV o RAND_CONV)
                     [GSYM ABS_NEG] THEN
     REWRITE_TAC[REAL_NEG_RMUL]]) THEN
  ASSUM_LIST(ASSUME_TAC o MATCH_MP REAL_LE_MUL o LIST_CONJ o rev) THEN
  ASM_REWRITE_TAC[abs]);

val ABS_LT_MUL2 = store_thm("ABS_LT_MUL2",
  (--`!w x y z. abs(w) < y /\ abs(x) < z ==> abs(w * x) < (y * z)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_REWRITE_TAC[ABS_POS]);

val ABS_SUB = store_thm("ABS_SUB",
  (--`!x y. abs(x - y) = abs(y - x)`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_NEG_SUB] THEN
  REWRITE_TAC[ABS_NEG]);

val ABS_NZ = store_thm("ABS_NZ",
  (--`!x. ~(x = 0) = 0 < abs(x)`--),
  GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABS_ZERO] THEN
    REWRITE_TAC[TAUT_CONV (--`~a ==> b = b \/ a`--)] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM REAL_LE_LT, ABS_POS],
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[abs, REAL_LT_REFL, REAL_LE_REFL]]);

val ABS_INV = store_thm("ABS_INV",
  (--`!x. ~(x = 0) ==> (abs(inv x) = inv(abs(x)))`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LINV_UNIQ THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_LINV th]) THEN
  REWRITE_TAC[abs, REAL_LE] THEN
  REWRITE_TAC[num_CONV (--`1:num`--), GSYM NOT_LESS, NOT_LESS_0]);

val ABS_ABS = store_thm("ABS_ABS",
  (--`!x. abs(abs(x)) = abs(x)`--),
  GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV  [abs] THEN
  REWRITE_TAC[ABS_POS]);

val ABS_LE = store_thm("ABS_LE",
  (--`!x. x <= abs(x)`--),
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_LE_NEGR] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_NOT_LE]);

val ABS_REFL = store_thm("ABS_REFL",
  (--`!x. (abs(x) = x) = 0 <= x`--),
  GEN_TAC THEN REWRITE_TAC[abs] THEN
  ASM_CASES_TAC (--`0 <= x`--) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  REWRITE_TAC[REAL_DOUBLE, REAL_ENTIRE, REAL_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV num_EQ_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_LE_REFL]);

val ABS_N = store_thm("ABS_N",
  (--`!n. abs(&n) = &n`--),
  GEN_TAC THEN REWRITE_TAC[ABS_REFL, REAL_LE, ZERO_LESS_EQ]);

val ABS_BETWEEN = store_thm("ABS_BETWEEN",
  (--`!x y d. 0 < d /\ ((x - d) < y) /\ (y < (x + d)) = abs(y - x) < d`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[abs] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN REWRITE_TAC[REAL_NEG_SUB] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_SUB_RADD] THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [REAL_ADD_SYM] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN (--`x < (x + d)`--) MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`y:real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`y:real`--) THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR],
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN (--`y < (y + d)`--) MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_ADDR] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR]]);

val ABS_BOUND = store_thm("ABS_BOUND",
  (--`!x y d. abs(x - y) < d ==> y < (x + d)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  ONCE_REWRITE_TAC[GSYM ABS_BETWEEN] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);

val ABS_STILLNZ = store_thm("ABS_STILLNZ",
  (--`!x y. abs(x - y) < abs(y) ==> ~(x = 0)`--),
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG, REAL_LT_REFL]);

val ABS_CASES = store_thm("ABS_CASES",
  (--`!x. (x = 0) \/ 0 < abs(x)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
  BOOL_CASES_TAC (--`x = 0`--) THEN ASM_REWRITE_TAC[]);

val ABS_BETWEEN1 = store_thm("ABS_BETWEEN1",
  (--`!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z`--),
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LET_TOTAL) THENL
   [ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
    REWRITE_TAC[real_sub, REAL_LT_RADD] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2),
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[]]);

val ABS_SIGN = store_thm("ABS_SIGN",
  (--`!x y. abs(x - y) < y ==> 0 < x`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ABS_BOUND) THEN
  REWRITE_TAC[REAL_LT_ADDL]);

val ABS_SIGN2 = store_thm("ABS_SIGN2",
  (--`!x y. abs(x - y) < ~y ==> x < 0`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`~x`--), (--`~y`--)] ABS_SIGN) THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0, REAL_NEGNEG]);

val ABS_DIV = store_thm("ABS_DIV",
  (--`!y. ~(y = 0) ==> !x. abs(x / y) = abs(x) / abs(y)`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[real_div] THEN
  REWRITE_TAC[ABS_MUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]));

val ABS_CIRCLE = store_thm("ABS_CIRCLE",
  (--`!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(x) + abs(h)`--) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN
  POP_ASSUM(MP_TAC o CONJ (SPEC (--`abs(x)`--) REAL_LE_REFL)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD2) THEN
  REWRITE_TAC[REAL_SUB_ADD2]);

val REAL_SUB_ABS = store_thm("REAL_SUB_ABS",
  (--`!x y. (abs(x) - abs(y)) <= abs(x - y)`--),
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`(abs(x - y) + abs(y)) - abs(y)`--) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[real_sub] THEN REWRITE_TAC[REAL_LE_RADD] THEN
    SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`y:real`--)] REAL_SUB_ADD)) THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)  [REAL_SUB_ADD] THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE,
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_ADD_SUB, REAL_LE_REFL]]);

val ABS_SUB_ABS = store_thm("ABS_SUB_ABS",
  (--`!x y. abs(abs(x) - abs(y)) <= abs(x - y)`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)  [abs] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_SUB_ABS] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN
  REWRITE_TAC[REAL_SUB_ABS]);

val ABS_BETWEEN2 = store_thm("ABS_BETWEEN2",
  (--`!x0 x y0 y.
        x0 < y0 /\
        abs(x - x0) < (y0 - x0) / &2 /\
        abs(y - y0) < (y0 - x0) / &2
        ==> x < y`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`x < y0 /\ x0 < y`--) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [(--`x0:real`--), (--`x:real`--),
                    (--`y0 - x0`--)] ABS_BOUND) THEN
      REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[ABS_SUB] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC (--`(y0 - x0) / &2`--) THEN
      ASM_REWRITE_TAC[REAL_LT_HALF2] THEN
      ASM_REWRITE_TAC[REAL_SUB_LT],
      GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a:bool`--)] THEN
      PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
       (--`(y0 + ~x0) + (x0 + ~y) = (~x0 + x0) + (y0 + ~y)`--)) THEN
      REWRITE_TAC[GSYM real_sub, REAL_ADD_LINV, REAL_ADD_LID] THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [(--`y0 - x0`--),
                    (--`x0 - y`--)] REAL_LE_ADDR) THEN
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN (--`~(y0 <= y)`--) ASSUME_TAC THENL
       [REWRITE_TAC[REAL_NOT_LE] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`y0 - x0`--) THEN
        ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_SUB_LT], ALL_TAC] THEN
      UNDISCH_TAC (--`abs(y - y0) < (y0 - x0) / &2`--) THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_NEG_SUB] THEN DISCH_TAC THEN
      SUBGOAL_THEN (--`(y0 - x0) < (y0 - x0) / &2`--)
                   MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (--`y0 - y`--) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[REAL_LT_HALF2] THEN ASM_REWRITE_TAC[REAL_SUB_LT]],
    ALL_TAC] THEN
  GEN_REWR_TAC I  [TAUT_CONV (--`a = ~~a:bool`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`abs(x0 - y) < (y0 - x0) / &2`--) ASSUME_TAC
  THENL
   [REWRITE_TAC[abs, REAL_SUB_LE] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`x - x0`--) THEN
    REWRITE_TAC[real_sub, REAL_LE_RADD] THEN
    ASM_REWRITE_TAC[GSYM real_sub] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`abs(x - x0)`--) THEN
    ASM_REWRITE_TAC[ABS_LE], ALL_TAC] THEN
  SUBGOAL_THEN
      (--`abs(y0 - x0) < ((y0 - x0) / &2) + ((y0 - x0) / &2)`--)
      MP_TAC
  THENL
   [ALL_TAC,
    REWRITE_TAC[REAL_HALF_DOUBLE, REAL_NOT_LT, ABS_LE]] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`abs(y0 - y) + abs(y - x0)`--) THEN
  CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_LT_ADD2 THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN (--`y0 - x0 = (y0 - y) + (y - x0)`--) SUBST1_TAC THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN
  REWRITE_TAC[real_sub] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`(a + b) + (c + d) = (b + c) + (a + d)`--)] THEN
  REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]);

val ABS_BOUNDS = store_thm("ABS_BOUNDS",
  (--`!x k. abs(x) <= k = ~k <= x /\ x <= k`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_LE_NEG] THEN
  REWRITE_TAC[REAL_NEGNEG] THEN REWRITE_TAC[abs] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[TAUT_CONV (--`(a = b /\ a) = a ==> b`--)] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[REAL_LE_NEGL],
    REWRITE_TAC[TAUT_CONV (--`(a = a /\ b) = a ==> b`--)] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`~x`--) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_NEGR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE]]);

(*---------------------------------------------------------------------------*)
(* Define integer powers                                                     *)
(*---------------------------------------------------------------------------*)

val pow = new_recursive_definition
  {name = "pow",
   def = (--`($pow x 0 = &1) /\ ($pow x (SUC n) = x * ($pow x n))`--),
   rec_axiom = num_Axiom}

val _ = set_fixity "pow" (Infixr 700);

val POW_0 = store_thm("POW_0",
  (--`!n. 0 pow (SUC n) = 0`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_MUL_LZERO]);

val POW_NZ = store_thm("POW_NZ",
  (--`!c n. ~(c = 0) ==> ~(c pow n = 0)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[pow, REAL_10, REAL_ENTIRE]);

val POW_INV = store_thm("POW_INV",
  (--`!c. ~(c = 0) ==> !n. (inv(c pow n) = (inv c) pow n)`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[pow, REAL_INV1] THEN
  MP_TAC(SPECL [(--`c:real`--), (--`c pow n`--)] REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN (--`~(c pow n = 0)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC POW_NZ THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[]);

val POW_ABS = store_thm("POW_ABS",
  (--`!c n. abs(c) pow n = abs(c pow n)`--),
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, ABS_1, ABS_MUL]);

val POW_PLUS1 = store_thm("POW_PLUS1",
  (--`!e. 0 < e ==> !n. (&1 + (&n * e)) <= (&1 + e) pow n`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`(&1 + e) * (&1 + (&n * e))`--) THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LDISTRIB, REAL_RDISTRIB, REAL, REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_RID, REAL_ADD_ASSOC, REAL_LE_ADDR] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ALL_TAC, MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
    SUBGOAL_THEN (--`0 < (&1 + e)`--)
      (fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LE_LMUL th]) THEN
    GEN_REWR_TAC LAND_CONV  [GSYM REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT] THEN REWRITE_TAC[num_CONV (--`1:num`--), LESS_0]]);

val POW_ADD = store_thm("POW_ADD",
  (--`!c m n. c pow (m + n) = (c pow m) * (c pow n)`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, ADD_CLAUSES, REAL_MUL_RID] THEN
  CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)));

val POW_1 = store_thm("POW_1",
  (--`!x. x pow 1 = x`--),
  GEN_TAC THEN REWRITE_TAC[num_CONV (--`1:num`--)] THEN
  REWRITE_TAC[pow, REAL_MUL_RID]);

val POW_2 = store_thm("POW_2",
  (--`!x. x pow 2 = x * x`--),
  GEN_TAC THEN REWRITE_TAC[num_CONV (--`2:num`--)] THEN
  REWRITE_TAC[pow, POW_1]);

val POW_ONE = store_thm("POW_ONE",
 Term`!n. &1 pow n = &1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[pow, REAL_MUL_LID]);

val POW_POS = store_thm("POW_POS",
  (--`!x. 0 <= x ==> !n. 0 <= (x pow n)`--),
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow, REAL_LE_01] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);

val POW_LE = store_thm("POW_LE",
  (--`!n x y. 0 <= x /\ x <= y ==> (x pow n) <= (y pow n)`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LE_REFL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

val POW_M1 = store_thm("POW_M1",
  (--`!n. abs(~1 pow n) = 1`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, ABS_NEG, ABS_1] THEN
  ASM_REWRITE_TAC[ABS_MUL, ABS_NEG, ABS_1, REAL_MUL_LID]);

val POW_MUL = store_thm("POW_MUL",
  (--`!n x y. (x * y) pow n = (x pow n) * (y pow n)`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_MUL_LID] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)));

val REAL_LE_POW2 = store_thm("REAL_LE_POW2",
  (--`!x. 0 <= x pow 2`--),
  GEN_TAC THEN REWRITE_TAC[POW_2, REAL_LE_SQUARE]);

val ABS_POW2 = store_thm("ABS_POW2",
  (--`!x. abs(x pow 2) = x pow 2`--),
  GEN_TAC THEN REWRITE_TAC[ABS_REFL, REAL_LE_POW2]);

val REAL_POW2_ABS = store_thm("REAL_POW2_ABS",
  (--`!x. abs(x) pow 2 = x pow 2`--),
  GEN_TAC THEN REWRITE_TAC[POW_2, POW_MUL] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  REWRITE_TAC[GSYM POW_2, ABS_POW2]);

val REAL_LE1_POW2 = store_thm("REAL_LE1_POW2",
  (--`!x. &1 <= x ==> &1 <= (x pow 2)`--),
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01]);

val REAL_LT1_POW2 = store_thm("REAL_LT1_POW2",
  (--`!x. &1 < x ==> &1 < (x pow 2)`--),
  GEN_TAC THEN REWRITE_TAC[POW_2] THEN DISCH_TAC THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01]);

val POW_POS_LT = store_thm("POW_POS_LT",
  (--`!x n. 0 < x ==> 0 < (x pow (SUC n))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[],
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC POW_NZ THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC[]]);

val POW_2_LE1 = store_thm("POW_2_LE1",
  (--`!n. &1 <= &2 pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LE_REFL] THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE] THEN
  REWRITE_TAC[ZERO_LESS_EQ, num_CONV (--`2:num`--), LESS_EQ_SUC_REFL]);

val POW_2_LT = store_thm("POW_2_LT",
  (--`!n. &n < &2 pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LT_01] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, GSYM REAL_DOUBLE] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[POW_2_LE1]);

val POW_MINUS1 = store_thm("POW_MINUS1",
  (--`!n. ~1 pow (2 * n) = 1`--),
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES, pow] THEN
  REWRITE_TAC(map num_CONV [Term`2:num`,Term`1:num`] @ [ADD_CLAUSES]) THEN
  REWRITE_TAC[pow] THEN
  REWRITE_TAC[SYM(num_CONV (--`2:num`--)), SYM(num_CONV (--`1:num`--))] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_NEGNEG]);

val POW_LT = store_thm("POW_LT",
  (--`!n x y. 0 <= x /\ x < y ==> (x pow (SUC n)) < (y pow (SUC n))`--),
  REPEAT STRIP_TAC THEN SPEC_TAC((--`n:num`--),(--`n:num`--))
   THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[pow, REAL_MUL_RID],
    ONCE_REWRITE_TAC[pow] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[]]);

val REAL_POW_LT = store_thm("REAL_POW_LT",
 Term`!x n. 0 < x ==> 0 < (x pow n)`,
  REPEAT STRIP_TAC THEN SPEC_TAC(Term`n:num`,Term`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[pow, REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]);;

val POW_EQ = store_thm("POW_EQ",
  (--`!n x y. 0 <= x /\ 0 <= y /\ (x pow (SUC n) = y pow (SUC n))
        ==> (x = y)`--),
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (--`x pow (SUC n) = y pow (SUC n)`--) THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THENL
   [ALL_TAC, CONV_TAC(RAND_CONV SYM_CONV)] THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  MATCH_MP_TAC POW_LT THEN ASM_REWRITE_TAC[]);

val POW_ZERO = store_thm("POW_ZERO",
  (--`!n x. (x pow n = 0) ==> (x = 0)`--),
  INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[pow] THEN
  REWRITE_TAC[REAL_10, REAL_ENTIRE] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val POW_ZERO_EQ = store_thm("POW_ZERO_EQ",
  (--`!n x. (x pow (SUC n) = 0) = (x = 0)`--),
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POW_ZERO] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[POW_0]);

val REAL_POW_LT2 = store_thm("REAL_POW_LT2",
 Term `!n x y. ~(n = 0) /\ 0 <= x /\ x < y ==> x pow n < y pow n`,
 INDUCT_TAC THEN REWRITE_TAC[NOT_SUC, pow] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC (Term `n = 0:num`) THEN ASM_REWRITE_TAC[pow, REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

val LT_EXISTS = prove
 (Term`!m n. m < n = ?d. n = m + SUC d`,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [IMP_RES_TAC LESS_ADD_1 THEN ASM_REWRITE_TAC[]
     THEN EXISTS_TAC (Term`p:num`) THEN REWRITE_TAC [ADD1],
   ASM_REWRITE_TAC[LESS_ADD_SUC]]);

val REAL_POW_MONO_LT = store_thm("REAL_POW_MONO_LT",
 Term`!m n x. &1 < x /\ m < n ==> x pow m < x pow n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LT_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL_IMP THEN CONJ_TAC THENL
   [SPEC_TAC(Term`d:num`,Term`d:num`) THEN
    INDUCT_TAC THEN ONCE_REWRITE_TAC[pow] THENL
     [ASM_REWRITE_TAC[pow, REAL_MUL_RID], ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
    MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (Term`&1`) THEN
    ASM_REWRITE_TAC[REAL_LT,prim_recTheory.LESS_0, ONE]]);

val REAL_POW_POW = store_thm("REAL_POW_POW",
 Term `!x m n. (x pow m) pow n = x pow (m * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, MULT_CLAUSES, POW_ADD]);;


(*---------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set        *)
(*---------------------------------------------------------------------------*)

val REAL_SUP_SOMEPOS = store_thm("REAL_SUP_SOMEPOS",
  (--`!P. (?x. P x /\ 0 < x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) = y < s)`--),
  let val lemma = TAUT_CONV (--`a /\ b ==> b`--) in
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC (--`\x. P x /\ 0 < x`--) REAL_SUP_ALLPOS) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[lemma] THEN
  SUBGOAL_THEN
  (--`?z. !x. P x /\ 0 < x ==> x < z`--) (SUBST1_TAC o EQT_INTRO)
  THENL
   [POP_ASSUM(X_CHOOSE_TAC (--`z:real`--) o CONJUNCT2) THEN
   EXISTS_TAC (--`z:real`--) THEN
    GEN_TAC THEN
    DISCH_THEN(curry op THEN (FIRST_ASSUM MATCH_MP_TAC) o ASSUME_TAC) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN (--`s:real`--) MP_TAC) THEN
  DISCH_THEN(curry op THEN (EXISTS_TAC (--`s:real`--) THEN GEN_TAC) o
                   (SUBST1_TAC o SYM o SPEC (--`y:real`--))) THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPECL [(--`y:real`--), (--`0`--)]
                                             REAL_LT_TOTAL)
    THENL
     [DISCH_THEN SUBST1_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
      POP_ASSUM(X_CHOOSE_TAC (--`x:real`--) o CONJUNCT1) THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o CONJ th o CONJUNCT2)) THEN
      DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_LT_TRANS) THEN
      DISCH_THEN(K ALL_TAC) THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
      POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN
      EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC (--`y:real`--) THEN ASM_REWRITE_TAC[]],
    DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN
    EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[]] end);

val SUP_LEMMA1 = store_thm("SUP_LEMMA1",
  (--`!P s d. (!y. (?x. (\x. P(x + d)) x /\ y < x) = y < s)
     ==> (!y. (?x. P x /\ y < x) = y < (s + d))`--),
  REPEAT GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  POP_ASSUM(MP_TAC o SPEC (--`y + ~d`--)) THEN
  REWRITE_TAC[REAL_LT_ADDNEG2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THENL
   [EXISTS_TAC (--`x + ~d`--) THEN
    ASM_REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID],
    EXISTS_TAC (--`x + d`--) THEN POP_ASSUM ACCEPT_TAC]);

val SUP_LEMMA2 = store_thm("SUP_LEMMA2",
  (--`!P. (?x. P x) ==> ?d. ?x. (\x. P(x + d)) x /\ 0 < x`--),
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN BETA_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPECL [(--`x:real`--), (--`0`--)]
                                           REAL_LT_TOTAL)
  THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [(--`~1`--), (--`1`--)] THEN
    ASM_REWRITE_TAC[REAL_ADD_RINV, REAL_LT_01],
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [(--`x + x`--), (--`~x`--)] THEN
    ASM_REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID, REAL_NEG_GT0],
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(--`0`--), (--`x:real`--)] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID]]);

val SUP_LEMMA3 = store_thm("SUP_LEMMA3",
  (--`!d. (?z. !x. P x ==> x < z) ==>
                (?z. !x. (\x. P(x + d)) x ==> x < z)`--),
  GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`z:real`--)) THEN
  EXISTS_TAC (--`z + ~d`--) THEN GEN_TAC THEN BETA_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  ASM_REWRITE_TAC[REAL_LT_ADDNEG]);

val REAL_SUP_EXISTS = store_thm("REAL_SUP_EXISTS",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) = y < s)`--),
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC (--`d:real`--) o MATCH_MP SUP_LEMMA2) MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SPEC (--`d:real`--) SUP_LEMMA3)) THEN
  POP_ASSUM(fn th => DISCH_THEN(MP_TAC o MATCH_MP REAL_SUP_SOMEPOS o CONJ th))
  THEN
  DISCH_THEN(X_CHOOSE_TAC (--`s:real`--)) THEN
  EXISTS_TAC (--`s + d`--) THEN
  MATCH_MP_TAC SUP_LEMMA1 THEN POP_ASSUM ACCEPT_TAC);

val sup = new_definition("sup",
  (--`sup P = @s. !y. (?x. P x /\ y < x) = y < s`--));

val REAL_SUP = store_thm("REAL_SUP",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. (?x. P x /\ y < x) = y < sup P)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o SELECT_RULE o MATCH_MP REAL_SUP_EXISTS)
  THEN REWRITE_TAC[GSYM sup]);

val REAL_SUP_UBOUND = store_thm("REAL_SUP_UBOUND",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. P y ==> y <= sup P)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC (--`sup P`--) o MATCH_MP REAL_SUP) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  X_GEN_TAC (--`x:real`--) THEN RULE_ASSUM_TAC(SPEC (--`x:real`--)) THEN
  DISCH_THEN (SUBST_ALL_TAC o EQT_INTRO) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_NOT_LT]);

val SETOK_LE_LT = store_thm("SETOK_LE_LT",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) =
       (?x. P x) /\ (?z. !x. P x ==> x < z)`--),
  GEN_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC (--`z:real`--))
  THENL (map EXISTS_TAC [(--`z + &1`--), (--`z:real`--)]) THEN
  GEN_TAC THEN DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REAL_LT_ADD1, REAL_LT_IMP_LE]);

val REAL_SUP_LE = store_thm("REAL_SUP_LE",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           (!y. (?x. P x /\ y < x) = y < sup P)`--),
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT, REAL_SUP]);

val REAL_SUP_UBOUND_LE = store_thm("REAL_SUP_UBOUND_LE",
  (--`!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
          (!y. P y ==> y <= sup P)`--),
  GEN_TAC THEN REWRITE_TAC[SETOK_LE_LT, REAL_SUP_UBOUND]);

(*---------------------------------------------------------------------------*)
(* Prove the Archimedean property                                            *)
(*---------------------------------------------------------------------------*)

val REAL_ARCH = store_thm("REAL_ARCH",
  (--`!x. 0 < x ==> !y. ?n. y < &n * x`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT_CONV (--`a = ~(~a):bool`--)] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`\z. ?n. z = &n * x`--) REAL_SUP_LE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN(fn th => REWRITE_TAC[th]) o funpow 2 (fst o dest_imp) o snd)
  THENL [CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [(--`&n * x`--), (--`n:num`--)] THEN REFL_TAC,
    EXISTS_TAC (--`y:real`--) THEN GEN_TAC THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC (--`sup(\z. ?n. z = &n * x) - x`--))
  THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC (--`n:num`--)) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWR_TAC (funpow 3 RAND_CONV) [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC (--`sup(\z. ?n. z = &n * x)`--)) THEN
  REWRITE_TAC[REAL_LT_REFL] THEN EXISTS_TAC (--`(&n + &1) * x`--)
  THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC (--`n + 1:num`--) THEN
  REWRITE_TAC[REAL_ADD]);

val REAL_ARCH_LEAST = store_thm("REAL_ARCH_LEAST",
  (--`!y. 0 < y
          ==> !x. 0 <= x
          ==> ?n. (&n * y) <= x
                  /\ x < (&(SUC n) * y)`--),
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP REAL_ARCH) THEN
  GEN_TAC THEN POP_ASSUM(ASSUME_TAC o SPEC (--`x:real`--)) THEN
  POP_ASSUM(X_CHOOSE_THEN (--`n:num`--) MP_TAC o CONV_RULE EXISTS_LEAST_CONV)
  THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SPEC (--`PRE n`--))) THEN
  DISCH_TAC THEN EXISTS_TAC (--`PRE n`--) THEN
  SUBGOAL_THEN (--`SUC(PRE n) = n`--) ASSUME_TAC THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC (CHOOSE_THEN SUBST_ALL_TAC)
        (SPEC (--`n:num`--) num_CASES) THENL
     [UNDISCH_TAC (--`x < 0 * y`--) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO, GSYM REAL_NOT_LE],
      REWRITE_TAC[PRE]],
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PRE, LESS_SUC_REFL]]);

(*---------------------------------------------------------------------------*)
(* Now define finite sums; NB: sum(m,n) f = f(m) + f(m+1) + ... + f(m+n-1)   *)
(*---------------------------------------------------------------------------*)

val sumc = new_recursive_definition
  {name = "sumc",
   def = (--`(sumc n 0 f = 0) /\
               (sumc n (SUC m) f = sumc n m f + f(n + m))`--),
   rec_axiom = num_Axiom}

val SUM_DEF = new_definition("SUM_DEF",
  (--`sum(m,n) f = sumc m n f`--));

val sum = store_thm("sum",
  (--`!f n m. (sum(n,0) f = 0) /\
              (sum(n,SUC m) f = sum(n,m) f + f(n + m))`--),
  REWRITE_TAC[SUM_DEF, sumc]);

(*---------------------------------------------------------------------------*)
(* Useful manipulative theorems for sums                                     *)
(*---------------------------------------------------------------------------*)

val SUM_TWO = store_thm("SUM_TWO",
  (--`!f n p. sum(0,n) f + sum(n,p) f = sum(0,n + p) f`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_ADD_RID, ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_ADD_ASSOC]);

val SUM_DIFF = store_thm("SUM_DIFF",
  (--`!f m n. sum(m,n) f = sum(0,m + n) f - sum(0,m) f`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN MATCH_ACCEPT_TAC SUM_TWO);

val ABS_SUM = store_thm("ABS_SUM",
  (--`!f m n. abs(sum(m,n) f) <= sum(m,n) (\n. abs(f n))`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, ABS_0, REAL_LE_REFL] THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`abs(sum(m,n) f) + abs(f(m + n))`--) THEN
  ASM_REWRITE_TAC[ABS_TRIANGLE, REAL_LE_RADD]);

val SUM_LE = store_thm("SUM_LE",
  (--`!f g m n. (!r. m <= r /\ r < (n + m) ==> f(r) <= g(r))
        ==> (sum(m,n) f <= sum(m,n) g)`--),
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[sum, REAL_LE_REFL] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`n + m:num`--),
    GEN_REWR_TAC (RAND_CONV o RAND_CONV)  [ADD_SYM]] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES, LESS_EQ_ADD, LESS_SUC_REFL]);

val SUM_EQ = store_thm("SUM_EQ",
  (--`!f g m n. (!r. m <= r /\ r < (n + m) ==> (f(r) = g(r)))
        ==> (sum(m,n) f = sum(m,n) g)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN GEN_TAC THEN
  DISCH_THEN(fn th => MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    FIRST_ASSUM(SUBST1_TAC o C MATCH_MP th)) THEN REFL_TAC);

val SUM_POS = store_thm("SUM_POS",
  (--`!f. (!n. 0 <= f(n)) ==> !m n. 0 <= sum(m,n) f`--),
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[]);

val SUM_POS_GEN = store_thm("SUM_POS_GEN",
  (--`!f m. (!n. m <= n ==> 0 <= f(n)) ==>
        !n. 0 <= sum(m,n) f`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_ACCEPT_TAC LESS_EQ_ADD);

val SUM_ABS = store_thm("SUM_ABS",
  (--`!f m n. abs(sum(m,n) (\m. abs(f m))) = sum(m,n) (\m. abs(f m))`--),
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[ABS_REFL] THEN
  GEN_TAC THEN MATCH_MP_TAC SUM_POS THEN BETA_TAC THEN
  REWRITE_TAC[ABS_POS]);

val SUM_ABS_LE = store_thm("SUM_ABS_LE",
  (--`!f m n. abs(sum(m,n) f) <= sum(m,n)(\n. abs(f n))`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, ABS_0, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`abs(sum(m,n) f) + abs(f(m + n))`--) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN BETA_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_RADD]);

val SUM_ZERO = store_thm("SUM_ZERO",
  (--`!f N. (!n. n >= N ==> (f(n) = 0))
              ==>
            (!m n. m >= N ==> (sum(m,n) f = 0))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [--`m:num`--, --`n:num`--] THEN
  REWRITE_TAC[GREATER_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC o MATCH_MP LESS_EQUAL_ADD)
  THEN
  SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN INDUCT_TAC THEN REWRITE_TAC[sum]
  THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[GREATER_EQ, GSYM ADD_ASSOC, LESS_EQ_ADD]);

val SUM_ADD = store_thm("SUM_ADD",
  (--`!f g m n.
      sum(m,n) (\n. f(n) + g(n))
      =
      sum(m,n) f + sum(m,n) g`--),
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_ADD_LID] THEN BETA_TAC THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val SUM_CMUL = store_thm("SUM_CMUL",
  (--`!f c m n. sum(m,n) (\n. c * f(n)) = c * sum(m,n) f`--),
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_MUL_RZERO] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_LDISTRIB]);

val SUM_NEG = store_thm("SUM_NEG",
  (--`!f n d. sum(n,d) (\n. ~(f n)) = ~(sum(n,d) f)`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_NEG_0] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_NEG_ADD]);

val SUM_SUB = store_thm("SUM_SUB",
  (--`!f g m n.
      sum(m,n)(\n. (f n) - (g n))
    = sum(m,n) f - sum(m,n) g`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub, GSYM SUM_NEG, GSYM SUM_ADD] THEN
  BETA_TAC THEN REFL_TAC);

val SUM_SUBST = store_thm("SUM_SUBST",
  (--`!f g m n. (!p. m <= p /\ p < (m + n) ==> (f p = g p))
        ==> (sum(m,n) f = sum(m,n) g)`--),
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN BINOP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC THEN
    MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[LESS_EQ_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    MATCH_MP_TAC LESS_MONO_ADD THEN REWRITE_TAC[LESS_SUC_REFL]]);

val SUM_NSUB = store_thm("SUM_NSUB",
  (--`!n f c.
      sum(0,n) f - (&n * c)
        =
      sum(0,n)(\p. f(p) - c)`--),
  INDUCT_TAC THEN REWRITE_TAC[sum, REAL_MUL_LZERO, REAL_SUB_REFL] THEN
  REWRITE_TAC[ADD_CLAUSES, REAL, REAL_RDISTRIB] THEN BETA_TAC THEN
  REPEAT GEN_TAC THEN POP_ASSUM(fn th => REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_MUL_LID] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val SUM_BOUND = store_thm("SUM_BOUND",
  (--`!f k m n. (!p. m <= p /\ p < (m + n) ==> (f(p) <= k))
        ==> (sum(m,n) f <= (&n * k))`--),
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN
  REWRITE_TAC[sum, REAL_MUL_LZERO, REAL_LE_REFL] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL, REAL_RDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_ACCEPT_TAC LESS_SUC,
    REWRITE_TAC[REAL_MUL_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ADD_CLAUSES, LESS_EQ_ADD] THEN
    MATCH_ACCEPT_TAC LESS_SUC_REFL]);

val SUM_GROUP = store_thm("SUM_GROUP",
  (--`!n k f. sum(0,n)(\m. sum(m * k,k) f) = sum(0,n * k) f`--),
  INDUCT_TAC THEN REWRITE_TAC[sum, MULT_CLAUSES] THEN
  REPEAT GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES, SUM_TWO]);

val SUM_1 = store_thm("SUM_1",
  (--`!f n. sum(n,1) f = f(n)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_CONV (--`1:num`--), sum, ADD_CLAUSES, REAL_ADD_LID]);

val SUM_2 = store_thm("SUM_2",
  (--`!f n. sum(n,2) f = f(n) + f(n + 1)`--),
  REPEAT GEN_TAC THEN CONV_TAC(REDEPTH_CONV num_CONV) THEN
  REWRITE_TAC[sum, ADD_CLAUSES, REAL_ADD_LID]);

val SUM_OFFSET = store_thm("SUM_OFFSET",
  (--`!f n k.
      sum(0,n)(\m. f(m + k))
    = sum(0,n + k) f - sum(0,k) f`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  REWRITE_TAC[GSYM SUM_TWO, REAL_ADD_SUB] THEN
  SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN
  INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC ADD_SYM);

val SUM_REINDEX = store_thm("SUM_REINDEX",
  (--`!f m k n. sum(m + k,n) f = sum(m,n)(\r. f(r + k))`--),
  EVERY [GEN_TAC, GEN_TAC, GEN_TAC] THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  ASM_REWRITE_TAC[REAL_EQ_LADD] THEN BETA_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(AC_CONV(ADD_ASSOC,ADD_SYM)));

val SUM_0 = store_thm("SUM_0",
  (--`!m n. sum(m,n)(\r. 0) = 0`--),
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID]);

val SUM_PERMUTE_0 = store_thm("SUM_PERMUTE_0",
  (--`!n p. (!y. y < n ==> ?!x. x < n /\ (p(x) = y))
        ==> !f. sum(0,n)(\n. f(p n)) = sum(0,n) f`--),
  INDUCT_TAC THEN GEN_TAC THEN TRY(REWRITE_TAC[sum] THEN NO_TAC) THEN
  DISCH_TAC THEN GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC (--`n:num`--)) THEN
  REWRITE_TAC[LESS_SUC_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) STRIP_ASSUME_TAC) THEN
  GEN_REWR_TAC RAND_CONV  [sum] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ABBREV_TAC (--`q:num->num = \r. if r < k then p(r) else p(SUC r)`--) THEN
  SUBGOAL_THEN (--`!y:num. y < n ==> ?!x. x < n /\ (q x = y)`--) MP_TAC
  THENL
   [X_GEN_TAC (--`y:num`--) THEN DISCH_TAC THEN
    (MP_TAC o ASSUME) (--`!y. y<SUC n ==> ?!x. x<SUC n /\ (p x = y)`--) THEN
    DISCH_THEN(MP_TAC o SPEC (--`y:num`--)) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`n:num`--) THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL],
      DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MP th))] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`x:num`--) STRIP_ASSUME_TAC o CONJUNCT1) THEN
    CONJ_TAC THENL
     [DISJ_CASES_TAC(SPECL [(--`x:num`--), (--`k:num`--)] LESS_CASES) THENL
       [EXISTS_TAC (--`x:num`--) THEN EXPAND_TAC "q" THEN BETA_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_LT] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC (--`&k`--) THEN ASM_REWRITE_TAC[REAL_LE, REAL_LT] THEN
        UNDISCH_TAC (--`k < SUC n`--) THEN
        REWRITE_TAC[LESS_EQ, LESS_EQ_MONO],
        MP_TAC(ASSUME (--`k <= x:num`--)) THEN REWRITE_TAC[LESS_OR_EQ] THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
         [EXISTS_TAC (--`x - 1:num`--) THEN EXPAND_TAC "q" THEN BETA_TAC THEN
          UNDISCH_TAC (--`k < x:num`--) THEN
          DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) MP_TAC o MATCH_MP LESS_ADD_1)
          THEN
          REWRITE_TAC[GSYM ADD1, ADD_CLAUSES] THEN
          DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_EQ]) THEN
          ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
          UNDISCH_TAC (--`(k + d) < k:num`--) THEN
          REWRITE_TAC[LESS_EQ] THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC[GSYM NOT_LESS, REWRITE_RULE[ADD_CLAUSES] LESS_ADD_SUC],
          SUBST_ALL_TAC(ASSUME (--`(p:num->num) x = n`--)) THEN
          UNDISCH_TAC (--`y < n:num`--) THEN ASM_REWRITE_TAC[LESS_REFL]]],
      SUBGOAL_THEN
       (--`!z. q z :num = p(if z < k then z else SUC z)`--) MP_TAC THENL
       [GEN_TAC THEN EXPAND_TAC "q" THEN BETA_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[],
        DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
      MAP_EVERY X_GEN_TAC [(--`x1:num`--), (--`x2:num`--)] THEN STRIP_TAC THEN
      UNDISCH_TAC (--`!y. y < SUC n ==> ?!x. x < SUC n /\ (p x = y)`--) THEN
      DISCH_THEN(MP_TAC o SPEC (--`y:num`--)) THEN
      REWRITE_TAC[MATCH_MP LESS_SUC (ASSUME (--`y < n:num`--))] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
      DISCH_THEN(MP_TAC
                 o SPECL [(--`if x1 < (k:num) then x1 else SUC x1`--),
                          (--`if x2 < (k:num) then x2 else SUC x2`--)]
                 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
       [CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LESS_MONO_EQ] THEN
        MATCH_MP_TAC LESS_SUC THEN ASM_REWRITE_TAC[],
        DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
        REPEAT COND_CASES_TAC THEN REWRITE_TAC[INV_SUC_EQ] THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`~(x2 < k:num)`--) THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
          EXISTS_TAC (--`SUC x2`--) THEN ASM_REWRITE_TAC[LESS_SUC_REFL],
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
          UNDISCH_TAC (--`~(x1 < k:num)`--) THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
          EXISTS_TAC (--`SUC x1`--) THEN ASM_REWRITE_TAC[LESS_SUC_REFL]]]],
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fn th => GEN_REWR_TAC(RAND_CONV o ONCE_DEPTH_CONV)[GSYM th])THEN
    BETA_TAC THEN UNDISCH_TAC (--`k < SUC n`--) THEN
    REWRITE_TAC[LESS_EQ, LESS_EQ_MONO] THEN
    DISCH_THEN(X_CHOOSE_TAC (--`d:num`--) o MATCH_MP LESS_EQUAL_ADD) THEN
    GEN_REWR_TAC (RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
                     [ASSUME (--`n = k + d:num`--)] THEN
    REWRITE_TAC[GSYM SUM_TWO] THEN
    GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      [ASSUME (--`n = k + d:num`--)] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUC] THEN
    REWRITE_TAC[GSYM SUM_TWO, sum, ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN BINOP_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (--`r:num`--) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
      BETA_TAC THEN EXPAND_TAC "q" THEN ASM_REWRITE_TAC[],
      GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
      REWRITE_TAC[ASSUME (--`(p:num->num) k = n`--), REAL_EQ_LADD] THEN
      REWRITE_TAC[ADD1, SUM_REINDEX] THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (--`r:num`--) THEN BETA_TAC THEN
      REWRITE_TAC[GSYM NOT_LESS] THEN DISCH_TAC THEN
      EXPAND_TAC "q" THEN BETA_TAC THEN ASM_REWRITE_TAC[ADD1]]]);

val SUM_CANCEL = store_thm("SUM_CANCEL",
  (--`!f n d.
      sum(n,d) (\n. f(SUC n) - f(n))
    = f(n + d) - f(n)`--),
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, ADD_CLAUSES, REAL_SUB_REFL] THEN
  BETA_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_RID]);

(* ------------------------------------------------------------------------- *)
(* Theorems to be compatible with hol-light.                                 *)
(* ------------------------------------------------------------------------- *)

val REAL_MUL_RNEG = store_thm("REAL_MUL_RNEG",
  Term`!x y. x * ~y = ~(x * y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL REAL_EQ_RADD)))) THEN
  EXISTS_TAC (Term`x:real * y`) THEN
  REWRITE_TAC[GSYM REAL_LDISTRIB, REAL_ADD_LINV, REAL_MUL_RZERO]);

val REAL_MUL_LNEG = store_thm ("REAL_MUL_LNEG",
Term`!x y. ~x * y = ~(x * y)`,
  MESON_TAC[REAL_MUL_SYM, REAL_MUL_RNEG]);

val real_lt = store_thm ("real_lt",
Term`!y x. x < y = ~(y <= x)`,
  let
    val th1 = TAUT_PROVE (Term`!t u:bool. (t = ~u) ==> (u = ~t)`)
    val th2 = SPECL [``y <= x``,``x < y``] th1
    val th3 = SPECL [``y:real``,``x:real``] real_lte
  in
    ACCEPT_TAC (GENL [``y:real``, ``x:real``] (MP th2 th3))
  end);

val REAL_LE_LADD_IMP = save_thm ("REAL_LE_LADD_IMP",
  let
    val th1 = GSYM (SPEC_ALL REAL_LE_LADD)
    val th2 = TAUT_PROVE ``(x:bool = y) ==> (x ==> y)``
  in
    GEN ``x:real`` (GEN ``y:real`` (GEN ``z:real`` (MATCH_MP th2 th1)))
  end);

val REAL_LE_LNEG = store_thm ("REAL_LE_LNEG",
  ``!x y. ~x <= y = 0 <= x + y``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THENL
   [DISCH_THEN(MP_TAC o SPEC ``x:real``) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LINV],
    DISCH_THEN(MP_TAC o SPEC ``~x``) THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_ASSOC, REAL_ADD_LID,
        ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID]]);

val REAL_LE_NEG2 = save_thm ("REAL_LE_NEG2", REAL_LE_NEG);

val REAL_NEG_NEG = save_thm ("REAL_NEG_NEG", REAL_NEGNEG);

val REAL_LE_RNEG = store_thm ("REAL_LE_RNEG",
  ``!x y. x <= ~y = x + y <= 0``,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_LE_LNEG, GSYM REAL_NEG_ADD] THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_LE_NEG2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_ADD_LINV] THEN
  REWRITE_TAC[REAL_NEG_ADD, REAL_NEG_NEG] THEN
  MATCH_ACCEPT_TAC REAL_ADD_SYM);

val REAL_POW_INV = Q.store_thm
 ("REAL_POW_INV",
  `!x n. (inv x) pow n = inv(x pow n)`,
  Induct_on `n` THEN REWRITE_TAC [pow] THENL
  [REWRITE_TAC [REAL_INV1],
   GEN_TAC THEN Cases_on `x = 0r` THENL
   [POP_ASSUM SUBST_ALL_TAC
     THEN REWRITE_TAC [REAL_INV_0,REAL_MUL_LZERO],
    `~(x pow n = 0)` by PROVE_TAC [POW_NZ] THEN
    IMP_RES_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC []]]);

val REAL_POW_DIV = Q.store_thm
("REAL_POW_DIV",
 `!x y n. (x / y) pow n = (x pow n) / (y pow n)`,
 REWRITE_TAC[real_div, POW_MUL, REAL_POW_INV]);

val REAL_POW_ADD = Q.store_thm
("REAL_POW_ADD",
 `!x m n. x pow (m + n) = x pow m * x pow n`,
  Induct_on `m` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES, pow, REAL_MUL_LID, REAL_MUL_ASSOC]);

val REAL_LE_RDIV_EQ = Q.store_thm
("REAL_LE_RDIV_EQ",
 `!x y z. &0 < z ==> (x <= y / z = x * z <= y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
    Rewrite.GEN_REWRITE_TAC LAND_CONV Rewrite.empty_rewrites
                   [GSYM(MATCH_MP REAL_LE_RMUL th)]) THEN
  RW_TAC bool_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV,
               REAL_MUL_RID, REAL_POS_NZ]);

val REAL_LE_LDIV_EQ = Q.store_thm
("REAL_LE_LDIV_EQ",
 `!x y z. &0 < z ==> (x / z <= y = x <= y * z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
    Rewrite.GEN_REWRITE_TAC LAND_CONV Rewrite.empty_rewrites
             [GSYM(MATCH_MP REAL_LE_RMUL th)]) THEN
  RW_TAC bool_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV,
               REAL_MUL_RID, REAL_POS_NZ]);

val REAL_LT_RDIV_EQ = Q.store_thm
("REAL_LT_RDIV_EQ",
 `!x y z. &0 < z ==> (x < y / z = x * z < y)`,
 RW_TAC bool_ss [GSYM REAL_NOT_LE, REAL_LE_LDIV_EQ]);

val REAL_LT_LDIV_EQ = Q.store_thm
("REAL_LT_LDIV_EQ",
 `!x y z. &0 < z ==> (x / z < y = x < y * z)`,
  RW_TAC bool_ss [GSYM REAL_NOT_LE, REAL_LE_RDIV_EQ]);

val REAL_EQ_RDIV_EQ = Q.store_thm
("REAL_EQ_RDIV_EQ",
 `!x y z. &0 < z ==> ((x = y / z) = (x * z = y))`,
 REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
 RW_TAC bool_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ]);

val REAL_EQ_LDIV_EQ = Q.store_thm
("REAL_EQ_LDIV_EQ",
 `!x y z. &0 < z ==> ((x / z = y) = (x = y * z))`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  RW_TAC bool_ss [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ]);

val REAL_OF_NUM_POW = Q.store_thm
("REAL_OF_NUM_POW",
 `!x n. (&x) pow n = &(x EXP n)`,
  Induct_on `n` THEN ASM_REWRITE_TAC[pow, EXP, REAL_MUL]);

val REAL_ADD_LDISTRIB = save_thm ("REAL_ADD_LDISTRIB", REAL_LDISTRIB);

val REAL_ADD_RDISTRIB = save_thm ("REAL_ADD_RDISTRIB", REAL_RDISTRIB);

val REAL_OF_NUM_ADD = save_thm ("REAL_OF_NUM_ADD", REAL_ADD);

val REAL_OF_NUM_LE = save_thm ("REAL_OF_NUM_LE", REAL_LE);

val REAL_OF_NUM_MUL = save_thm ("REAL_OF_NUM_MUL", REAL_MUL);

val REAL_OF_NUM_SUC = store_thm (
  "REAL_OF_NUM_SUC",
  ``!n. &n + &1 = &(SUC n)``,
  REWRITE_TAC[ADD1, REAL_ADD]);

val REAL_OF_NUM_EQ = save_thm ("REAL_OF_NUM_EQ", REAL_INJ);

val REAL_EQ_MUL_LCANCEL = store_thm (
  "REAL_EQ_MUL_LCANCEL",
  ``!x y z. (x * y = x * z) = (x = 0) \/ (y = z)``,
  REWRITE_TAC [REAL_EQ_LMUL]);

val REAL_ABS_0 = save_thm ("REAL_ABS_0", ABS_0);
val _ = export_rewrites ["REAL_ABS_0"]

val REAL_ABS_TRIANGLE = save_thm ("REAL_ABS_TRIANGLE", ABS_TRIANGLE);

val REAL_ABS_MUL = save_thm ("REAL_ABS_MUL", ABS_MUL);

val REAL_ABS_POS = save_thm ("REAL_ABS_POS", ABS_POS);

val REAL_LE_EPSILON = store_thm
  ("REAL_LE_EPSILON",
   ``!x y : real. (!e. 0 < e ==> x <= y + e) ==> x <= y``,
   RW_TAC boolSimps.bool_ss []
   THEN (SUFF_TAC ``~(0r < x - y)``
         THEN1 RW_TAC boolSimps.bool_ss
               [REAL_NOT_LT, REAL_LE_SUB_RADD, REAL_ADD_LID])
   THEN STRIP_TAC
   THEN Q.PAT_ASSUM `!e. P e` MP_TAC
   THEN RW_TAC boolSimps.bool_ss []
   THEN (KNOW_TAC ``!a b c : real. ~(a <= b + c) = c < a - b``
         THEN1 (RW_TAC boolSimps.bool_ss [REAL_LT_SUB_LADD, REAL_NOT_LE]
                THEN PROVE_TAC [REAL_ADD_SYM]))
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN PROVE_TAC [REAL_DOWN]);

val REAL_BIGNUM = store_thm
  ("REAL_BIGNUM",
   ``!r : real. ?n : num. r < &n``,
   GEN_TAC
   THEN MP_TAC (Q.SPEC `1` REAL_ARCH)
   THEN REWRITE_TAC [REAL_LT_01, REAL_MUL_RID]
   THEN PROVE_TAC []);

val REAL_INV_LT_ANTIMONO = store_thm
  ("REAL_INV_LT_ANTIMONO",
   ``!x y : real. 0 < x /\ 0 < y ==> (inv x < inv y = y < x)``,
   RW_TAC boolSimps.bool_ss []
   THEN (REVERSE EQ_TAC THEN1 PROVE_TAC [REAL_LT_INV])
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_INV_INV]
   THEN MATCH_MP_TAC REAL_LT_INV
   THEN RW_TAC boolSimps.bool_ss [REAL_INV_POS]);

val REAL_INV_INJ = store_thm
  ("REAL_INV_INJ",
   ``!x y : real. (inv x = inv y) = (x = y)``,
   PROVE_TAC [REAL_INV_INV])

val REAL_DIV_RMUL_CANCEL = store_thm
  ("REAL_DIV_RMUL_CANCEL",
   ``!c a b : real. ~(c = 0) ==> ((a * c) / (b * c) = a / b)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN Cases_on `b = 0`
   THEN RW_TAC boolSimps.bool_ss
      [REAL_MUL_LZERO, REAL_INV_0, REAL_INV_MUL, REAL_MUL_RZERO,
       REAL_EQ_MUL_LCANCEL, GSYM REAL_MUL_ASSOC]
   THEN DISJ2_TAC
   THEN (KNOW_TAC ``!a b c : real. a * (b * c) = (a * c) * b``
         THEN1 PROVE_TAC [REAL_MUL_ASSOC, REAL_MUL_SYM])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_RINV, REAL_MUL_LID]);

val REAL_DIV_LMUL_CANCEL = store_thm
  ("REAL_DIV_LMUL_CANCEL",
   ``!c a b : real. ~(c = 0) ==> ((c * a) / (c * b) = a / b)``,
   METIS_TAC [REAL_DIV_RMUL_CANCEL, REAL_MUL_SYM]);

val REAL_DIV_ADD = store_thm
  ("REAL_DIV_ADD",
   ``!x y z : real. y / x + z / x = (y + z) / x``,
   RW_TAC boolSimps.bool_ss [real_div, REAL_ADD_RDISTRIB]);

val REAL_ADD_RAT = store_thm
  ("REAL_ADD_RAT",
   ``!a b c d : real.
       ~(b = 0) /\ ~(d = 0) ==>
       (a / b + c / d = (a * d + b * c) / (b * d))``,
   RW_TAC boolSimps.bool_ss
   [GSYM REAL_DIV_ADD, REAL_DIV_RMUL_CANCEL, REAL_DIV_LMUL_CANCEL]);

val REAL_SUB_RAT = store_thm
  ("REAL_SUB_RAT",
   ``!a b c d : real.
       ~(b = 0) /\ ~(d = 0) ==>
       (a / b - c / d = (a * d - b * c) / (b * d))``,
   RW_TAC boolSimps.bool_ss [real_sub, real_div, REAL_NEG_LMUL]
   THEN RW_TAC boolSimps.bool_ss [GSYM real_div]
   THEN METIS_TAC [REAL_ADD_RAT, REAL_NEG_LMUL, REAL_NEG_RMUL]);

val REAL_SUB = store_thm
  ("REAL_SUB",
   ``!m n : num.
       (& m : real) - & n = if m - n = 0 then ~(& (n - m)) else & (m - n)``,
   RW_TAC old_arith_ss [REAL_EQ_SUB_RADD, REAL_ADD]
   THEN ONCE_REWRITE_TAC [REAL_ADD_SYM]
   THEN RW_TAC old_arith_ss [GSYM real_sub, REAL_EQ_SUB_LADD, REAL_ADD]);

(* ------------------------------------------------------------------------- *)
(* Define a constant for extracting "the positive part" of real numbers.     *)
(* ------------------------------------------------------------------------- *)

val pos_def = Define `pos (x : real) = if 0 <= x then x else 0`;

val REAL_POS_POS = store_thm
  ("REAL_POS_POS",
   ``!x. 0 <= pos x``,
   RW_TAC boolSimps.bool_ss [pos_def, REAL_LE_REFL]);

val REAL_POS_ID = store_thm
  ("REAL_POS_ID",
   ``!x. 0 <= x ==> (pos x = x)``,
   RW_TAC boolSimps.bool_ss [pos_def]);

val REAL_POS_INFLATE = store_thm
  ("REAL_POS_INFLATE",
   ``!x. x <= pos x``,
   RW_TAC boolSimps.bool_ss [pos_def, REAL_LE_REFL]
   THEN PROVE_TAC [REAL_LE_TOTAL]);

val REAL_POS_MONO = store_thm
  ("REAL_POS_MONO",
   ``!x y. x <= y ==> pos x <= pos y``,
   RW_TAC boolSimps.bool_ss [pos_def, REAL_LE_REFL]
   THEN PROVE_TAC [REAL_LE_TOTAL, REAL_LE_TRANS]);

val REAL_POS_EQ_ZERO = store_thm
  ("REAL_POS_EQ_ZERO",
   ``!x. (pos x = 0) = x <= 0``,
   RW_TAC boolSimps.bool_ss [pos_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL])

val REAL_POS_LE_ZERO = store_thm
  ("REAL_POS_LE_ZERO",
   ``!x. (pos x <= 0) = x <= 0``,
   RW_TAC boolSimps.bool_ss [pos_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL])

(* ------------------------------------------------------------------------- *)
(* Define the minimum of two real numbers                                    *)
(* ------------------------------------------------------------------------- *)

val min_def = Define `min (x : real) y = if x <= y then x else y`;

val REAL_MIN_REFL = store_thm
  ("REAL_MIN_REFL",
   ``!x. min x x = x``,
   RW_TAC boolSimps.bool_ss [min_def]);

val REAL_LE_MIN = store_thm
  ("REAL_LE_MIN",
   ``!z x y. z <= min x y = z <= x /\ z <= y``,
   RW_TAC boolSimps.bool_ss [min_def]
   THEN PROVE_TAC [REAL_LE_TRANS, REAL_LE_TOTAL]);

val REAL_MIN_LE = store_thm
  ("REAL_MIN_LE",
   ``!z x y. min x y <= z = x <= z \/ y <= z``,
   RW_TAC boolSimps.bool_ss [min_def, REAL_LE_REFL]
   THEN PROVE_TAC [REAL_LE_TOTAL, REAL_LE_TRANS]);

val REAL_MIN_LE1 = store_thm
  ("REAL_MIN_LE1",
   ``!x y. min x y <= x``,
   RW_TAC boolSimps.bool_ss [REAL_MIN_LE, REAL_LE_REFL]);

val REAL_MIN_LE2 = store_thm
  ("REAL_MIN_LE2",
   ``!x y. min x y <= y``,
   RW_TAC boolSimps.bool_ss [REAL_MIN_LE, REAL_LE_REFL]);

val REAL_MIN_ALT = store_thm
  ("REAL_MIN_ALT",
   ``!x y. (x <= y ==> (min x y = x)) /\ (y <= x ==> (min x y = y))``,
   RW_TAC boolSimps.bool_ss [min_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM]);

val REAL_MIN_LE_LIN = store_thm
  ("REAL_MIN_LE_LIN",
   ``!z x y. 0 <= z /\ z <= 1 ==> min x y <= z * x + (1 - z) * y``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (Q.SPECL [`x`, `y`] REAL_LE_TOTAL)
   THEN (STRIP_TAC THEN RW_TAC boolSimps.bool_ss [REAL_MIN_ALT])
   THENL [MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `z * x + (1 - z) * x`
          THEN (CONJ_TAC THEN1
                RW_TAC boolSimps.bool_ss
                [GSYM REAL_RDISTRIB, REAL_SUB_ADD2, REAL_LE_REFL, REAL_MUL_LID])
          THEN MATCH_MP_TAC REAL_LE_ADD2
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_REFL])
          THEN MATCH_MP_TAC REAL_LE_LMUL_IMP
          THEN ASM_REWRITE_TAC [REAL_SUB_LE],
          MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `z * y + (1 - z) * y`
          THEN (CONJ_TAC THEN1
                RW_TAC boolSimps.bool_ss
                [GSYM REAL_RDISTRIB, REAL_SUB_ADD2, REAL_LE_REFL, REAL_MUL_LID])
          THEN MATCH_MP_TAC REAL_LE_ADD2
          THEN (REVERSE CONJ_TAC THEN1 PROVE_TAC [REAL_LE_REFL])
          THEN MATCH_MP_TAC REAL_LE_LMUL_IMP
          THEN ASM_REWRITE_TAC []]);

val REAL_MIN_ADD = store_thm
  ("REAL_MIN_ADD",
   ``!z x y. min (x + z) (y + z) = min x y + z``,
   RW_TAC boolSimps.bool_ss [min_def, REAL_LE_RADD]);

val REAL_MIN_SUB = store_thm
  ("REAL_MIN_SUB",
   ``!z x y. min (x - z) (y - z) = min x y - z``,
   RW_TAC boolSimps.bool_ss [min_def, REAL_LE_SUB_RADD, REAL_SUB_ADD]);

val REAL_IMP_MIN_LE2 = store_thm
  ("REAL_IMP_MIN_LE2",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> min x1 x2 <= min y1 y2``,
   RW_TAC boolSimps.bool_ss [REAL_LE_MIN]
   THEN RW_TAC boolSimps.bool_ss [REAL_MIN_LE]);

(* ------------------------------------------------------------------------- *)
(* Define the maximum of two real numbers                                    *)
(* ------------------------------------------------------------------------- *)

val max_def = Define `max (x : real) y = if x <= y then y else x`;

val REAL_MAX_REFL = store_thm
  ("REAL_MAX_REFL",
   ``!x. max x x = x``,
   RW_TAC boolSimps.bool_ss [max_def]);

val REAL_LE_MAX = store_thm
  ("REAL_LE_MAX",
   ``!z x y. z <= max x y = z <= x \/ z <= y``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LE_TOTAL, REAL_LE_TRANS]);

val REAL_LE_MAX1 = store_thm
  ("REAL_LE_MAX1",
   ``!x y. x <= max x y``,
   RW_TAC boolSimps.bool_ss [REAL_LE_MAX, REAL_LE_REFL]);

val REAL_LE_MAX2 = store_thm
  ("REAL_LE_MAX2",
   ``!x y. y <= max x y``,
   RW_TAC boolSimps.bool_ss [REAL_LE_MAX, REAL_LE_REFL]);

val REAL_MAX_LE = store_thm
  ("REAL_MAX_LE",
   ``!z x y. max x y <= z = x <= z /\ y <= z``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LE_TRANS, REAL_LE_TOTAL]);

val REAL_MAX_ALT = store_thm
  ("REAL_MAX_ALT",
   ``!x y. (x <= y ==> (max x y = y)) /\ (y <= x ==> (max x y = x))``,
   RW_TAC boolSimps.bool_ss [max_def]
   THEN PROVE_TAC [REAL_LE_ANTISYM]);

val REAL_MAX_MIN = store_thm
  ("REAL_MAX_MIN",
   ``!x y. max x y = ~min (~x) (~y)``,
   REPEAT GEN_TAC
   THEN MP_TAC (Q.SPECL [`x`, `y`] REAL_LE_TOTAL)
   THEN STRIP_TAC
   THEN RW_TAC boolSimps.bool_ss
        [REAL_MAX_ALT, REAL_MIN_ALT, REAL_LE_NEG2, REAL_NEGNEG]);

val REAL_MIN_MAX = store_thm
  ("REAL_MIN_MAX",
   ``!x y. min x y = ~max (~x) (~y)``,
   REPEAT GEN_TAC
   THEN MP_TAC (Q.SPECL [`x`, `y`] REAL_LE_TOTAL)
   THEN STRIP_TAC
   THEN RW_TAC boolSimps.bool_ss
        [REAL_MAX_ALT, REAL_MIN_ALT, REAL_LE_NEG2, REAL_NEGNEG]);

val REAL_LIN_LE_MAX = store_thm
  ("REAL_LIN_LE_MAX",
   ``!z x y. 0 <= z /\ z <= 1 ==> z * x + (1 - z) * y <= max x y``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (Q.SPECL [`z`, `~x`, `~y`] REAL_MIN_LE_LIN)
   THEN RW_TAC boolSimps.bool_ss
        [REAL_MIN_MAX, REAL_NEGNEG, REAL_MUL_RNEG, GSYM REAL_NEG_ADD,
         REAL_LE_NEG2]);

val REAL_MAX_ADD = store_thm
  ("REAL_MAX_ADD",
   ``!z x y. max (x + z) (y + z) = max x y + z``,
   RW_TAC boolSimps.bool_ss [max_def, REAL_LE_RADD]);

val REAL_MAX_SUB = store_thm
  ("REAL_MAX_SUB",
   ``!z x y. max (x - z) (y - z) = max x y - z``,
   RW_TAC boolSimps.bool_ss [max_def, REAL_LE_SUB_RADD, REAL_SUB_ADD]);

val REAL_IMP_MAX_LE2 = store_thm
  ("REAL_IMP_MAX_LE2",
   ``!x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> max x1 x2 <= max y1 y2``,
   RW_TAC boolSimps.bool_ss [REAL_MAX_LE]
   THEN RW_TAC boolSimps.bool_ss [REAL_LE_MAX]);

(* ------------------------------------------------------------------------- *)
(* More theorems about sup, and corresponding theorems about an inf operator *)
(* ------------------------------------------------------------------------- *)

val inf_def = Define `inf p = ~(sup (\r. p (~r)))`;

val REAL_SUP_EXISTS_UNIQUE = store_thm
  ("REAL_SUP_EXISTS_UNIQUE",
   ``!p : real -> bool.
       (?x. p x) /\ (?z. !x. p x ==> x <= z) ==>
       ?!s. !y. (?x. p x /\ y < x) = y < s``,
   REPEAT STRIP_TAC
   THEN CONV_TAC EXISTS_UNIQUE_CONV
   THEN (RW_TAC boolSimps.bool_ss []
         THEN1 (MP_TAC (Q.SPEC `p` REAL_SUP_LE) THEN PROVE_TAC []))
   THEN REWRITE_TAC [GSYM REAL_LE_ANTISYM, GSYM REAL_NOT_LT]
   THEN REPEAT STRIP_TAC
   THENL [(SUFF_TAC ``!x : real. p x ==> ~(s' < x)`` THEN1 PROVE_TAC [])
          THEN REPEAT STRIP_TAC
          THEN (SUFF_TAC ``~((s' : real) < s')`` THEN1 PROVE_TAC [])
          THEN REWRITE_TAC [REAL_LT_REFL],
          (SUFF_TAC ``!x : real. p x ==> ~(s < x)`` THEN1 PROVE_TAC [])
          THEN REPEAT STRIP_TAC
          THEN (SUFF_TAC ``~((s : real) < s)`` THEN1 PROVE_TAC [])
          THEN REWRITE_TAC [REAL_LT_REFL]]);

val REAL_SUP_MAX = store_thm
  ("REAL_SUP_MAX",
   ``!p z. p z /\ (!x. p x ==> x <= z) ==> (sup p = z)``,
    REPEAT STRIP_TAC
    THEN (KNOW_TAC ``!y : real. (?x. p x /\ y < x) = y < z``
          THEN1 (STRIP_TAC
                 THEN REVERSE EQ_TAC THEN1 PROVE_TAC []
                 THEN REPEAT STRIP_TAC
                 THEN PROVE_TAC [REAL_LTE_TRANS]))
    THEN STRIP_TAC
    THEN (KNOW_TAC ``!y. (?x. p x /\ y < x) = y < sup p``
          THEN1 PROVE_TAC [REAL_SUP_LE])
    THEN STRIP_TAC
    THEN (KNOW_TAC ``(?x : real. p x) /\ (?z. !x. p x ==> x <= z)``
          THEN1 PROVE_TAC [])
    THEN STRIP_TAC
    THEN ASSUME_TAC ((SPEC ``p:real->bool`` o CONV_RULE
                    (DEPTH_CONV EXISTS_UNIQUE_CONV)) REAL_SUP_EXISTS_UNIQUE)
    THEN RES_TAC);

val REAL_IMP_SUP_LE = store_thm
  ("REAL_IMP_SUP_LE",
   ``!p x. (?r. p r) /\ (!r. p r ==> r <= x) ==> sup p <= x``,
   RW_TAC boolSimps.bool_ss []
   THEN REWRITE_TAC [GSYM REAL_NOT_LT]
   THEN STRIP_TAC
   THEN MP_TAC (SPEC ``p:real->bool`` REAL_SUP_LE)
   THEN RW_TAC boolSimps.bool_ss []
   THENL [PROVE_TAC [],
          PROVE_TAC [],
          EXISTS_TAC ``x:real``
          THEN RW_TAC boolSimps.bool_ss []
          THEN PROVE_TAC [real_lte]]);

val REAL_IMP_LE_SUP = store_thm
  ("REAL_IMP_LE_SUP",
   ``!p x.
       (?r. p r) /\ (?z. !r. p r ==> r <= z) /\ (?r. p r /\ x <= r) ==>
       x <= sup p``,
   RW_TAC boolSimps.bool_ss []
   THEN (SUFF_TAC ``!y. p y ==> y <= sup p`` THEN1 PROVE_TAC [REAL_LE_TRANS])
   THEN MATCH_MP_TAC REAL_SUP_UBOUND_LE
   THEN PROVE_TAC []);

val REAL_INF_MIN = store_thm
  ("REAL_INF_MIN",
   ``!p z. p z /\ (!x. p x ==> z <= x) ==> (inf p = z)``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (SPECL [``(\r. (p:real->bool) (~r))``, ``~(z:real)``]
                REAL_SUP_MAX)
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG, inf_def]
   THEN (SUFF_TAC ``!x : real. p ~x ==> x <= ~z`` THEN1 PROVE_TAC [REAL_NEGNEG])
   THEN REPEAT STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN ONCE_REWRITE_TAC [REAL_LE_NEG]
   THEN REWRITE_TAC [REAL_NEGNEG]
   THEN PROVE_TAC []);

val REAL_IMP_LE_INF = store_thm
  ("REAL_IMP_LE_INF",
   ``!p r. (?x. p x) /\ (!x. p x ==> r <= x) ==> r <= inf p``,
   RW_TAC boolSimps.bool_ss [inf_def]
   THEN POP_ASSUM MP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN Q.SPEC_TAC (`~r`, `r`)
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG, REAL_LE_NEG]
   THEN MATCH_MP_TAC REAL_IMP_SUP_LE
   THEN RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC [REAL_NEGNEG]);

val REAL_IMP_INF_LE = store_thm
  ("REAL_IMP_INF_LE",
   ``!p r. (?z. !x. p x ==> z <= x) /\ (?x. p x /\ x <= r) ==> inf p <= r``,
   RW_TAC boolSimps.bool_ss [inf_def]
   THEN POP_ASSUM MP_TAC
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN Q.SPEC_TAC (`~r`, `r`)
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG, REAL_LE_NEG]
   THEN MATCH_MP_TAC REAL_IMP_LE_SUP
   THEN RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

val REAL_INF_LT = store_thm
  ("REAL_INF_LT",
   ``!p z. (?x. p x) /\ inf p < z ==> (?x. p x /\ x < z)``,
   RW_TAC boolSimps.bool_ss []
   THEN (SUFF_TAC ``~(!x. p x ==> ~(x < z))`` THEN1 PROVE_TAC [])
   THEN REWRITE_TAC [GSYM real_lte]
   THEN STRIP_TAC
   THEN Q.PAT_ASSUM `inf p < z` MP_TAC
   THEN RW_TAC boolSimps.bool_ss [GSYM real_lte]
   THEN MATCH_MP_TAC REAL_IMP_LE_INF
   THEN PROVE_TAC []);

val REAL_INF_CLOSE = store_thm
  ("REAL_INF_CLOSE",
   ``!p e. (?x. p x) /\ 0 < e ==> (?x. p x /\ x < inf p + e)``,
   RW_TAC boolSimps.bool_ss []
   THEN MATCH_MP_TAC REAL_INF_LT
   THEN (CONJ_TAC THEN1 PROVE_TAC [])
   THEN RW_TAC boolSimps.bool_ss [REAL_LT_ADDR]);

val SUP_EPSILON = store_thm
  ("SUP_EPSILON",
   ``!p e.
       0 < e /\ (?x. p x) /\ (?z. !x. p x ==> x <= z) ==>
       ?x. p x /\ sup p <= x + e``,
   REPEAT GEN_TAC
   THEN REPEAT DISCH_TAC
   THEN REWRITE_TAC [GSYM REAL_NOT_LT]
   THEN MP_TAC (Q.SPEC `p` REAL_SUP_LE)
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
   THEN POP_ASSUM MP_TAC
   THEN RW_TAC boolSimps.bool_ss [GSYM IMP_DISJ_THM, REAL_NOT_LT]
   THEN (SUFF_TAC
         ``?n : num.
             ?x : real. p x /\ z - &(SUC n) * e <= x /\ x <= z - & n * e /\
             !y. p y ==> y <= z - &n * e``
         THEN1 (RW_TAC boolSimps.bool_ss []
                THEN Q.EXISTS_TAC `x'`
                THEN RW_TAC boolSimps.bool_ss []
                THEN Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x''`)
                THEN RW_TAC boolSimps.bool_ss []
                THEN MATCH_MP_TAC REAL_LE_TRANS
                THEN Q.EXISTS_TAC `z - &n * e`
                THEN RW_TAC boolSimps.bool_ss []
                THEN (SUFF_TAC ``(z:real) - &n * e = z - &(SUC n) * e + 1 * e``
                      THEN1 RW_TAC boolSimps.bool_ss
                            [REAL_MUL_LID, REAL_LE_RADD])
                THEN RW_TAC boolSimps.bool_ss
                     [real_sub, GSYM REAL_ADD_ASSOC, REAL_EQ_LADD]
                THEN ONCE_REWRITE_TAC [GSYM REAL_EQ_NEG]
                THEN RW_TAC boolSimps.bool_ss
                     [REAL_NEGNEG, REAL_NEG_ADD, GSYM REAL_MUL_LNEG,
                      GSYM REAL_ADD_RDISTRIB, REAL_EQ_RMUL]
                THEN DISJ2_TAC
                THEN RW_TAC boolSimps.bool_ss
                     [REAL_EQ_SUB_LADD, GSYM real_sub, REAL_ADD, REAL_INJ,
                      arithmeticTheory.ADD1]))
   THEN (KNOW_TAC ``?n : num. ?x : real. p x /\ z - &(SUC n) * e <= x``
         THEN1 (MP_TAC (Q.SPEC `(z - x) / e` REAL_BIGNUM)
                THEN STRIP_TAC
                THEN Q.EXISTS_TAC `n`
                THEN Q.EXISTS_TAC `x`
                THEN RW_TAC boolSimps.bool_ss [REAL_LE_SUB_RADD]
                THEN ONCE_REWRITE_TAC [REAL_ADD_SYM]
                THEN REWRITE_TAC [GSYM REAL_LE_SUB_RADD]
                THEN (KNOW_TAC ``((z - x) / e) * e = (z:real) - x``
                      THEN1 (MATCH_MP_TAC REAL_DIV_RMUL
                             THEN PROVE_TAC [REAL_LT_LE]))
                THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
                THEN RW_TAC boolSimps.bool_ss [REAL_LE_RMUL]
                THEN MATCH_MP_TAC REAL_LE_TRANS
                THEN Q.EXISTS_TAC `&n`
                THEN REWRITE_TAC [REAL_LE]
                THEN PROVE_TAC
                     [arithmeticTheory.LESS_EQ_SUC_REFL, REAL_LT_LE]))
   THEN DISCH_THEN (MP_TAC o HO_MATCH_MP LEAST_EXISTS_IMP)
   THEN Q.SPEC_TAC (`$LEAST (\n. ?x. p x /\ z - & (SUC n) * e <= x)`, `m`)
   THEN RW_TAC boolSimps.bool_ss [GSYM IMP_DISJ_THM]
   THEN Q.EXISTS_TAC `m`
   THEN Q.EXISTS_TAC `x'`
   THEN ASM_REWRITE_TAC []
   THEN (Cases_on `m`
         THEN1 RW_TAC boolSimps.bool_ss [REAL_MUL_LZERO, REAL_SUB_RZERO])
   THEN POP_ASSUM (MP_TAC o Q.SPEC `n`)
   THEN RW_TAC boolSimps.bool_ss [prim_recTheory.LESS_SUC_REFL, GSYM real_lt]
   THEN PROVE_TAC [REAL_LT_LE]);

val REAL_LE_SUP = store_thm
  ("REAL_LE_SUP",
   ``!p x : real.
       (?y. p y) /\ (?y. !z. p z ==> z <= y) ==>
       (x <= sup p = !y. (!z. p z ==> z <= y) ==> x <= y)``,
   RW_TAC boolSimps.bool_ss []
   THEN EQ_TAC
   THENL [RW_TAC boolSimps.bool_ss []
          THEN MATCH_MP_TAC REAL_LE_EPSILON
          THEN RW_TAC boolSimps.bool_ss [GSYM REAL_LE_SUB_RADD]
          THEN (KNOW_TAC ``(x:real) - e < sup p``
                THEN1 (MATCH_MP_TAC REAL_LTE_TRANS
                       THEN Q.EXISTS_TAC `x`
                       THEN RW_TAC boolSimps.bool_ss
                            [REAL_LT_SUB_RADD, REAL_LT_ADDR]))
          THEN Q.PAT_ASSUM `0 < e` (K ALL_TAC)
          THEN Q.PAT_ASSUM `x <= sup p` (K ALL_TAC)
          THEN Q.SPEC_TAC (`x - e`, `x`)
          THEN GEN_TAC
          THEN MP_TAC (Q.SPEC `p` REAL_SUP_LE)
          THEN MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
          THEN (CONJ_TAC THEN1 PROVE_TAC [])
          THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
          THEN STRIP_TAC
          THEN MATCH_MP_TAC REAL_LE_TRANS
          THEN PROVE_TAC [REAL_LT_LE],
          RW_TAC boolSimps.bool_ss []
          THEN MATCH_MP_TAC REAL_LE_EPSILON
          THEN RW_TAC boolSimps.bool_ss [GSYM REAL_LE_SUB_RADD]
          THEN (SUFF_TAC ``(x:real) - e < sup p`` THEN1 PROVE_TAC [REAL_LT_LE])
          THEN Q.PAT_ASSUM `!y. P y` (MP_TAC o Q.SPEC `x - e`)
          THEN (KNOW_TAC ``!a b : real. a <= a - b = ~(0 < b)``
                THEN1 (RW_TAC boolSimps.bool_ss [real_lt, REAL_LE_SUB_LADD]
                       THEN PROVE_TAC [REAL_ADD_RID, REAL_LE_LADD]))
          THEN DISCH_THEN (fn th => ASM_REWRITE_TAC [th])
          THEN POP_ASSUM (K ALL_TAC)
          THEN Q.SPEC_TAC (`x - e`, `x`)
          THEN GEN_TAC
          THEN RW_TAC boolSimps.bool_ss []
          THEN MP_TAC (Q.SPEC `p` REAL_SUP_LE)
          THEN MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
          THEN (CONJ_TAC THEN1 PROVE_TAC [])
          THEN DISCH_THEN (fn th => REWRITE_TAC [GSYM th])
          THEN PROVE_TAC [real_lt]]);

val REAL_INF_LE = store_thm
  ("REAL_INF_LE",
   ``!p x : real.
       (?y. p y) /\ (?y. !z. p z ==> y <= z) ==>
       (inf p <= x = !y. (!z. p z ==> y <= z) ==> y <= x)``,
   RW_TAC boolSimps.bool_ss []
   THEN MP_TAC (Q.SPECL [`\r. p ~r`, `~x`] REAL_LE_SUP)
   THEN MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
   THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG])
   THEN ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   THEN REWRITE_TAC [GSYM inf_def]
   THEN REWRITE_TAC [REAL_LE_NEG]
   THEN RW_TAC boolSimps.bool_ss [REAL_NEGNEG]
   THEN POP_ASSUM (K ALL_TAC)
   THEN EQ_TAC
   THEN RW_TAC boolSimps.bool_ss []
   THEN Q.PAT_ASSUM `!a. (!b. P a b) ==> Q a` (MP_TAC o Q.SPEC `~y''`)
   THEN PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

val REAL_SUP_CONST = store_thm
  ("REAL_SUP_CONST",
   ``!x : real. sup (\r. r = x) = x``,
   RW_TAC boolSimps.bool_ss []
   THEN ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   THEN CONJ_TAC
   THENL [MATCH_MP_TAC REAL_IMP_SUP_LE
          THEN PROVE_TAC [REAL_LE_REFL],
          MATCH_MP_TAC REAL_IMP_LE_SUP
          THEN PROVE_TAC [REAL_LE_REFL]]);

(* ------------------------------------------------------------------------- *)
(* Theorems to put in the real simpset                                       *)
(* ------------------------------------------------------------------------- *)

val REAL_MUL_SUB2_CANCEL = store_thm
  ("REAL_MUL_SUB2_CANCEL",
   ``!z x y : real. x * y + (z - x) * y = z * y``,
   RW_TAC boolSimps.bool_ss [GSYM REAL_RDISTRIB, REAL_SUB_ADD2]);

val REAL_MUL_SUB1_CANCEL = store_thm
  ("REAL_MUL_SUB1_CANCEL",
   ``!z x y : real. y * x + y * (z - x) = y * z``,
   RW_TAC boolSimps.bool_ss [GSYM REAL_LDISTRIB, REAL_SUB_ADD2]);

val REAL_NEG_HALF = store_thm
  ("REAL_NEG_HALF",
   ``!x : real. x - x / 2 = x / 2``,
   STRIP_TAC
   THEN (SUFF_TAC ``((x:real) - x / 2) + x / 2 = x / 2 + x / 2``
         THEN1 RW_TAC boolSimps.bool_ss [REAL_EQ_RADD])
   THEN RW_TAC boolSimps.bool_ss [REAL_SUB_ADD, REAL_HALF_DOUBLE]);

val REAL_NEG_THIRD = store_thm
  ("REAL_NEG_THIRD",
   ``!x : real. x - x / 3 = (2 * x) / 3``,
   STRIP_TAC
   THEN MATCH_MP_TAC REAL_EQ_LMUL_IMP
   THEN Q.EXISTS_TAC `3`
   THEN (KNOW_TAC ``~(3r = 0)``
         THEN1 (REWRITE_TAC [REAL_INJ] THEN numLib.ARITH_TAC))
   THEN RW_TAC boolSimps.bool_ss [REAL_SUB_LDISTRIB, REAL_DIV_LMUL]
   THEN (KNOW_TAC ``!x y z : real. (y = 1 * x + z) ==> (y - x = z)``
         THEN1 RW_TAC boolSimps.bool_ss [REAL_MUL_LID, REAL_ADD_SUB])
   THEN DISCH_THEN MATCH_MP_TAC
   THEN RW_TAC boolSimps.bool_ss [GSYM REAL_ADD_RDISTRIB, REAL_ADD,
                                  REAL_EQ_RMUL, REAL_INJ]
   THEN DISJ2_TAC
   THEN numLib.ARITH_TAC);

val REAL_DIV_DENOM_CANCEL = store_thm
  ("REAL_DIV_DENOM_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((y / x) / (z / x) = y / z)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN (Cases_on `y = 0` THEN1 RW_TAC boolSimps.bool_ss [REAL_MUL_LZERO])
   THEN (Cases_on `z = 0`
         THEN1 RW_TAC boolSimps.bool_ss
               [REAL_INV_0, REAL_MUL_RZERO, REAL_MUL_LZERO])
   THEN RW_TAC boolSimps.bool_ss [REAL_INV_MUL, REAL_INV_EQ_0, REAL_INVINV]
   THEN (KNOW_TAC ``!a b c d : real. a * b * (c * d) = (a * c) * (b * d)``
         THEN1 metisLib.METIS_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_DENOM_CANCEL2 = save_thm
  ("REAL_DIV_DENOM_CANCEL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_DENOM_CANCEL));

val REAL_DIV_DENOM_CANCEL3 = save_thm
  ("REAL_DIV_DENOM_CANCEL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_DENOM_CANCEL));

val REAL_DIV_INNER_CANCEL = store_thm
  ("REAL_DIV_INNER_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((y / x) * (x / z) = y / z)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN (KNOW_TAC ``!a b c d : real. a * b * (c * d) = (a * d) * (b * c)``
         THEN1 metisLib.METIS_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_INNER_CANCEL2 = save_thm
  ("REAL_DIV_INNER_CANCEL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_INNER_CANCEL));

val REAL_DIV_INNER_CANCEL3 = save_thm
  ("REAL_DIV_INNER_CANCEL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_INNER_CANCEL));

val REAL_DIV_OUTER_CANCEL = store_thm
  ("REAL_DIV_OUTER_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((x / y) * (z / x) = z / y)``,
   RW_TAC boolSimps.bool_ss [real_div]
   THEN (KNOW_TAC ``!a b c d : real. a * b * (c * d) = (a * d) * (c * b)``
         THEN1 metisLib.METIS_TAC [REAL_MUL_SYM, REAL_MUL_ASSOC])
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [th])
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_RINV, REAL_MUL_LID]);

val REAL_DIV_OUTER_CANCEL2 = save_thm
  ("REAL_DIV_OUTER_CANCEL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_OUTER_CANCEL));

val REAL_DIV_OUTER_CANCEL3 = save_thm
  ("REAL_DIV_OUTER_CANCEL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_OUTER_CANCEL));

val REAL_DIV_REFL2 = save_thm
  ("REAL_DIV_REFL2",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(2n = 0)``, REAL_INJ]
   (Q.SPEC `2` REAL_DIV_REFL));

val REAL_DIV_REFL3 = save_thm
  ("REAL_DIV_REFL3",
   SIMP_RULE boolSimps.bool_ss [numLib.ARITH_PROVE ``~(3n = 0)``, REAL_INJ]
   (Q.SPEC `3` REAL_DIV_REFL));

val REAL_HALF_BETWEEN = store_thm
  ("REAL_HALF_BETWEEN",
   ``((0:real) <  1 / 2 /\ 1 / 2 <  (1:real)) /\
     ((0:real) <= 1 / 2 /\ 1 / 2 <= (1:real))``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_TOTAL, real_lt])
   THEN RW_TAC boolSimps.bool_ss [real_lt]
   THEN MP_TAC (Q.SPEC `2` REAL_LE_LMUL)
   THEN (KNOW_TAC ``0r < 2 /\ ~(2r = 0)``
         THEN1 (REWRITE_TAC [REAL_LT, REAL_INJ] THEN numLib.ARITH_TAC))
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   THEN ONCE_REWRITE_TAC [REAL_MUL_SYM]
   THEN RW_TAC boolSimps.bool_ss [real_div, GSYM REAL_MUL_ASSOC]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_INJ]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL, REAL_LE]
   THEN numLib.ARITH_TAC);

val REAL_THIRDS_BETWEEN = store_thm
  ("REAL_THIRDS_BETWEEN",
   ``((0:real) <  1 / 3 /\ 1 / 3 <  (1:real) /\
      (0:real) <  2 / 3 /\ 2 / 3 <  (1:real)) /\
     ((0:real) <= 1 / 3 /\ 1 / 3 <= (1:real) /\
      (0:real) <= 2 / 3 /\ 2 / 3 <= (1:real))``,
   MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_TOTAL, real_lt])
   THEN RW_TAC boolSimps.bool_ss [real_lt]
   THEN MP_TAC (Q.SPEC `3` REAL_LE_LMUL)
   THEN (KNOW_TAC ``0r < 3 /\ ~(3r = 0)``
         THEN1 (REWRITE_TAC [REAL_LT, REAL_INJ] THEN numLib.ARITH_TAC))
   THEN STRIP_TAC
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   THEN ONCE_REWRITE_TAC [REAL_MUL_SYM]
   THEN RW_TAC boolSimps.bool_ss [real_div, GSYM REAL_MUL_ASSOC]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL_LINV, REAL_INJ]
   THEN RW_TAC boolSimps.bool_ss [REAL_MUL, REAL_LE]
   THEN numLib.ARITH_TAC);

val REAL_LE_SUB_CANCEL2 = store_thm
  ("REAL_LE_SUB_CANCEL2",
   ``!x y z : real. x - z <= y - z = x <= y``,
   RW_TAC boolSimps.bool_ss [REAL_LE_SUB_RADD, REAL_SUB_ADD]);

val REAL_ADD_SUB_ALT = store_thm
  ("REAL_ADD_SUB_ALT",
   ``!x y : real. (x + y) - y = x``,
   RW_TAC boolSimps.bool_ss [REAL_EQ_SUB_RADD]);

val INFINITE_REAL_UNIV = store_thm(
  "INFINITE_REAL_UNIV",
  ``INFINITE univ(:real)``,
  REWRITE_TAC [pred_setTheory.INFINITE_DEF] THEN STRIP_TAC THEN
  `FINITE (IMAGE real_of_num univ(:num))`
     by METIS_TAC [pred_setTheory.SUBSET_FINITE,
                   pred_setTheory.SUBSET_UNIV] THEN
  FULL_SIMP_TAC (srw_ss()) [pred_setTheory.INJECTIVE_IMAGE_FINITE]);
val _ = export_rewrites ["INFINITE_REAL_UNIV"]

(* ----------------------------------------------------------------------
   theorems for calculating with the reals; naming scheme taken from
   Joe Hurd's development of the positive reals with an infinity
  ---------------------------------------------------------------------- *)

local open markerTheory in end; (* for unint *)

val ui = markerTheory.unint_def

val add_rat = store_thm(
  "add_rat",
  ``x / y + u / v =
      if y = 0 then unint (x/y) + u/v
      else if v = 0 then x/y + unint (u/v)
      else if y = v then (x + u) / v
      else (x * v + u * y) / (y * v)``,
  SRW_TAC [][ui, REAL_DIV_LZERO, REAL_DIV_ADD] THEN
  SRW_TAC [][REAL_ADD_RAT, REAL_MUL_COMM]);

val add_ratl = store_thm(
  "add_ratl",
  ``x / y + z =
      if y = 0 then unint(x/y) + z
      else (x + z * y) / y``,
  SRW_TAC [][ui, REAL_DIV_LZERO] THEN
  `z = z/1` by SRW_TAC [][] THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  SRW_TAC [][REAL_ADD_RAT, REAL_MUL_COMM]);

val add_ratr = store_thm(
  "add_ratr",
  ``x + y / z =
      if z = 0 then x + unint (y/z)
      else (x * z + y) / z``,
  ONCE_REWRITE_TAC [REAL_ADD_COMM] THEN
  SRW_TAC [][add_ratl, REAL_DIV_LZERO]);

val add_ints = store_thm(
  "add_ints",
  ``(&n + &m = &(n + m)) /\
    (~&n + &m = if n <= m then &(m - n) else ~&(n - m)) /\
    (&n + ~&m = if n < m then ~&(m - n) else &(n - m)) /\
    (~&n + ~&m = ~&(n + m))``,
  `!x y. ~x + y = y + ~x` by SRW_TAC [][REAL_ADD_COMM] THEN
  SRW_TAC [][GSYM REAL_NEG_ADD, GSYM real_sub, REAL_SUB] THEN
  FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss) [] THEN
  `m = n` by SRW_TAC [old_ARITH_ss][] THEN SRW_TAC [][])

val mult_rat = store_thm(
  "mult_rat",
  ``(x / y) * (u / v) =
       if y = 0 then unint (x/y) * (u/v)
       else if v = 0 then (x/y) * unint(u/v)
       else (x * u) / (y * v)``,
  SRW_TAC [][ui, REAL_DIV_LZERO] THEN
  SRW_TAC [][REAL_DIV_LZERO] THEN
  MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN
  Q.EXISTS_TAC `y * v` THEN ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_ENTIRE] THEN
  SRW_TAC [][REAL_DIV_LMUL, REAL_ENTIRE] THEN
  `y * v * (x / y) * (u / v) = (y * (x / y)) * (v * (u / v))`
     by CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM)) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  SRW_TAC [][REAL_DIV_LMUL]);

val mult_ratl = store_thm(
  "mult_ratl",
  ``(x / y) * z = if y = 0 then unint (x/y) * z else (x * z) / y``,
  SRW_TAC [][ui] THEN
  SRW_TAC [][REAL_DIV_LZERO] THEN
  `z = z / 1` by SRW_TAC [][] THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) THEN
  REWRITE_TAC [mult_rat] THEN SRW_TAC [][]);

val mult_ratr = store_thm(
  "mult_ratr",
  ``x * (y/z) = if z = 0 then x * unint (y/z) else (x * y) / z``,
  CONV_TAC (LAND_CONV (REWR_CONV REAL_MUL_COMM)) THEN
  SRW_TAC [][mult_ratl] THEN SRW_TAC [][ui, REAL_MUL_COMM]);

val mult_ints = store_thm(
  "mult_ints",
  ``(&a * &b = &(a * b)) /\
    (~&a * &b = ~&(a * b)) /\
    (&a * ~&b = ~&(a * b)) /\
    (~&a * ~&b = &(a * b))``,
  SRW_TAC [][REAL_MUL_LNEG, REAL_MUL_RNEG]);

val pow_rat = store_thm(
  "pow_rat",
  ``(x pow 0 = 1) /\
    (0 pow (NUMERAL (BIT1 n)) = 0) /\
    (0 pow (NUMERAL (BIT2 n)) = 0) /\
    (&(NUMERAL a) pow (NUMERAL n) = &(NUMERAL a EXP NUMERAL n)) /\
    (~&(NUMERAL a) pow (NUMERAL n) =
      (if ODD (NUMERAL n) then (~) else (\x.x))
      (&(NUMERAL a EXP NUMERAL n))) /\
    ((x / y) pow n = (x pow n) / (y pow n))``,
  SIMP_TAC bool_ss [pow, NUMERAL_DEF, BIT1, BIT2, POW_ADD,
                    ALT_ZERO, ADD_CLAUSES, REAL_MUL, MULT_CLAUSES,
                    REAL_MUL_RZERO, REAL_OF_NUM_POW, REAL_POW_DIV, EXP] THEN
  Induct_on `n` THEN ASM_SIMP_TAC bool_ss [pow, ODD, EXP] THEN
  Cases_on `ODD n` THEN
  ASM_SIMP_TAC bool_ss [REAL_MUL, REAL_MUL_LNEG,
                        REAL_MUL_RNEG, REAL_NEG_NEG]);

val neg_rat = store_thm(
  "neg_rat",
  ``(~(x / y) = if y = 0 then ~ (unint(x/y)) else ~x / y) /\
    (x / ~y   = if y = 0 then unint(x/y) else ~x/y)``,
  SRW_TAC [][ui] THEN
  SRW_TAC [][real_div, GSYM REAL_NEG_INV, REAL_MUL_LNEG, REAL_MUL_RNEG]);

val eq_rat = store_thm(
  "eq_rat",
  ``(x / y = u / v) = if y = 0 then unint (x/y) = u / v
                      else if v = 0 then x / y = unint (u/v)
                      else if y = v then x = u
                      else x * v = y * u``,
  SRW_TAC [][ui] THENL [
    METIS_TAC [REAL_DIV_LMUL, REAL_EQ_LMUL],
    `~(y * v = 0)` by SRW_TAC [][REAL_ENTIRE] THEN
    `(x/y = u/v) = ((y * v) * (x/y) = (y * v) * (u/v))`
       by METIS_TAC [REAL_EQ_LMUL2] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `((y * v) * (x/y) = v * (y * (x/y))) /\
     ((y * v) * (u/v) = y * (v * (u/v)))`
       by (CONJ_TAC THEN
           CONV_TAC (AC_CONV(REAL_MUL_ASSOC, REAL_MUL_COMM))) THEN
    ASM_REWRITE_TAC [] THEN SRW_TAC [][REAL_DIV_LMUL] THEN
    SRW_TAC [][REAL_MUL_COMM]
  ]);

val eq_ratl = store_thm(
  "eq_ratl",
  ``(x/y = z) = if y = 0 then unint(x/y) = z else x = y * z``,
  SRW_TAC [][ui] THEN METIS_TAC [REAL_DIV_LMUL, REAL_EQ_LMUL]);

val eq_ratr = store_thm(
  "eq_ratr",
  ``(z = x/y) = if y = 0 then z = unint(x/y) else y * z = x``,
  METIS_TAC [eq_ratl]);

val eq_ints = store_thm(
  "eq_ints",
  ``((&n = &m) = (n = m)) /\
    ((~&n = &m) = (n = 0) /\ (m = 0)) /\
    ((&n = ~&m) = (n = 0) /\ (m = 0)) /\
    ((~&n = ~&m) = (n = m))``,
  REWRITE_TAC [REAL_INJ, REAL_EQ_NEG] THEN
  Q_TAC SUFF_TAC `!n m. (&n = ~&m) = (n = 0) /\ (m = 0)` THEN1
      METIS_TAC [] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN
    `&n <= ~&m` by METIS_TAC [REAL_LE_ANTISYM] THEN
    `0 <= ~&m` by METIS_TAC [REAL_LE_TRANS, REAL_LE,
                             arithmeticTheory.ZERO_LESS_EQ] THEN
    `m <= 0` by METIS_TAC [REAL_LE, REAL_NEG_GE0] THEN
    `m = 0` by SRW_TAC [old_ARITH_ss][] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][]
  ]);

val REALMUL_AC = CONV_TAC (AC_CONV (REAL_MUL_ASSOC, REAL_MUL_COMM))

val div_ratr = store_thm(
  "div_ratr",
  ``x / (y / z) = if (y = 0) \/ (z = 0) then x / unint(y/z)
                  else x * z / y``,
  SRW_TAC [][ui] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][real_div, REAL_INV_MUL, REAL_INV_EQ_0, REAL_INV_INV] THEN
  REALMUL_AC);

val div_ratl = store_thm(
  "div_ratl",
  ``(x/y) / z = if y = 0 then unint(x/y) / z
                else if z = 0 then unint((x/y)/ z)
                else x / (y * z)``,
  SRW_TAC [][ui, real_div, REAL_INV_MUL, REAL_INV_EQ_0, REAL_INV_INV] THEN
  REALMUL_AC);



val div_rat = store_thm(
  "div_rat",
  ``(x/y) / (u/v) =
      if (u = 0) \/ (v = 0) then (x/y) / unint (u/v)
      else if y = 0 then unint(x/y) / (u/v)
      else (x * v) / (y * u)``,
  SRW_TAC [][ui] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][real_div, REAL_INV_MUL, REAL_INV_EQ_0, REAL_INV_INV] THEN
  REALMUL_AC);

val le_rat = store_thm(
  "le_rat",
  ``x / &n <= u / &m = if n = 0 then unint(x/0) <= u / &m
                       else if m = 0 then x/ &n <= unint(u/0)
                       else &m * x <= &n * u``,
  SRW_TAC [][ui] THEN
  `0 < m /\ 0 < n` by SRW_TAC [old_ARITH_ss][] THEN
  `0 < &m * &n` by SRW_TAC [][REAL_LT_MUL] THEN
  POP_ASSUM (ASSUME_TAC o MATCH_MP REAL_LE_LMUL) THEN
  POP_ASSUM (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [GSYM th]))) THEN
  `&m * &n * (x / &n) = &m * (&n * (x/ &n))` by REALMUL_AC THEN
  `&m * &n * (u / &m) = &n * (&m * (u / &m))` by REALMUL_AC THEN
  SRW_TAC [][REAL_DIV_LMUL]);

val le_ratl = save_thm(
  "le_ratl",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``m:num`` |-> ``1n``] le_rat));

val le_ratr = save_thm(
  "le_ratr",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``n:num`` |-> ``1n``] le_rat));

val le_int = store_thm(
  "le_int",
  ``(&n <= &m = n <= m) /\
    (~&n <= &m = T) /\
    (&n <= ~&m = (n = 0) /\ (m = 0)) /\
    (~&n <= ~&m = m <= n)``,
  SRW_TAC [][REAL_LE_NEG] THENL [
    MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `0` THEN SRW_TAC [][REAL_NEG_LE0],
    Cases_on `m` THEN SRW_TAC [][REAL_NEG_LE0] THEN
    SRW_TAC [][REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    Q.EXISTS_TAC `0` THEN SRW_TAC [][REAL_NEG_LT0]
  ]);

val lt_rat = store_thm(
  "lt_rat",
  ``x / &n < u / &m = if n = 0 then unint(x/0) < u / &m
                      else if m = 0 then x / & n < unint(u/0)
                      else &m * x < &n * u``,
  SRW_TAC [][ui] THEN
  `0 < m /\ 0 < n` by SRW_TAC [old_ARITH_ss][] THEN
  `0 < &m * &n` by SRW_TAC [][REAL_LT_MUL] THEN
  POP_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_LMUL) THEN
  POP_ASSUM (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [GSYM th]))) THEN
  `&m * &n * (x / &n) = &m * (&n * (x / &n))` by REALMUL_AC THEN
  `&m * &n * (u / &m) = &n * (&m * (u / &m))` by REALMUL_AC THEN
  SRW_TAC [][REAL_DIV_LMUL]);

val lt_ratl = save_thm(
  "lt_ratl",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``m:num`` |-> ``1n``] lt_rat));

val lt_ratr = save_thm(
  "lt_ratr",
  SIMP_RULE (srw_ss()) [] (Thm.INST [``n:num`` |-> ``1n``] lt_rat));

val lt_int = store_thm(
  "lt_int",
  ``(&n < &m = n < m) /\
    (~&n < &m = ~(n = 0) \/ ~(m = 0)) /\
    (&n < ~&m = F) /\
    (~&n < ~&m = m < n)``,
  SRW_TAC [][REAL_LT_NEG] THENL [
    Cases_on `m` THEN SRW_TAC [old_ARITH_ss][REAL_NEG_LT0] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `0` THEN
    SRW_TAC [old_ARITH_ss][REAL_NEG_LE0],
    SRW_TAC [][REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    Q.EXISTS_TAC `0` THEN SRW_TAC [][REAL_NEG_LE0]
  ]);


(*---------------------------------------------------------------------------*)
(* Floor and ceiling (nums)                                                  *)
(*---------------------------------------------------------------------------*)

val NUM_FLOOR_def =
 Define
   `NUM_FLOOR (x:real) = LEAST (n:num). real_of_num (n+1) > x`;

val NUM_CEILING_def =
 Define
   `NUM_CEILING (x:real) = LEAST (n:num). x <= real_of_num(n)`;

val _ = overload_on ("flr",``NUM_FLOOR``);
val _ = overload_on ("clg",``NUM_CEILING``);

val lem = SIMP_RULE arith_ss [REAL_POS,REAL_ADD_RID]
              (Q.SPECL[`y`,`&n`,`0r`,`1r`] REAL_LTE_ADD2);

val add1_gt_exists = prove(
  ``!y : real. ?n. & (n + 1) > y``,
  GEN_TAC THEN Q.SPEC_THEN `1` MP_TAC REAL_ARCH THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `n` THEN
  SIMP_TAC arith_ss [GSYM REAL_ADD,real_gt,REAL_LT_ADDL,REAL_LT_ADDR] THEN
  METIS_TAC [lem]);

val lt_add1_exists = prove(
  ``!y: real. ?n. y < &(n + 1)``,
  GEN_TAC THEN Q.SPEC_THEN `1` MP_TAC REAL_ARCH THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `n` THEN
  SIMP_TAC bool_ss [GSYM REAL_ADD] THEN METIS_TAC [lem]);

val NUM_FLOOR_LE = store_thm
("NUM_FLOOR_LE",
  ``0 <= x ==> &(NUM_FLOOR x) <= x``,
  SRW_TAC [][NUM_FLOOR_def] THEN
  LEAST_ELIM_TAC THEN
  SRW_TAC [][add1_gt_exists] THEN
  Cases_on `n` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
  SRW_TAC [old_ARITH_ss] [real_gt, REAL_NOT_LT, ADD1]);

val NUM_FLOOR_LE2 = store_thm
("NUM_FLOOR_LE2",
 ``0 <= y ==> (x <= NUM_FLOOR y = &x <= y)``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][lt_add1_exists, real_gt,REAL_NOT_LT, EQ_IMP_THM]
  THENL [
    Cases_on `n` THENL [
      FULL_SIMP_TAC (srw_ss()) [],
      FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
      FULL_SIMP_TAC (bool_ss ++ old_ARITH_ss)
                    [ADD1, GSYM REAL_ADD, GSYM REAL_LE] THEN
      METIS_TAC [REAL_LE_TRANS]
    ],
    `&x < &(n + 1):real` by PROVE_TAC [REAL_LET_TRANS] THEN
    FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss) []
  ]);

val NUM_FLOOR_LET = store_thm
("NUM_FLOOR_LET",
 ``(NUM_FLOOR x <= y) = (x < &y + 1)``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][lt_add1_exists, real_gt,REAL_NOT_LT, EQ_IMP_THM]
  THENL [
    FULL_SIMP_TAC bool_ss [GSYM REAL_LE,GSYM REAL_ADD] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    Q.EXISTS_TAC `&n + 1` THEN SRW_TAC [][],
    Cases_on `n` THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
    FULL_SIMP_TAC (bool_ss ++ old_ARITH_ss) [ADD1] THEN
    STRIP_TAC THEN
    `&(n' + 1) < &(y + 1):real` by METIS_TAC [REAL_LET_TRANS] THEN
    FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss) []
  ]);

val NUM_FLOOR_DIV = store_thm
("NUM_FLOOR_DIV",
  ``0 <= x /\ 0 < y ==> &(NUM_FLOOR (x / y)) * y <= x``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][add1_gt_exists] THEN
  Cases_on `n` THEN1 SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `n'` MP_TAC) THEN
  SRW_TAC [old_ARITH_ss] [real_gt,REAL_NOT_LT,ADD1,REAL_LE_RDIV_EQ]);

val NUM_FLOOR_DIV_LOWERBOUND = store_thm
("NUM_FLOOR_DIV_LOWERBOUND",
 ``0 <= x:real /\ 0 < y:real ==> x < &(NUM_FLOOR (x/y) + 1) * y ``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THEN
  SRW_TAC [][add1_gt_exists] THEN Cases_on `n` THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][real_gt, REAL_LT_LDIV_EQ]);

val NUM_FLOOR_EQNS = store_thm(
 "NUM_FLOOR_EQNS",
  ``(NUM_FLOOR (real_of_num n) = n) /\
    (0 < m ==> (NUM_FLOOR (real_of_num n / real_of_num m) = n DIV m))``,
  SRW_TAC [][NUM_FLOOR_def] THEN LEAST_ELIM_TAC THENL [
    SIMP_TAC (srw_ss()) [real_gt, REAL_LT] THEN
    CONJ_TAC THENL
     [Q.EXISTS_TAC `n` THEN RW_TAC old_arith_ss [],
      Cases THEN FULL_SIMP_TAC old_arith_ss []
        THEN STRIP_TAC
        THEN Q.PAT_ASSUM `$! M` (MP_TAC o Q.SPEC `n''`)
        THEN RW_TAC old_arith_ss []],
    ASM_SIMP_TAC (srw_ss()) [real_gt, REAL_LT_LDIV_EQ] THEN
    CONJ_TAC THENL [
      Q.EXISTS_TAC `n` THEN
      SRW_TAC [][RIGHT_ADD_DISTRIB] THEN
      MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
      Q.EXISTS_TAC `n * m` THEN
      SRW_TAC [old_ARITH_ss][] THEN
      CONV_TAC (LAND_CONV (REWR_CONV (GSYM MULT_RIGHT_1))) THEN
      SRW_TAC [old_ARITH_ss][],
      Q.HO_MATCH_ABBREV_TAC
         `!p:num. (!i. i < p ==> ~(n < (i + 1) * m)) /\ n < (p + 1) * m
                   ==> (p = n DIV m)` THEN
      REPEAT STRIP_TAC THEN
      CONV_TAC (REWR_CONV EQ_SYM_EQ) THEN
      MATCH_MP_TAC DIV_UNIQUE THEN
      `(p = 0) \/ (?p0. p = SUC p0)`
         by PROVE_TAC [arithmeticTheory.num_CASES] THEN
      FULL_SIMP_TAC (srw_ss() ++ old_ARITH_ss)
                    [ADD1,RIGHT_ADD_DISTRIB] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `p0` MP_TAC) THEN
      SRW_TAC [old_ARITH_ss][NOT_LESS] THEN
      Q.EXISTS_TAC `n - (m + p0 * m)` THEN
      SRW_TAC [old_ARITH_ss][]
    ]
  ]);

val NUM_FLOOR_LOWER_BOUND = store_thm(
  "NUM_FLOOR_LOWER_BOUND",
  ``(x:real < &n) = (NUM_FLOOR(x+1) <= n)``,
  MP_TAC (Q.INST [`x` |-> `x + 1`, `y` |-> `n`] NUM_FLOOR_LET) THEN
  SIMP_TAC (srw_ss()) []);

val NUM_FLOOR_UPPER_BOUND = store_thm(
  "NUM_FLOOR_upper_bound",
  ``(&n <= x:real) = (n < NUM_FLOOR(x + 1))``,
  MP_TAC (AP_TERM negation NUM_FLOOR_LOWER_BOUND) THEN
  PURE_REWRITE_TAC [REAL_NOT_LT, NOT_LESS_EQUAL,IMP_CLAUSES]);

(*---------------------------------------------------------------------------*)
(* Ceiling function                                                          *)
(*---------------------------------------------------------------------------*)

val LE_NUM_CEILING = store_thm
("LE_NUM_CEILING",
 ``!x. x <= &(clg x)``,
 RW_TAC std_ss [NUM_CEILING_def]
   THEN numLib.LEAST_ELIM_TAC
   THEN Q.SPEC_THEN `1` MP_TAC REAL_ARCH
   THEN SIMP_TAC (srw_ss()) []
   THEN METIS_TAC [REAL_LT_IMP_LE]);

val NUM_CEILING_LE = store_thm
("NUM_CEILING_LE",
 ``!x n. x <= &n ==> clg(x) <= n``,
 RW_TAC std_ss [NUM_CEILING_def]
   THEN numLib.LEAST_ELIM_TAC
   THEN METIS_TAC [NOT_LESS_EQUAL]);

val _ = export_theory();

end
