(*---------------------------------------------------------------------------*)
(* Construct positive reals from positive rationals                          *)
(*---------------------------------------------------------------------------*)

structure hrealScript =
struct

(*
app load ["hol88Lib",
          "numLib",
          "reduceLib",
          "pairTheory",
          "arithmeticTheory",
          "jrhUtils",
          "hratTheory"];
*)

open HolKernel Parse boolLib
     hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory
     prim_recTheory jrhUtils hratTheory;

infix THEN THENL ORELSE ORELSEC;

val _ = new_theory "hreal";

(*---------------------------------------------------------------------------*)
(* Lemmas about the half-rationals, including definition of ordering         *)
(*---------------------------------------------------------------------------*)

val hrat_lt = new_definition("hrat_lt",
  (--`$hrat_lt x y = ?d. y = x hrat_add d`--));
val _ = temp_set_fixity "hrat_lt" (Infix(NONASSOC, 450))

val HRAT_LT_REFL = store_thm("HRAT_LT_REFL",
  (--`!x. ~(x hrat_lt x)`--),
  GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[HRAT_NOZERO]);

val HRAT_LT_TRANS = store_thm("HRAT_LT_TRANS",
  (--`!x y z. x hrat_lt y /\ y hrat_lt z ==> x hrat_lt z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 CHOOSE_TAC (CHOOSE_THEN SUBST1_TAC)) THEN
  POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[GSYM HRAT_ADD_ASSOC] THEN
  W(EXISTS_TAC o rand o lhs o body o rand o snd) THEN REFL_TAC);

val HRAT_LT_ANTISYM = store_thm("HRAT_LT_ANTISYM",
  (--`!x y. ~(x hrat_lt y /\ y hrat_lt x)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HRAT_LT_TRANS) THEN
  REWRITE_TAC[HRAT_LT_REFL]);

val HRAT_LT_TOTAL = store_thm("HRAT_LT_TOTAL",
  (--`!x y. (x = y) \/ x hrat_lt y \/ y hrat_lt x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  REPEAT_TCL DISJ_CASES_THEN (SUBST1_TAC o EQT_INTRO)
   (SPECL [(--`x:hrat`--), (--`y:hrat`--)] HRAT_ADD_TOTAL) THEN
  REWRITE_TAC[]);

val HRAT_MUL_RID = store_thm("HRAT_MUL_RID",
  (--`!x. x hrat_mul hrat_1 = x`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_MUL_LID);

val HRAT_MUL_RINV = store_thm("HRAT_MUL_RINV",
  (--`!x. x hrat_mul (hrat_inv x) = hrat_1`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_MUL_LINV);

val HRAT_RDISTRIB = store_thm("HRAT_RDISTRIB",
  (--`!x y z. (x hrat_add y) hrat_mul z =
     (x hrat_mul z) hrat_add (y hrat_mul z)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LDISTRIB);

val HRAT_LT_ADDL = store_thm("HRAT_LT_ADDL",
  (--`!x y. x hrat_lt (x hrat_add y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  EXISTS_TAC (--`y:hrat`--) THEN REFL_TAC);

val HRAT_LT_ADDR = store_thm("HRAT_LT_ADDR",
  (--`!x y. y hrat_lt (x hrat_add y)`--),
  ONCE_REWRITE_TAC[HRAT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_ADDL);

val HRAT_LT_GT = store_thm("HRAT_LT_GT",
  (--`!x y. x hrat_lt y ==> ~(y hrat_lt x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM HRAT_ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[HRAT_NOZERO]);

val HRAT_LT_NE = store_thm("HRAT_LT_NE",
  (--`!x y. x hrat_lt y ==> ~(x = y)`--),
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC HRAT_LT_REFL);

val HRAT_EQ_LADD = store_thm("HRAT_EQ_LADD",
  (--`!x y z. (x hrat_add y = x hrat_add z) = (y = z)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (SPECL [(--`y:hrat`--), (--`z:hrat`--)] HRAT_ADD_TOTAL) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[HRAT_ADD_ASSOC, HRAT_NOZERO, GSYM HRAT_NOZERO],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val HRAT_EQ_LMUL = store_thm("HRAT_EQ_LMUL",
  (--`!x y z. (x hrat_mul y = x hrat_mul z) = (y = z)`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$hrat_mul (hrat_inv x)`--)) THEN
    REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_LID],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val HRAT_LT_ADD2 = store_thm("HRAT_LT_ADD2",
  (--`!u v x y. u hrat_lt x /\ v hrat_lt y ==>
     (u hrat_add v) hrat_lt (x hrat_add y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN (--`d1:hrat`--) SUBST1_TAC)
    (X_CHOOSE_THEN (--`d2:hrat`--) SUBST1_TAC)) THEN
  EXISTS_TAC (--`d1 hrat_add d2`--) THEN
  CONV_TAC(AC_CONV(HRAT_ADD_ASSOC,HRAT_ADD_SYM)));

val HRAT_LT_LADD = store_thm("HRAT_LT_LADD",
  (--`!x y z. (z hrat_add x) hrat_lt (z hrat_add y) = x hrat_lt y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:hrat`--) (curry op THEN (EXISTS_TAC (--`d:hrat`--)) o MP_TAC))
  THEN REWRITE_TAC[GSYM HRAT_ADD_ASSOC, HRAT_EQ_LADD]);

val HRAT_LT_RADD = store_thm("HRAT_LT_RADD",
  (--`!x y z. (x hrat_add z) hrat_lt (y hrat_add z) = x hrat_lt y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_LADD);

val HRAT_LT_MUL2 = store_thm("HRAT_LT_MUL2",
  (--`!u v x y. u hrat_lt x /\ v hrat_lt y ==>
     (u hrat_mul v) hrat_lt (x hrat_mul y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN (--`d1:hrat`--) SUBST1_TAC)
    (X_CHOOSE_THEN (--`d2:hrat`--) SUBST1_TAC)) THEN
  REWRITE_TAC[HRAT_LDISTRIB, HRAT_RDISTRIB, GSYM HRAT_ADD_ASSOC] THEN
  REWRITE_TAC[HRAT_EQ_LADD] THEN
  W(EXISTS_TAC o lhs o body o rand o snd) THEN REFL_TAC);

val HRAT_LT_LMUL = store_thm("HRAT_LT_LMUL",
  (--`!x y z. (z hrat_mul x) hrat_lt (z hrat_mul y) = x hrat_lt y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC (--`d:hrat`--)) THENL
   [EXISTS_TAC (--`(hrat_inv z) hrat_mul d`--),
    EXISTS_TAC (--`z hrat_mul d`--)] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM HRAT_LDISTRIB, GSYM HRAT_MUL_ASSOC, HRAT_EQ_LMUL] THEN
  DISCH_THEN(MP_TAC o AP_TERM (--`$hrat_mul (hrat_inv z)`--)) THEN
  REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_LID, HRAT_LDISTRIB]);

val HRAT_LT_RMUL = store_thm("HRAT_LT_RMUL",
  (--`!x y z. (x hrat_mul z) hrat_lt (y hrat_mul z) = x hrat_lt y`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL);

val HRAT_LT_LMUL1 = store_thm("HRAT_LT_LMUL1",
  (--`!x y. (x hrat_mul y) hrat_lt y = x hrat_lt hrat_1`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM HRAT_MUL_LID] THEN
  MATCH_ACCEPT_TAC HRAT_LT_RMUL);

val HRAT_LT_RMUL1 = store_thm("HRAT_LT_RMUL1",
  (--`!x y. (x hrat_mul y) hrat_lt x = y hrat_lt hrat_1`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL1);

val HRAT_GT_LMUL1 = store_thm("HRAT_GT_LMUL1",
  (--`!x y. y hrat_lt (x hrat_mul y) = hrat_1 hrat_lt x`--),
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (funpow 2 LAND_CONV) [GSYM HRAT_MUL_LID]
  THEN MATCH_ACCEPT_TAC HRAT_LT_RMUL);

val HRAT_LT_L1 = store_thm("HRAT_LT_L1",
  (--`!x y. ((hrat_inv x) hrat_mul y) hrat_lt hrat_1 = y hrat_lt x`--),
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(SPEC (--`x:hrat`--) HRAT_MUL_LINV)) THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL);

val HRAT_LT_R1 = store_thm("HRAT_LT_R1",
  (--`!x y. (x hrat_mul (hrat_inv y)) hrat_lt hrat_1 = x hrat_lt y`--),
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(SPEC (--`y:hrat`--) HRAT_MUL_RINV)) THEN
  MATCH_ACCEPT_TAC HRAT_LT_RMUL);

val HRAT_GT_L1 = store_thm("HRAT_GT_L1",
  (--`!x y. hrat_1 hrat_lt ((hrat_inv x) hrat_mul y) = x hrat_lt y`--),
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(SPEC (--`x:hrat`--) HRAT_MUL_LINV)) THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL);

val HRAT_INV_MUL = store_thm("HRAT_INV_MUL",
  (--`!x y. hrat_inv (x hrat_mul y) = (hrat_inv x) hrat_mul (hrat_inv y)`--),
  REPEAT GEN_TAC THEN SUBST1_TAC
    (SYM(SPECL [(--`x hrat_mul y`--), (--`hrat_inv (x hrat_mul y)`--),
                (--`(hrat_inv x) hrat_mul (hrat_inv y)`--)] HRAT_EQ_LMUL)) THEN
  ONCE_REWRITE_TAC[AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
    (--`(a hrat_mul b) hrat_mul (c hrat_mul d) =
     (a hrat_mul c) hrat_mul (b hrat_mul d)`--)] THEN
  REWRITE_TAC[HRAT_MUL_RINV, HRAT_MUL_LID]);

val HRAT_UP = store_thm("HRAT_UP",
  (--`!x. ?y. x hrat_lt y`--),
  GEN_TAC THEN EXISTS_TAC (--`x hrat_add x`--) THEN
  REWRITE_TAC[hrat_lt] THEN EXISTS_TAC (--`x:hrat`--) THEN REFL_TAC);

val HRAT_DOWN = store_thm("HRAT_DOWN",
  (--`!x. ?y. y hrat_lt x`--),
  GEN_TAC THEN
  EXISTS_TAC (--`x hrat_mul (hrat_inv (hrat_1 hrat_add hrat_1))`--) THEN
  REWRITE_TAC[HRAT_LT_RMUL1] THEN
  GEN_REWR_TAC LAND_CONV [GSYM HRAT_MUL_LID] THEN
  REWRITE_TAC[HRAT_LT_R1] THEN REWRITE_TAC[hrat_lt] THEN
  EXISTS_TAC (--`hrat_1`--) THEN REFL_TAC);

val HRAT_DOWN2 = store_thm("HRAT_DOWN2",
  (--`!x y. ?z. z hrat_lt x /\ z hrat_lt y`--),
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [(--`x:hrat`--), (--`y:hrat`--)] HRAT_ADD_TOTAL) THEN
  ASM_REWRITE_TAC[HRAT_DOWN] THEN
  POP_ASSUM(X_CHOOSE_THEN (--`d:hrat`--) SUBST1_TAC) THENL
   [X_CHOOSE_TAC (--`z:hrat`--) (SPEC (--`y:hrat`--) HRAT_DOWN),
    X_CHOOSE_TAC (--`z:hrat`--) (SPEC (--`x:hrat`--) HRAT_DOWN)] THEN
  EXISTS_TAC (--`z:hrat`--) THEN RULE_ASSUM_TAC(REWRITE_RULE[hrat_lt]) THEN
  POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM HRAT_ADD_ASSOC, HRAT_LT_ADDL]);

val HRAT_MEAN = store_thm("HRAT_MEAN",
  (--`!x y. x hrat_lt y ==> (?z. x hrat_lt z /\ z hrat_lt y)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC (--`(x hrat_add y) hrat_mul (hrat_inv(hrat_1 hrat_add hrat_1))`--) THEN
  FREEZE_THEN (fn th => ONCE_REWRITE_TAC[th]) ((GENL [(--`x:hrat`--), (--`y:hrat`--)] o SYM o
    SPECL [(--`x:hrat`--), (--`y:hrat`--), (--`hrat_1 hrat_add hrat_1`--)]) HRAT_LT_RMUL) THEN
  REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_RID] THEN
  REWRITE_TAC[HRAT_LDISTRIB, HRAT_MUL_RID] THEN
  ASM_REWRITE_TAC[HRAT_LT_LADD, HRAT_LT_RADD]);

(*---------------------------------------------------------------------------*)
(* Define cuts and the type ":hreal"                                         *)
(*---------------------------------------------------------------------------*)

val _ = Parse.hide "C";   (* in combinTheory *)

val isacut = new_definition("isacut",
--`isacut C =
      (?x. C x)                          /\     (* Nonempty     *)
      (?x. ~C x)                         /\     (* Bounded above   *)
      (!x y. C x /\ y hrat_lt x ==> C y) /\     (* Downward closed *)
      (!x. C x ==> ?y. C y /\ x hrat_lt y)`--);  (* No greatest element*)

val cut_of_hrat = new_definition("cut_of_hrat",
  (--`cut_of_hrat x = \y. y hrat_lt x`--));

val ISACUT_HRAT = store_thm("ISACUT_HRAT",
  (--`!h. isacut(cut_of_hrat h)`--),
  let val th = TAUT_CONV (--`!x y. ~(x /\ y) ==> (x ==> ~y)`--) in
  GEN_TAC THEN REWRITE_TAC[cut_of_hrat, isacut] THEN BETA_TAC THEN
  REPEAT CONJ_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[HRAT_DOWN, HRAT_MEAN, HRAT_LT_TRANS] THEN
  X_CHOOSE_TAC (--`x:hrat`--) (SPEC (--`h:hrat`--) HRAT_UP) THEN
  EXISTS_TAC (--`x:hrat`--) THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC th THEN MATCH_ACCEPT_TAC HRAT_LT_ANTISYM end);

val hreal_tydef = new_type_definition
  ("hreal",
   prove ((--`?C. isacut C`--),
         EXISTS_TAC (--`cut_of_hrat($@(K T))`--) THEN
         MATCH_ACCEPT_TAC ISACUT_HRAT));

val hreal_tybij =
 define_new_type_bijections
   {name="hreal_tybij",ABS="hreal",REP="cut",tyax=hreal_tydef};

val EQUAL_CUTS = store_thm("EQUAL_CUTS",
  (--`!X Y. (cut X = cut Y) ==> (X = Y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM (--`hreal`--)) THEN
  REWRITE_TAC[hreal_tybij]);

(*---------------------------------------------------------------------------*)
(* Required lemmas about cuts                                                *)
(*---------------------------------------------------------------------------*)

val CUT_ISACUT = store_thm("CUT_ISACUT",
  (--`!X. isacut (cut X)`--),
  REWRITE_TAC[hreal_tybij]);

val CUT_PROPERTIES = EQ_MP (SPEC (--`cut X`--) isacut)
                           (SPEC (--`X:hreal`--) CUT_ISACUT);

val CUT_NONEMPTY = store_thm("CUT_NONEMPTY",
  (--`!X. ?x. (cut X) x`--),
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_BOUNDED = store_thm("CUT_BOUNDED",
  (--`!X. ?x. ~((cut X) x)`--),
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_DOWN = store_thm("CUT_DOWN",
  (--`!X x y. cut X x /\ y hrat_lt x ==> cut X y`--),
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_UP = store_thm("CUT_UP",
  (--`!X x. cut X x ==> (?y. cut X y /\ x hrat_lt y)`--),
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_UBOUND = store_thm("CUT_UBOUND",
  (--`!X x y. ~((cut X) x) /\ x hrat_lt y ==> ~((cut X) y)`--),
  let val lemma = TAUT_CONV (--`(~a /\ b ==> ~c) = (c /\ b ==> a)`--) in
  REWRITE_TAC[lemma, CUT_DOWN] end);

val CUT_STRADDLE = store_thm("CUT_STRADDLE",
  (--`!X x y. (cut X) x /\ ~((cut X) y) ==> x hrat_lt y`--),
  let val lemma = TAUT_CONV (--`~(a /\ ~a)`--) in
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [(--`x:hrat`--), (--`y:hrat`--)] HRAT_LT_TOTAL) THEN
  ASM_REWRITE_TAC[lemma] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC CUT_DOWN THEN
  EXISTS_TAC (--`x:hrat`--) THEN ASM_REWRITE_TAC[] end);

val CUT_NEARTOP_ADD = store_thm("CUT_NEARTOP_ADD",
  (--`!X e. ?x. (cut X) x /\ ~((cut X) (x hrat_add e))`--),
  REPEAT GEN_TAC THEN X_CHOOSE_TAC (--`x1:hrat`--)
                                   (SPEC (--`X:hreal`--) CUT_BOUNDED) THEN
  EVERY_TCL (map X_CHOOSE_THEN [(--`n:num`--), (--`d:hrat`--)])
   (MP_TAC o AP_TERM (--`$hrat_mul e`--))
   (SPEC (--`(hrat_inv e) hrat_mul x1`--) HRAT_ARCH) THEN
  REWRITE_TAC[HRAT_LDISTRIB, HRAT_MUL_ASSOC,
              HRAT_MUL_RINV, HRAT_MUL_LID] THEN
  DISCH_THEN(MP_TAC o EXISTS
    ((--`?d. e hrat_mul (hrat_sucint n) = x1 hrat_add d`--),
     (--`e hrat_mul d`--))) THEN
  REWRITE_TAC[GSYM hrat_lt] THEN
  POP_ASSUM(fn th => DISCH_THEN (MP_TAC o MATCH_MP CUT_UBOUND o CONJ th)) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:num`--) MP_TAC o CONV_RULE EXISTS_LEAST_CONV o
    EXISTS((--`?n. ~((cut X) (e hrat_mul (hrat_sucint n)))`--),
           (--`n:num`--))) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (--`n:num`--) SUBST1_TAC)
    (SPEC (--`k:num`--) num_CASES) THEN ASM_REWRITE_TAC[HRAT_SUCINT] THENL
   [REWRITE_TAC[NOT_LESS_0, HRAT_MUL_RINV, HRAT_MUL_RID] THEN
    X_CHOOSE_TAC (--`x:hrat`--) (SPEC (--`X:hreal`--) CUT_NONEMPTY) THEN
    DISCH_THEN(curry op THEN (EXISTS_TAC (--`x:hrat`--)) o MP_TAC) THEN
    POP_ASSUM(SUBST1_TAC o EQT_INTRO) THEN REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o MATCH_MP CUT_UBOUND o
               C CONJ (SPECL [(--`x:hrat`--), (--`e:hrat`--)] HRAT_LT_ADDR)),
    REWRITE_TAC[HRAT_LDISTRIB, HRAT_MUL_RID] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (ASSUME_TAC o REWRITE_RULE[LESS_SUC_REFL] o SPEC (--`n:num`--))) THEN
    EXISTS_TAC (--`e hrat_mul (hrat_sucint n)`--) THEN ASM_REWRITE_TAC[]]);

val CUT_NEARTOP_MUL = store_thm("CUT_NEARTOP_MUL",
  (--`!X u. hrat_1 hrat_lt u ==> ?x. (cut X) x /\ ~((cut X)(u hrat_mul x))`--),
  REPEAT GEN_TAC THEN
  X_CHOOSE_TAC (--`x0:hrat`--)
               (SPEC (--`X:hreal`--) CUT_NONEMPTY) THEN
  ASM_CASES_TAC (--`(cut X)(u hrat_mul x0)`--) THENL
   [REWRITE_TAC[hrat_lt] THEN DISCH_THEN(X_CHOOSE_TAC (--`d:hrat`--)) THEN
    X_CHOOSE_TAC (--`x:hrat`--) (SPECL [(--`X:hreal`--),
                                        (--`d hrat_mul x0`--)] CUT_NEARTOP_ADD)
    THEN EXISTS_TAC (--`x:hrat`--) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HRAT_RDISTRIB, HRAT_MUL_LID]) THEN
    REWRITE_TAC[HRAT_RDISTRIB, HRAT_MUL_LID] THEN
    MATCH_MP_TAC CUT_UBOUND THEN
    EXISTS_TAC (--`x hrat_add (d hrat_mul x0)`--) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC
                o MATCH_MP CUT_STRADDLE
                o CONJ (ASSUME (--`(cut X)(x0 hrat_add (d hrat_mul x0))`--))
                o CONJUNCT2) THEN
    REWRITE_TAC[HRAT_LT_RADD, HRAT_LT_LADD, HRAT_LT_LMUL],
    DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC (--`x0:hrat`--) THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Define the operations. "hreal_lt" and "hreal_sub are convenient later     *)
(*---------------------------------------------------------------------------*)

val hreal_1 = new_definition("hreal_1",
  (--`hreal_1 = hreal (cut_of_hrat hrat_1)`--));

val hreal_add = new_infixl_definition("hreal_add",
  (--`hreal_add X Y = hreal (\w. ?x y. (w = x hrat_add y) /\
                                    (cut X) x /\ (cut Y) y)`--), 500);

val hreal_mul = new_infixl_definition("hreal_mul",
  (--`hreal_mul X Y = hreal (\w. ?x y. (w = x hrat_mul y) /\
                                    (cut X) x /\ (cut Y) y)`--),600);

val hreal_inv = new_definition("hreal_inv",
  (--`hreal_inv X = hreal (\w. ?d. (d hrat_lt hrat_1) /\
                   (!x. (cut X) x ==> ($hrat_mul w x) hrat_lt d))`--));

val hreal_sup = new_definition("hreal_sup",
  (--`hreal_sup P = hreal (\w. ?X. (P X) /\ (cut X) w)`--));

val hreal_lt = new_definition("hreal_lt",
  (--`hreal_lt X Y = ~(X = Y) /\ !x. (cut X) x ==> (cut Y) x`--));
val _ = set_fixity "hreal_lt" (Infix(NONASSOC, 450))


(*---------------------------------------------------------------------------*)
(* Prove the appropriate closure properties of the basic operations          *)
(*---------------------------------------------------------------------------*)

val HREAL_INV_ISACUT = store_thm("HREAL_INV_ISACUT",
  (--`!X. isacut (\w.
      ?d. d hrat_lt hrat_1 /\ (!x. cut X x ==> (w hrat_mul x) hrat_lt d))`--),
  GEN_TAC THEN REWRITE_TAC[isacut] THEN REPEAT CONJ_TAC THEN BETA_TAC THENL
   [X_CHOOSE_TAC (--`d:hrat`--) (SPEC (--`hrat_1`--) HRAT_DOWN) THEN
    X_CHOOSE_TAC (--`z:hrat`--) (SPEC (--`X:hreal`--) CUT_BOUNDED) THEN
    MAP_EVERY EXISTS_TAC [(--`d hrat_mul (hrat_inv z)`--), (--`d:hrat`--)] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP CUT_STRADDLE o
               C CONJ (ASSUME (--`~(cut X z)`--))) THEN
    REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_LT_RMUL1, HRAT_LT_L1],

    X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`X:hreal`--) CUT_NONEMPTY) THEN
    EXISTS_TAC (--`hrat_inv y`--) THEN CONV_TAC NOT_EXISTS_CONV THEN
    GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o SPEC (--`y:hrat`--))) THEN
    ASM_REWRITE_TAC[HRAT_MUL_LINV, HRAT_LT_GT],

    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN (--`d:hrat`--) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC (--`d:hrat`--) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC (--`z:hrat`--) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_TAC THEN MATCH_MP_TAC HRAT_LT_TRANS THEN
    EXISTS_TAC (--`x hrat_mul z`--) THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[HRAT_LT_RMUL],

    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN (--`d:hrat`--) STRIP_ASSUME_TAC) THEN
    X_CHOOSE_THEN (--`e:hrat`--) STRIP_ASSUME_TAC
      (MATCH_MP HRAT_MEAN (ASSUME (--`d hrat_lt hrat_1`--))) THEN
    EXISTS_TAC (--`(e hrat_mul x) hrat_mul (hrat_inv d)`--) THEN CONJ_TAC THENL
     [EXISTS_TAC (--`e:hrat`--) THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC (--`z:hrat`--) THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_LT_RMUL1] THEN
      ONCE_REWRITE_TAC[AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
        (--`a hrat_mul (b hrat_mul c) = b hrat_mul (a hrat_mul c)`--)] THEN
      REWRITE_TAC[HRAT_LT_L1],
      ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
      ASM_REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_GT_LMUL1, HRAT_GT_L1]]]);

val HREAL_ADD_ISACUT = store_thm("HREAL_ADD_ISACUT",
  (--`!X Y. isacut (\w. ?x y. (w = x hrat_add y) /\ cut X x /\ cut Y y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[isacut] THEN REPEAT CONJ_TAC THENL
   [X_CHOOSE_TAC (--`x:hrat`--) (SPEC (--`X:hreal`--) CUT_NONEMPTY) THEN
    X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`Y:hreal`--) CUT_NONEMPTY) THEN
    EXISTS_TAC (--`x hrat_add y`--) THEN BETA_TAC THEN
    MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y:hrat`--)] THEN
    ASM_REWRITE_TAC[],

    X_CHOOSE_TAC (--`x:hrat`--) (SPEC (--`X:hreal`--) CUT_BOUNDED) THEN
    X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`Y:hreal`--) CUT_BOUNDED) THEN
    EXISTS_TAC (--`x hrat_add y`--) THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [(--`u:hrat`--), (--`v:hrat`--)])
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MATCH_MP_TAC HRAT_LT_NE THEN MATCH_MP_TAC HRAT_LT_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CUT_STRADDLE THENL
     [EXISTS_TAC (--`X:hreal`--), EXISTS_TAC (--`Y:hreal`--)] THEN
    ASM_REWRITE_TAC[],

    MAP_EVERY X_GEN_TAC [(--`w:hrat`--), (--`z:hrat`--)] THEN BETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (EVERY_TCL (map X_CHOOSE_THEN
      [(--`u:hrat`--), (--`v:hrat`--)]) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_ASSUM (UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY (fn tm => EXISTS_TAC (--`(z hrat_mul (hrat_inv (u hrat_add v)))
                                       hrat_mul ^tm`--))
              [(--`u:hrat`--), (--`v:hrat`--)]
    THEN REWRITE_TAC[GSYM HRAT_LDISTRIB, GSYM HRAT_MUL_ASSOC,
                     HRAT_MUL_LINV, HRAT_MUL_RID] THEN
    CONJ_TAC THEN MATCH_MP_TAC CUT_DOWN THENL
     [EXISTS_TAC (--`u:hrat`--), EXISTS_TAC (--`v:hrat`--)] THEN
    ASM_REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_LT_LMUL1, HRAT_LT_R1],

    X_GEN_TAC (--`w:hrat`--) THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [(--`x:hrat`--), (--`y:hrat`--)])
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    X_CHOOSE_TAC (--`u:hrat`--) (UNDISCH_ALL (SPECL [(--`X:hreal`--),
                                                     (--`x:hrat`--)] CUT_UP))
    THEN EXISTS_TAC (--`u hrat_add y`--) THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [(--`u:hrat`--), (--`y:hrat`--)], ALL_TAC] THEN
    ASM_REWRITE_TAC[HRAT_LT_RADD]]);

val HREAL_MUL_ISACUT = store_thm("HREAL_MUL_ISACUT",
  (--`!X Y. isacut (\w. ?x y. (w = x hrat_mul y) /\ cut X x /\ cut Y y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[isacut] THEN REPEAT CONJ_TAC THENL
   [X_CHOOSE_TAC (--`x:hrat`--) (SPEC (--`X:hreal`--) CUT_NONEMPTY) THEN
    X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`Y:hreal`--) CUT_NONEMPTY) THEN
    EXISTS_TAC (--`x hrat_mul y`--) THEN BETA_TAC THEN
    MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y:hrat`--)] THEN
    ASM_REWRITE_TAC[],

    X_CHOOSE_TAC (--`x:hrat`--) (SPEC (--`X:hreal`--) CUT_BOUNDED) THEN
    X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`Y:hreal`--) CUT_BOUNDED) THEN
    EXISTS_TAC (--`x hrat_mul y`--) THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [(--`u:hrat`--), (--`v:hrat`--)])
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MATCH_MP_TAC HRAT_LT_NE THEN MATCH_MP_TAC HRAT_LT_MUL2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CUT_STRADDLE THENL
     [EXISTS_TAC (--`X:hreal`--), EXISTS_TAC (--`Y:hreal`--)] THEN
    ASM_REWRITE_TAC[],

    MAP_EVERY X_GEN_TAC [(--`w:hrat`--), (--`z:hrat`--)] THEN BETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (EVERY_TCL (map X_CHOOSE_THEN
      [(--`u:hrat`--), (--`v:hrat`--)]) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_ASSUM (UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC (--`u:hrat`--) THEN
    EXISTS_TAC (--`v hrat_mul (z hrat_mul (hrat_inv (u hrat_mul v)))`--) THEN
    ASM_REWRITE_TAC[HRAT_MUL_ASSOC] THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
    ONCE_REWRITE_TAC[HRAT_MUL_ASSOC] THEN
    REWRITE_TAC[HRAT_MUL_LINV, HRAT_MUL_LID] THEN
    MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`v:hrat`--) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC
     [AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
        (--`(a hrat_mul b) hrat_mul c = (c hrat_mul a) hrat_mul b`--)]
    THEN ASM_REWRITE_TAC[HRAT_LT_LMUL1, HRAT_LT_R1],

    X_GEN_TAC (--`w:hrat`--) THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [(--`x:hrat`--), (--`y:hrat`--)])
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    X_CHOOSE_TAC (--`u:hrat`--)
                 (UNDISCH_ALL (SPECL [(--`X:hreal`--), (--`x:hrat`--)] CUT_UP))
    THEN EXISTS_TAC (--`u hrat_mul y`--) THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [(--`u:hrat`--), (--`y:hrat`--)], ALL_TAC] THEN
    ASM_REWRITE_TAC[HRAT_LT_RMUL]]);

(*---------------------------------------------------------------------------*)
(* Now prove the various theorems about the new type                         *)
(*---------------------------------------------------------------------------*)

val HREAL_ADD_SYM = store_thm("HREAL_ADD_SYM",
  (--`!X Y. X hreal_add Y = Y hreal_add X`--),
  let val vars = [(--`a:hrat`--), (--`b:hrat`--)] in
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_THEN((EVERY_TCL o map X_CHOOSE_THEN) vars ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC (rev vars) THEN ONCE_REWRITE_TAC[HRAT_ADD_SYM]
  THEN ASM_REWRITE_TAC[] end);

val HREAL_MUL_SYM = store_thm("HREAL_MUL_SYM",
  (--`!X Y. X hreal_mul Y = Y hreal_mul X`--),
  let val vars = [(--`a:hrat`--), (--`b:hrat`--)] in
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_mul] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_THEN((EVERY_TCL o map X_CHOOSE_THEN) vars ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC (rev vars) THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM]
  THEN ASM_REWRITE_TAC[] end);

val HREAL_ADD_ASSOC = store_thm("HREAL_ADD_ASSOC",
  (--`!X Y Z. X hreal_add (Y hreal_add Z) = (X hreal_add Y) hreal_add Z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN BETA_TAC THEN
  CONV_TAC(REDEPTH_CONV(LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV))
  THEN EQ_TAC THEN
  DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["u", "v", "x", "y"]) STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXISTS_TAC [(--`u hrat_add x`--), (--`y:hrat`--),
                          (--`u:hrat`--), (--`x:hrat`--)],
    MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y hrat_add v`--),
                          (--`y:hrat`--), (--`v:hrat`--)]]
  THEN ASM_REWRITE_TAC[HRAT_ADD_ASSOC]);

val HREAL_MUL_ASSOC = store_thm("HREAL_MUL_ASSOC",
  (--`!X Y Z. X hreal_mul (Y hreal_mul Z) = (X hreal_mul Y) hreal_mul Z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_mul] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_MUL_ISACUT] THEN BETA_TAC THEN
  CONV_TAC(REDEPTH_CONV(LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV))
  THEN EQ_TAC THEN
  DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["u", "v", "x", "y"]) STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXISTS_TAC [(--`u hrat_mul x`--), (--`y:hrat`--),
                          (--`u:hrat`--), (--`x:hrat`--)],
    MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y hrat_mul v`--),
                          (--`y:hrat`--), (--`v:hrat`--)]]
  THEN ASM_REWRITE_TAC[HRAT_MUL_ASSOC]);

val HREAL_LDISTRIB = store_thm("HREAL_LDISTRIB",
  (--`!X Y Z. X hreal_mul (Y hreal_add Z) =
              (X hreal_mul Y) hreal_add (X hreal_mul Z)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_mul, hreal_add] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
  (REWRITE_TAC o map (REWRITE_RULE[hreal_tybij]))
    [HREAL_MUL_ISACUT, HREAL_ADD_ISACUT] THEN BETA_TAC THEN
  CONV_TAC(REDEPTH_CONV(LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV))
  THEN EQ_TAC THENL
   [DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["a", "b", "c", "d"]) STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [(--`a hrat_mul c`--), (--`a hrat_mul d`--),
        (--`a:hrat`--), (--`c:hrat`--), (--`a:hrat`--), (--`d:hrat`--)] THEN
    ASM_REWRITE_TAC[HRAT_LDISTRIB],
    DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["a", "b", "c", "d", "e", "f"]) STRIP_ASSUME_TAC) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [(--`c:hrat`--), (--`e:hrat`--)] HRAT_LT_TOTAL) THENL
     [MAP_EVERY EXISTS_TAC [(--`e:hrat`--), (--`d hrat_add f`--),
                            (--`d:hrat`--), (--`f:hrat`--)] THEN
      ASM_REWRITE_TAC[HRAT_LDISTRIB],

      MAP_EVERY EXISTS_TAC [(--`e:hrat`--),
        (--`((hrat_inv e) hrat_mul (c hrat_mul d)) hrat_add f`--),
        (--`(hrat_inv e) hrat_mul (c hrat_mul d)`--), (--`f:hrat`--)] THEN
      ASM_REWRITE_TAC
       [HRAT_LDISTRIB, HRAT_MUL_ASSOC, HRAT_MUL_RINV, HRAT_MUL_LID] THEN
      MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`d:hrat`--) THEN
      ASM_REWRITE_TAC[HRAT_LT_LMUL1, HRAT_LT_L1],

      MAP_EVERY EXISTS_TAC [(--`c:hrat`--),
        (--`d hrat_add ((hrat_inv c) hrat_mul (e hrat_mul f))`--),
        (--`d:hrat`--), (--`(hrat_inv c) hrat_mul (e hrat_mul f)`--)] THEN
      ASM_REWRITE_TAC
       [HRAT_LDISTRIB, HRAT_MUL_ASSOC, HRAT_MUL_RINV, HRAT_MUL_LID] THEN
      MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`f:hrat`--) THEN
      ASM_REWRITE_TAC[HRAT_LT_LMUL1, HRAT_LT_L1]]]);

val HREAL_MUL_LID = store_thm("HREAL_MUL_LID",
  (--`!X. hreal_1 hreal_mul X = X`--),
  GEN_TAC THEN REWRITE_TAC[hreal_1, hreal_mul] THEN
  MATCH_MP_TAC EQUAL_CUTS THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_MUL_ISACUT] THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] ISACUT_HRAT] THEN
  REWRITE_TAC[cut_of_hrat] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV (--`w:hrat`--)) THEN GEN_TAC THEN BETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(REPEAT_TCL CHOOSE_THEN
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`y:hrat`--) THEN
    ASM_REWRITE_TAC[HRAT_LT_LMUL1],
    DISCH_THEN(X_CHOOSE_THEN (--`v:hrat`--) STRIP_ASSUME_TAC o MATCH_MP CUT_UP)
    THEN MAP_EVERY EXISTS_TAC [(--`w hrat_mul (hrat_inv v)`--),(--`v:hrat`--)]
    THEN ASM_REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_RID]
    THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN ASM_REWRITE_TAC[HRAT_LT_L1]]);

val HREAL_MUL_LINV = store_thm("HREAL_MUL_LINV",
  (--`!X. (hreal_inv X) hreal_mul X = hreal_1`--),
  GEN_TAC THEN REWRITE_TAC[hreal_inv, hreal_mul, hreal_1] THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_INV_ISACUT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[cut_of_hrat] THEN
  CONV_TAC(X_FUN_EQ_CONV (--`z:hrat`--)) THEN BETA_TAC THEN GEN_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME (--`cut X y`--))) THEN
    MATCH_MP_TAC HRAT_LT_TRANS THEN EXISTS_TAC (--`d:hrat`--) THEN
    ASM_REWRITE_TAC[],

    DISCH_THEN(X_CHOOSE_THEN (--`d:hrat`--) (CONJUNCTS_THEN2 (MP_TAC o
      ONCE_REWRITE_RULE[GSYM HRAT_GT_L1]) ASSUME_TAC) o MATCH_MP HRAT_MEAN)
    THEN DISCH_THEN(X_CHOOSE_TAC (--`x:hrat`--) o
      SPEC (--`X:hreal`--) o MATCH_MP CUT_NEARTOP_MUL) THEN
    MAP_EVERY EXISTS_TAC [(--`z hrat_mul (hrat_inv x)`--), (--`x:hrat`--)] THEN
(* begin change *)
    GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM HRAT_MUL_ASSOC]
    THEN ASM_REWRITE_TAC[HRAT_MUL_LINV, HRAT_MUL_RID] THEN
(* end change *)
(* Rewriting change forces change in proof
 *   ASM_REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_RID] THEN
 *)
    EXISTS_TAC (--`d:hrat`--) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC (--`y:hrat`--) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
    DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C CONJ (CONJUNCT2 th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CUT_STRADDLE) THEN
    SUBST1_TAC(SYM(SPECL [(--`y:hrat`--),
                          (--`((hrat_inv z) hrat_mul d) hrat_mul x`--),
                          (--`z hrat_mul (hrat_inv x)`--)] HRAT_LT_LMUL)) THEN
    ONCE_REWRITE_TAC[AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
                     (--`(a hrat_mul b) hrat_mul ((c hrat_mul d) hrat_mul e) =
                      ((c hrat_mul a) hrat_mul (b hrat_mul e)) hrat_mul d`--)]
    THEN REWRITE_TAC[HRAT_MUL_LINV, HRAT_MUL_LID]]);

val HREAL_NOZERO = store_thm("HREAL_NOZERO",
  (--`!X Y. ~(X hreal_add Y = X)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add] THEN
  DISCH_THEN(MP_TAC o AP_TERM (--`cut`--)) THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN
  DISCH_THEN(MP_TAC o CONV_RULE (X_FUN_EQ_CONV (--`w:hrat`--))) THEN
  REWRITE_TAC[] THEN CONV_TAC NOT_FORALL_CONV THEN BETA_TAC THEN
  X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`Y:hreal`--) CUT_NONEMPTY) THEN
  X_CHOOSE_TAC (--`x:hrat`--)
               (SPECL [(--`X:hreal`--), (--`y:hrat`--)] CUT_NEARTOP_ADD) THEN
  EXISTS_TAC (--`x hrat_add y`--) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y:hrat`--)] THEN
  ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Need a sequence of lemmas for totality of addition; it's convenient       *)
(* to define a "subtraction" function and prove its closure                  *)
(*---------------------------------------------------------------------------*)

val hreal_sub = new_infixl_definition("hreal_sub",
--`hreal_sub Y X = hreal (\w. ?x. ~((cut X) x) /\ (cut Y) ($hrat_add x w))`--,
  500);

val HREAL_LT_LEMMA = store_thm("HREAL_LT_LEMMA",
  (--`!X Y. X hreal_lt Y ==> ?x. ~(cut X x) /\ (cut Y x)`--),
  let val lemma1 = TAUT_CONV (--`~(~a /\ b) = b ==> a`--)
      val lemma2 = TAUT_CONV (--`(a ==> b) /\ (b ==> a) = (a = b)`--)
  in
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(LAND_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[hreal_lt, lemma1] THEN
  DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C CONJ th)) THEN
  CONV_TAC(LAND_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[lemma2] THEN CONV_TAC(LAND_CONV EXT_CONV) THEN
  DISCH_THEN(MP_TAC o AP_TERM (--`hreal`--)) THEN REWRITE_TAC[hreal_tybij]
  end);

val HREAL_SUB_ISACUT = store_thm("HREAL_SUB_ISACUT",
--`!X Y. X hreal_lt Y ==> isacut(\w. ?x. ~cut X x /\ cut Y(x hrat_add w))`--,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[isacut] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC (--`y:hrat`--) o MATCH_MP HREAL_LT_LEMMA) THEN
    FIRST_ASSUM(X_CHOOSE_THEN (--`z:hrat`--) MP_TAC
                o MATCH_MP (SPECL [(--`Y:hreal`--), (--`y:hrat`--)] CUT_UP)
                o CONJUNCT2) THEN
    REWRITE_TAC[hrat_lt] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (--`x:hrat`--) SUBST_ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y:hrat`--)] THEN
    ASM_REWRITE_TAC[],

    X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`Y:hreal`--) CUT_BOUNDED) THEN
    EXISTS_TAC (--`y:hrat`--) THEN CONV_TAC NOT_EXISTS_CONV THEN
    X_GEN_TAC (--`d:hrat`--) THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISJ2_TAC THEN MATCH_MP_TAC CUT_UBOUND THEN EXISTS_TAC (--`y:hrat`--) THEN
    ASM_REWRITE_TAC[HRAT_LT_ADDR],

    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN (--`z:hrat`--) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC (--`z:hrat`--) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`z hrat_add x`--) THEN
    ASM_REWRITE_TAC[HRAT_LT_LADD],

    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN (--`z:hrat`--) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN (--`w:hrat`--) MP_TAC o MATCH_MP
     (SPECL [(--`Y:hreal`--), (--`z hrat_add x`--)] CUT_UP)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (--`d:hrat`--) SUBST_ALL_TAC) o REWRITE_RULE[hrat_lt]) THEN
    EXISTS_TAC (--`x hrat_add d`--) THEN REWRITE_TAC[HRAT_LT_ADDL] THEN
    EXISTS_TAC (--`z:hrat`--) THEN ASM_REWRITE_TAC[HRAT_ADD_ASSOC]]);

val HREAL_SUB_ADD = store_thm("HREAL_SUB_ADD",
  (--`!X Y. X hreal_lt Y ==> ((Y hreal_sub X) hreal_add X = Y)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add, hreal_sub] THEN
  DISCH_TAC THEN MATCH_MP_TAC EQUAL_CUTS THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[hreal_tybij]
                   (MATCH_MP HREAL_SUB_ISACUT th)]) THEN
  CONV_TAC (X_FUN_EQ_CONV (--`w:hrat`--)) THEN BETA_TAC THEN GEN_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(REPEAT_TCL CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (--`z:hrat`--) STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CUT_DOWN THEN
    EXISTS_TAC (--`z hrat_add x`--) THEN ASM_REWRITE_TAC[] THEN
    GEN_REWR_TAC RAND_CONV [HRAT_ADD_SYM] THEN
    REWRITE_TAC[HRAT_LT_LADD] THEN MATCH_MP_TAC CUT_STRADDLE THEN
    EXISTS_TAC (--`X:hreal`--) THEN ASM_REWRITE_TAC[],

    DISCH_TAC THEN ASM_CASES_TAC (--`(cut X) w`--) THENL
     [FIRST_ASSUM (X_CHOOSE_THEN (--`z:hrat`--) MP_TAC o MATCH_MP
       (SPECL [(--`X:hreal`--), (--`Y:hreal`--)] HREAL_LT_LEMMA)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN (--`k:hrat`--) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o
        MATCH_MP CUT_UP)) THEN REWRITE_TAC[hrat_lt] THEN
      DISCH_THEN(X_CHOOSE_THEN (--`e:hrat`--) SUBST_ALL_TAC) THEN
      X_CHOOSE_THEN (--`x:hrat`--)
                    MP_TAC (SPECL[--`e:hrat`--, --`w:hrat`--] HRAT_DOWN2) THEN
      SUBST1_TAC(SYM(SPECL [(--`x:hrat`--), (--`e:hrat`--),
                            (--`z:hrat`--)] HRAT_LT_LADD)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP CUT_DOWN o
       CONJ (ASSUME (--`cut Y(z hrat_add e)`--))) MP_TAC) THEN
      REWRITE_TAC[hrat_lt] THEN DISCH_THEN(X_CHOOSE_TAC (--`y:hrat`--)) THEN
      MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y:hrat`--)] THEN ASM_REWRITE_TAC[]
      THEN CONJ_TAC THENL
       [EXISTS_TAC (--`z:hrat`--) THEN ASM_REWRITE_TAC[],
        MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`w:hrat`--) THEN
        ASM_REWRITE_TAC[HRAT_LT_ADDR]],

      FIRST_ASSUM(X_CHOOSE_THEN (--`k:hrat`--) MP_TAC o MATCH_MP CUT_UP) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[hrat_lt]
      THEN DISCH_THEN(X_CHOOSE_THEN (--`e:hrat`--) SUBST_ALL_TAC) THEN
      X_CHOOSE_THEN (--`y:hrat`--) STRIP_ASSUME_TAC
       (SPECL [(--`X:hreal`--), (--`e:hrat`--)] CUT_NEARTOP_ADD) THEN
      ASM_CASES_TAC (--`(cut Y) (y hrat_add e)`--) THENL
       [SUBGOAL_THEN (--`y hrat_lt w`--) MP_TAC THENL
         [MATCH_MP_TAC CUT_STRADDLE THEN EXISTS_TAC (--`X:hreal`--) THEN
          ASM_REWRITE_TAC[], ALL_TAC] THEN REWRITE_TAC[hrat_lt] THEN
        DISCH_THEN(X_CHOOSE_THEN (--`x:hrat`--) SUBST_ALL_TAC) THEN
        MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`y:hrat`--)] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_ACCEPT_TAC HRAT_ADD_SYM,
          EXISTS_TAC (--`y hrat_add e`--) THEN
          ONCE_REWRITE_TAC[AC(HRAT_ADD_ASSOC,HRAT_ADD_SYM)
            (--`(a hrat_add b) hrat_add c = (a hrat_add c) hrat_add b`--)] THEN
          ASM_REWRITE_TAC[],
          FIRST_ASSUM ACCEPT_TAC],

        UNDISCH_TAC (--`cut X y`--) THEN CONV_TAC CONTRAPOS_CONV THEN
        DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC CUT_UBOUND THEN
        EXISTS_TAC (--`w:hrat`--) THEN ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(SPECL [(--`w:hrat`--), (--`y:hrat`--), (--`e:hrat`--)] HRAT_LT_RADD)) THEN
        MATCH_MP_TAC CUT_STRADDLE THEN EXISTS_TAC (--`Y:hreal`--) THEN
        ASM_REWRITE_TAC[]]]]);

val HREAL_LT_TOTAL = store_thm("HREAL_LT_TOTAL",
  (--`!X Y. (X = Y) \/ (X hreal_lt Y) \/ (Y hreal_lt X)`--),
  let val lemma = TAUT_CONV (--`a \/ (~a /\ b) \/ (~a /\ c) = ~b /\ ~c ==> a`--)
      val negneg = TAUT_CONV (--`a = ~(~a)`--) in
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_lt] THEN
  SUBST1_TAC(ISPECL[(--`Y:hreal`--), (--`X:hreal`--)] EQ_SYM_EQ) THEN
  REWRITE_TAC[lemma] THEN CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN(MP_TAC o MATCH_MP(CONTRAPOS(SPEC_ALL EQUAL_CUTS))) THEN
  CONV_TAC(ONCE_DEPTH_CONV(X_FUN_EQ_CONV (--`x:hrat`--))) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`z:hrat`--) MP_TAC o CONV_RULE NOT_FORALL_CONV) THEN
  ASM_CASES_TAC (--`cut X z`--) THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN DISCH_TAC
  THENL [DISJ2_TAC, DISJ1_TAC] THEN
  GEN_REWR_TAC I [negneg] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`w:hrat`--) MP_TAC o CONV_RULE NOT_FORALL_CONV) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fn th =>
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CUT_STRADDLE o CONJ th)) THEN
  MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`z:hrat`--) THEN ASM_REWRITE_TAC[] end);

val HREAL_LT = store_thm("HREAL_LT",
  (--`!X Y. X hreal_lt Y = ?D. Y = X hreal_add D`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(curry op THEN (EXISTS_TAC (--`Y hreal_sub X`--)) o MP_TAC) THEN
    DISCH_THEN(CONV_TAC o (LAND_CONV o REWR_CONV) o
      SYM o MATCH_MP HREAL_SUB_ADD) THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM,
    DISCH_THEN(X_CHOOSE_THEN (--`D:hreal`--) SUBST_ALL_TAC) THEN
    REWRITE_TAC[hreal_lt, NOT_EQ_SYM(SPEC_ALL HREAL_NOZERO)] THEN
    X_GEN_TAC (--`x:hrat`--) THEN DISCH_TAC THEN
    X_CHOOSE_TAC (--`e:hrat`--) (SPEC (--`D:hreal`--) CUT_NONEMPTY) THEN
    X_CHOOSE_THEN (--`d:hrat`--) MP_TAC (SPECL [(--`x:hrat`--), (--`e:hrat`--)] HRAT_DOWN2) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC (--`w:hrat`--) o REWRITE_RULE[hrat_lt])
      (ASSUME_TAC o MATCH_MP CUT_DOWN o CONJ (ASSUME (--`cut D e`--)))) THEN
    REWRITE_TAC[hreal_add, REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN
    BETA_TAC THEN MAP_EVERY EXISTS_TAC [(--`w:hrat`--), (--`d:hrat`--)] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC HRAT_ADD_SYM,
      MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC (--`x:hrat`--) THEN
      ASM_REWRITE_TAC[HRAT_LT_ADDR]]]);

val HREAL_ADD_TOTAL = store_thm("HREAL_ADD_TOTAL",
  (--`!X Y. (X = Y) \/ (?D. Y = X hreal_add D) \/ (?D. X = Y hreal_add D)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[SYM(SPEC_ALL HREAL_LT)] THEN
  MATCH_ACCEPT_TAC HREAL_LT_TOTAL);

(*---------------------------------------------------------------------------*)
(* Now prove the supremum property                                           *)
(*---------------------------------------------------------------------------*)

val HREAL_SUP_ISACUT = store_thm("HREAL_SUP_ISACUT",
  (--`!P. (?X:hreal. P X) /\ (?Y. (!X. P X ==> X hreal_lt Y))
        ==> isacut (\w. ?X. P X /\ cut X w)`--),
  let val lemma = TAUT_CONV (--`~(a /\ b) = (a ==> ~b)`--) in
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN CHOOSE_TAC) THEN
  REWRITE_TAC[isacut] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [X_CHOOSE_TAC (--`x:hrat`--) (SPEC (--`X:hreal`--) CUT_NONEMPTY) THEN
    MAP_EVERY EXISTS_TAC [(--`x:hrat`--), (--`X:hreal`--)] THEN ASM_REWRITE_TAC[],

    X_CHOOSE_TAC (--`y:hrat`--) (SPEC (--`Y:hreal`--) CUT_BOUNDED) THEN
    EXISTS_TAC (--`y:hrat`--) THEN CONV_TAC NOT_EXISTS_CONV THEN
    X_GEN_TAC (--`Z:hreal`--) THEN REWRITE_TAC[lemma] THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[hreal_lt] THEN
    DISCH_THEN(MP_TAC o SPEC (--`y:hrat`--) o CONJUNCT2) THEN ASM_REWRITE_TAC[],

    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC (--`Z:hreal`--)) ASSUME_TAC) THEN
    EXISTS_TAC (--`Z:hreal`--) THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CUT_DOWN THEN
    EXISTS_TAC (--`x:hrat`--) THEN ASM_REWRITE_TAC[],

    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN (--`Z:hreal`--) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_TAC (--`y:hrat`--) o MATCH_MP
      (SPECL [(--`Z:hreal`--), (--`x:hrat`--)] CUT_UP)) THEN
    EXISTS_TAC (--`y:hrat`--) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC (--`Z:hreal`--) THEN ASM_REWRITE_TAC[]] end);

val HREAL_SUP = store_thm("HREAL_SUP",
  (--`!P. (?X. P X) /\ (?Y. (!X. P X ==> X hreal_lt Y)) ==>
         (!Y. (?X. P X /\ Y hreal_lt X) = Y hreal_lt (hreal_sup P))`--),
  let val stac = FIRST_ASSUM(SUBST1_TAC o MATCH_MP
    (REWRITE_RULE[hreal_tybij] HREAL_SUP_ISACUT)) in
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[hreal_sup, hreal_lt] THEN stac THEN
    REWRITE_TAC[GSYM hreal_lt] THEN BETA_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN (--`X:hreal`--) STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [DISCH_THEN(MP_TAC o AP_TERM (--`cut`--)) THEN stac THEN
        DISCH_THEN(MP_TAC o CONV_RULE (X_FUN_EQ_CONV (--`x:hrat`--))) THEN
        BETA_TAC THEN REWRITE_TAC[] THEN CONV_TAC NOT_FORALL_CONV THEN
        FIRST_ASSUM(X_CHOOSE_TAC (--`x:hrat`--) o MATCH_MP HREAL_LT_LEMMA) THEN
        EXISTS_TAC (--`x:hrat`--) THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC (--`X:hreal`--) THEN ASM_REWRITE_TAC[],
        X_GEN_TAC (--`x:hrat`--) THEN DISCH_THEN(ASSUME_TAC o MATCH_MP
         (CONJUNCT2(REWRITE_RULE[hreal_lt] (ASSUME (--`Y hreal_lt X`--))))) THEN
        EXISTS_TAC (--`X:hreal`--) THEN ASM_REWRITE_TAC[]]],
    DISCH_THEN(X_CHOOSE_THEN (--`x:hrat`--) MP_TAC o MATCH_MP HREAL_LT_LEMMA) THEN
    REWRITE_TAC[hreal_sup] THEN stac THEN BETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (--`X:hreal`--))) THEN
    EXISTS_TAC (--`X:hreal`--) THEN ASM_REWRITE_TAC[] THEN
    REPEAT_TCL DISJ_CASES_THEN (fn th => SUBST_ALL_TAC th ORELSE ASSUME_TAC th)
     (SPECL [(--`X:hreal`--), (--`Y:hreal`--)] HREAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(SUBST_ALL_TAC o EQT_INTRO o CONJUNCT2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC,
      MP_TAC (CONJUNCT2 (REWRITE_RULE[hreal_lt] (ASSUME (--`X hreal_lt Y`--)))) THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC (--`x:hrat`--) THEN
      ASM_REWRITE_TAC[]]] end);

val _ = export_theory();

end
