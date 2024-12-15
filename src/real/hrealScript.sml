(*---------------------------------------------------------------------------*)
(* Construct positive reals from positive rationals                          *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib
     hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory
     prim_recTheory jrhUtils hratTheory;

infix THEN THENL ORELSE ORELSEC;

val _ = new_theory "hreal";
val _ = ParseExtras.temp_loose_equality()

val GEN_ALL   = hol88Lib.GEN_ALL;   (* it has old reverted variable order *)

(*---------------------------------------------------------------------------*)
(* Lemmas about the half-rationals, including definition of ordering         *)
(*---------------------------------------------------------------------------*)

val hrat_lt = new_definition("hrat_lt",
  “$hrat_lt x y = ?d. y = x hrat_add d”);
val _ = temp_set_fixity "hrat_lt" (Infix(NONASSOC, 450))

val HRAT_LT_REFL = store_thm("HRAT_LT_REFL",
  “!x. ~(x hrat_lt x)”,
  GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[HRAT_NOZERO]);

val HRAT_LT_TRANS = store_thm("HRAT_LT_TRANS",
  “!x y z. x hrat_lt y /\ y hrat_lt z ==> x hrat_lt z”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 CHOOSE_TAC (CHOOSE_THEN SUBST1_TAC)) THEN
  POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[GSYM HRAT_ADD_ASSOC] THEN
  W(EXISTS_TAC o rand o lhs o body o rand o snd) THEN REFL_TAC);

val HRAT_LT_ANTISYM = store_thm("HRAT_LT_ANTISYM",
  “!x y. ~(x hrat_lt y /\ y hrat_lt x)”,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HRAT_LT_TRANS) THEN
  REWRITE_TAC[HRAT_LT_REFL]);

val HRAT_LT_TOTAL = store_thm("HRAT_LT_TOTAL",
  “!x y. (x = y) \/ x hrat_lt y \/ y hrat_lt x”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  REPEAT_TCL DISJ_CASES_THEN (SUBST1_TAC o EQT_INTRO)
   (SPECL [“x:hrat”, “y:hrat”] HRAT_ADD_TOTAL) THEN
  REWRITE_TAC[]);

val HRAT_MUL_RID = store_thm("HRAT_MUL_RID",
  “!x. x hrat_mul hrat_1 = x”,
  GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_MUL_LID);

val HRAT_MUL_RINV = store_thm("HRAT_MUL_RINV",
  “!x. x hrat_mul (hrat_inv x) = hrat_1”,
  GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_MUL_LINV);

val HRAT_RDISTRIB = store_thm("HRAT_RDISTRIB",
  “!x y z. (x hrat_add y) hrat_mul z =
     (x hrat_mul z) hrat_add (y hrat_mul z)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LDISTRIB);

val HRAT_LT_ADDL = store_thm("HRAT_LT_ADDL",
  “!x y. x hrat_lt (x hrat_add y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  EXISTS_TAC “y:hrat” THEN REFL_TAC);

val HRAT_LT_ADDR = store_thm("HRAT_LT_ADDR",
  “!x y. y hrat_lt (x hrat_add y)”,
  ONCE_REWRITE_TAC[HRAT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_ADDL);

val HRAT_LT_GT = store_thm("HRAT_LT_GT",
  “!x y. x hrat_lt y ==> ~(y hrat_lt x)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM HRAT_ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[HRAT_NOZERO]);

val HRAT_LT_NE = store_thm("HRAT_LT_NE",
  “!x y. x hrat_lt y ==> ~(x = y)”,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC HRAT_LT_REFL);

val HRAT_EQ_LADD = store_thm("HRAT_EQ_LADD",
  “!x y z. (x hrat_add y = x hrat_add z) = (y = z)”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
      (SPECL [“y:hrat”, “z:hrat”] HRAT_ADD_TOTAL) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[HRAT_ADD_ASSOC, HRAT_NOZERO, GSYM HRAT_NOZERO],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val HRAT_EQ_LMUL = store_thm("HRAT_EQ_LMUL",
  “!x y z. (x hrat_mul y = x hrat_mul z) = (y = z)”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM “$hrat_mul (hrat_inv x)”) THEN
    REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_LID],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val HRAT_LT_ADD2 = store_thm("HRAT_LT_ADD2",
  “!u v x y. u hrat_lt x /\ v hrat_lt y ==>
     (u hrat_add v) hrat_lt (x hrat_add y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN “d1:hrat” SUBST1_TAC)
    (X_CHOOSE_THEN “d2:hrat” SUBST1_TAC)) THEN
  EXISTS_TAC “d1 hrat_add d2” THEN
  CONV_TAC(AC_CONV(HRAT_ADD_ASSOC,HRAT_ADD_SYM)));

val HRAT_LT_LADD = store_thm("HRAT_LT_LADD",
  “!x y z. (z hrat_add x) hrat_lt (z hrat_add y) = x hrat_lt y”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN “d:hrat” (curry op THEN (EXISTS_TAC “d:hrat”) o MP_TAC))
  THEN REWRITE_TAC[GSYM HRAT_ADD_ASSOC, HRAT_EQ_LADD]);

val HRAT_LT_RADD = store_thm("HRAT_LT_RADD",
  “!x y z. (x hrat_add z) hrat_lt (y hrat_add z) = x hrat_lt y”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_ADD_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_LADD);

val HRAT_LT_MUL2 = store_thm("HRAT_LT_MUL2",
  “!u v x y. u hrat_lt x /\ v hrat_lt y ==>
     (u hrat_mul v) hrat_lt (x hrat_mul y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN “d1:hrat” SUBST1_TAC)
    (X_CHOOSE_THEN “d2:hrat” SUBST1_TAC)) THEN
  REWRITE_TAC[HRAT_LDISTRIB, HRAT_RDISTRIB, GSYM HRAT_ADD_ASSOC] THEN
  REWRITE_TAC[HRAT_EQ_LADD] THEN
  W(EXISTS_TAC o lhs o body o rand o snd) THEN REFL_TAC);

val HRAT_LT_LMUL = store_thm("HRAT_LT_LMUL",
  “!x y z. (z hrat_mul x) hrat_lt (z hrat_mul y) = x hrat_lt y”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hrat_lt] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC “d:hrat”) THENL
   [EXISTS_TAC “(hrat_inv z) hrat_mul d”,
    EXISTS_TAC “z hrat_mul d”] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM HRAT_LDISTRIB, GSYM HRAT_MUL_ASSOC, HRAT_EQ_LMUL] THEN
  DISCH_THEN(MP_TAC o AP_TERM “$hrat_mul (hrat_inv z)”) THEN
  REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_LID, HRAT_LDISTRIB]);

val HRAT_LT_RMUL = store_thm("HRAT_LT_RMUL",
  “!x y z. (x hrat_mul z) hrat_lt (y hrat_mul z) = x hrat_lt y”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL);

val HRAT_LT_LMUL1 = store_thm("HRAT_LT_LMUL1",
  “!x y. (x hrat_mul y) hrat_lt y = x hrat_lt hrat_1”,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM HRAT_MUL_LID] THEN
  MATCH_ACCEPT_TAC HRAT_LT_RMUL);

val HRAT_LT_RMUL1 = store_thm("HRAT_LT_RMUL1",
  “!x y. (x hrat_mul y) hrat_lt x = y hrat_lt hrat_1”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL1);

val HRAT_GT_LMUL1 = store_thm("HRAT_GT_LMUL1",
  “!x y. y hrat_lt (x hrat_mul y) = hrat_1 hrat_lt x”,
  REPEAT GEN_TAC THEN
  GEN_REWR_TAC (funpow 2 LAND_CONV) [GSYM HRAT_MUL_LID]
  THEN MATCH_ACCEPT_TAC HRAT_LT_RMUL);

val HRAT_LT_L1 = store_thm("HRAT_LT_L1",
  “!x y. ((hrat_inv x) hrat_mul y) hrat_lt hrat_1 = y hrat_lt x”,
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(SPEC “x:hrat” HRAT_MUL_LINV)) THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL);

val HRAT_LT_R1 = store_thm("HRAT_LT_R1",
  “!x y. (x hrat_mul (hrat_inv y)) hrat_lt hrat_1 = x hrat_lt y”,
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(SPEC “y:hrat” HRAT_MUL_RINV)) THEN
  MATCH_ACCEPT_TAC HRAT_LT_RMUL);

val HRAT_GT_L1 = store_thm("HRAT_GT_L1",
  “!x y. hrat_1 hrat_lt ((hrat_inv x) hrat_mul y) = x hrat_lt y”,
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(SPEC “x:hrat” HRAT_MUL_LINV)) THEN
  MATCH_ACCEPT_TAC HRAT_LT_LMUL);

val HRAT_INV_MUL = store_thm("HRAT_INV_MUL",
  “!x y. hrat_inv (x hrat_mul y) = (hrat_inv x) hrat_mul (hrat_inv y)”,
  REPEAT GEN_TAC THEN SUBST1_TAC
    (SYM(SPECL [“x hrat_mul y”, “hrat_inv (x hrat_mul y)”,
                “(hrat_inv x) hrat_mul (hrat_inv y)”] HRAT_EQ_LMUL)) THEN
  ONCE_REWRITE_TAC[AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
    “(a hrat_mul b) hrat_mul (c hrat_mul d) =
     (a hrat_mul c) hrat_mul (b hrat_mul d)”] THEN
  REWRITE_TAC[HRAT_MUL_RINV, HRAT_MUL_LID]);

val HRAT_UP = store_thm("HRAT_UP",
  “!x. ?y. x hrat_lt y”,
  GEN_TAC THEN EXISTS_TAC “x hrat_add x” THEN
  REWRITE_TAC[hrat_lt] THEN EXISTS_TAC “x:hrat” THEN REFL_TAC);

val HRAT_DOWN = store_thm("HRAT_DOWN",
  “!x. ?y. y hrat_lt x”,
  GEN_TAC THEN
  EXISTS_TAC “x hrat_mul (hrat_inv (hrat_1 hrat_add hrat_1))” THEN
  REWRITE_TAC[HRAT_LT_RMUL1] THEN
  GEN_REWR_TAC LAND_CONV [GSYM HRAT_MUL_LID] THEN
  REWRITE_TAC[HRAT_LT_R1] THEN REWRITE_TAC[hrat_lt] THEN
  EXISTS_TAC “hrat_1” THEN REFL_TAC);

val HRAT_DOWN2 = store_thm("HRAT_DOWN2",
  “!x y. ?z. z hrat_lt x /\ z hrat_lt y”,
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [“x:hrat”, “y:hrat”] HRAT_ADD_TOTAL) THEN
  ASM_REWRITE_TAC[HRAT_DOWN] THEN
  POP_ASSUM(X_CHOOSE_THEN “d:hrat” SUBST1_TAC) THENL
   [X_CHOOSE_TAC “z:hrat” (SPEC “y:hrat” HRAT_DOWN),
    X_CHOOSE_TAC “z:hrat” (SPEC “x:hrat” HRAT_DOWN)] THEN
  EXISTS_TAC “z:hrat” THEN RULE_ASSUM_TAC(REWRITE_RULE[hrat_lt]) THEN
  POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM HRAT_ADD_ASSOC, HRAT_LT_ADDL]);

val HRAT_MEAN = store_thm("HRAT_MEAN",
  “!x y. x hrat_lt y ==> (?z. x hrat_lt z /\ z hrat_lt y)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC “(x hrat_add y) hrat_mul (hrat_inv(hrat_1 hrat_add hrat_1))” THEN
  FREEZE_THEN (fn th => ONCE_REWRITE_TAC[th]) ((GENL [“x:hrat”, “y:hrat”] o SYM o
    SPECL [“x:hrat”, “y:hrat”, “hrat_1 hrat_add hrat_1”]) HRAT_LT_RMUL) THEN
  REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_RID] THEN
  REWRITE_TAC[HRAT_LDISTRIB, HRAT_MUL_RID] THEN
  ASM_REWRITE_TAC[HRAT_LT_LADD, HRAT_LT_RADD]);

(*---------------------------------------------------------------------------*)
(* Define cuts and the type ":hreal"                                         *)
(*---------------------------------------------------------------------------*)

val _ = Parse.hide "C";   (* in combinTheory *)

val isacut = new_definition("isacut",
“isacut C =
      (?x. C x)                          /\     (* Nonempty     *)
      (?x. ~C x)                         /\     (* Bounded above   *)
      (!x y. C x /\ y hrat_lt x ==> C y) /\     (* Downward closed *)
      (!x. C x ==> ?y. C y /\ x hrat_lt y)”);  (* No greatest element*)

val cut_of_hrat = new_definition("cut_of_hrat",
  “cut_of_hrat x = \y. y hrat_lt x”);

val ISACUT_HRAT = store_thm("ISACUT_HRAT",
  “!h. isacut(cut_of_hrat h)”,
  let val th = TAUT_CONV “!x y. ~(x /\ y) ==> (x ==> ~y)” in
  GEN_TAC THEN REWRITE_TAC[cut_of_hrat, isacut] THEN BETA_TAC THEN
  REPEAT CONJ_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[HRAT_DOWN, HRAT_MEAN, HRAT_LT_TRANS] THEN
  X_CHOOSE_TAC “x:hrat” (SPEC “h:hrat” HRAT_UP) THEN
  EXISTS_TAC “x:hrat” THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC th THEN MATCH_ACCEPT_TAC HRAT_LT_ANTISYM end);

val hreal_tydef = new_type_definition
  ("hreal",
   prove (“?C. isacut C”,
         EXISTS_TAC “cut_of_hrat($@(K T))” THEN
         MATCH_ACCEPT_TAC ISACUT_HRAT));

val hreal_tybij =
 define_new_type_bijections
   {name="hreal_tybij",ABS="hreal",REP="cut",tyax=hreal_tydef};

val EQUAL_CUTS = store_thm("EQUAL_CUTS",
  “!X Y. (cut X = cut Y) ==> (X = Y)”,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM “hreal”) THEN
  REWRITE_TAC[hreal_tybij]);

(*---------------------------------------------------------------------------*)
(* Required lemmas about cuts                                                *)
(*---------------------------------------------------------------------------*)

val CUT_ISACUT = store_thm("CUT_ISACUT",
  “!X. isacut (cut X)”,
  REWRITE_TAC[hreal_tybij]);

val CUT_PROPERTIES = EQ_MP (SPEC “cut X” isacut)
                           (SPEC “X:hreal” CUT_ISACUT);

val CUT_NONEMPTY = store_thm("CUT_NONEMPTY",
  “!X. ?x. (cut X) x”,
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_BOUNDED = store_thm("CUT_BOUNDED",
  “!X. ?x. ~((cut X) x)”,
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_DOWN = store_thm("CUT_DOWN",
  “!X x y. cut X x /\ y hrat_lt x ==> cut X y”,
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_UP = store_thm("CUT_UP",
  “!X x. cut X x ==> (?y. cut X y /\ x hrat_lt y)”,
  REWRITE_TAC[CUT_PROPERTIES]);

val CUT_UBOUND = store_thm("CUT_UBOUND",
  “!X x y. ~((cut X) x) /\ x hrat_lt y ==> ~((cut X) y)”,
  let val lemma = TAUT_CONV “(~a /\ b ==> ~c) = (c /\ b ==> a)” in
  REWRITE_TAC[lemma, CUT_DOWN] end);

val CUT_STRADDLE = store_thm("CUT_STRADDLE",
  “!X x y. (cut X) x /\ ~((cut X) y) ==> x hrat_lt y”,
  let val lemma = TAUT_CONV “~(a /\ ~a)” in
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [“x:hrat”, “y:hrat”] HRAT_LT_TOTAL) THEN
  ASM_REWRITE_TAC[lemma] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC CUT_DOWN THEN
  EXISTS_TAC “x:hrat” THEN ASM_REWRITE_TAC[] end);

val CUT_NEARTOP_ADD = store_thm("CUT_NEARTOP_ADD",
  “!X e. ?x. (cut X) x /\ ~((cut X) (x hrat_add e))”,
  REPEAT GEN_TAC THEN X_CHOOSE_TAC “x1:hrat”
                                   (SPEC “X:hreal” CUT_BOUNDED) THEN
  EVERY_TCL (map X_CHOOSE_THEN [“n:num”, “d:hrat”])
   (MP_TAC o AP_TERM “$hrat_mul e”)
   (SPEC “(hrat_inv e) hrat_mul x1” HRAT_ARCH) THEN
  REWRITE_TAC[HRAT_LDISTRIB, HRAT_MUL_ASSOC,
              HRAT_MUL_RINV, HRAT_MUL_LID] THEN
  DISCH_THEN(MP_TAC o EXISTS
    (“?d. e hrat_mul (hrat_sucint n) = x1 hrat_add d”,
     “e hrat_mul d”)) THEN
  REWRITE_TAC[GSYM hrat_lt] THEN
  POP_ASSUM(fn th => DISCH_THEN (MP_TAC o MATCH_MP CUT_UBOUND o CONJ th)) THEN
  DISCH_THEN(X_CHOOSE_THEN “k:num” MP_TAC o CONV_RULE EXISTS_LEAST_CONV o
    EXISTS(“?n. ~((cut X) (e hrat_mul (hrat_sucint n)))”,
           “n:num”)) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN “n:num” SUBST1_TAC)
    (SPEC “k:num” num_CASES) THEN ASM_REWRITE_TAC[HRAT_SUCINT] THENL
   [REWRITE_TAC[NOT_LESS_0, HRAT_MUL_RINV, HRAT_MUL_RID] THEN
    X_CHOOSE_TAC “x:hrat” (SPEC “X:hreal” CUT_NONEMPTY) THEN
    DISCH_THEN(curry op THEN (EXISTS_TAC “x:hrat”) o MP_TAC) THEN
    POP_ASSUM(SUBST1_TAC o EQT_INTRO) THEN REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o MATCH_MP CUT_UBOUND o
               C CONJ (SPECL [“x:hrat”, “e:hrat”] HRAT_LT_ADDR)),
    REWRITE_TAC[HRAT_LDISTRIB, HRAT_MUL_RID] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (ASSUME_TAC o REWRITE_RULE[LESS_SUC_REFL] o SPEC “n:num”)) THEN
    EXISTS_TAC “e hrat_mul (hrat_sucint n)” THEN ASM_REWRITE_TAC[]]);

val CUT_NEARTOP_MUL = store_thm("CUT_NEARTOP_MUL",
  “!X u. hrat_1 hrat_lt u ==> ?x. (cut X) x /\ ~((cut X)(u hrat_mul x))”,
  REPEAT GEN_TAC THEN
  X_CHOOSE_TAC “x0:hrat”
               (SPEC “X:hreal” CUT_NONEMPTY) THEN
  ASM_CASES_TAC “(cut X)(u hrat_mul x0)” THENL
   [REWRITE_TAC[hrat_lt] THEN DISCH_THEN(X_CHOOSE_TAC “d:hrat”) THEN
    X_CHOOSE_TAC “x:hrat” (SPECL [“X:hreal”,
                                        “d hrat_mul x0”] CUT_NEARTOP_ADD)
    THEN EXISTS_TAC “x:hrat” THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HRAT_RDISTRIB, HRAT_MUL_LID]) THEN
    REWRITE_TAC[HRAT_RDISTRIB, HRAT_MUL_LID] THEN
    MATCH_MP_TAC CUT_UBOUND THEN
    EXISTS_TAC “x hrat_add (d hrat_mul x0)” THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC
                o MATCH_MP CUT_STRADDLE
                o CONJ (ASSUME “(cut X)(x0 hrat_add (d hrat_mul x0))”)
                o CONJUNCT2) THEN
    REWRITE_TAC[HRAT_LT_RADD, HRAT_LT_LADD, HRAT_LT_LMUL],
    DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC “x0:hrat” THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Define the operations. "hreal_lt" and "hreal_sub are convenient later     *)
(*---------------------------------------------------------------------------*)

val hreal_1 = new_definition("hreal_1",
  “hreal_1 = hreal (cut_of_hrat hrat_1)”);

val hreal_add = new_infixl_definition("hreal_add",
  “hreal_add X Y = hreal (\w. ?x y. (w = x hrat_add y) /\
                                    (cut X) x /\ (cut Y) y)”, 500);

val hreal_mul = new_infixl_definition("hreal_mul",
  “hreal_mul X Y = hreal (\w. ?x y. (w = x hrat_mul y) /\
                                    (cut X) x /\ (cut Y) y)”,600);

val hreal_inv = new_definition("hreal_inv",
  “hreal_inv X = hreal (\w. ?d. (d hrat_lt hrat_1) /\
                   (!x. (cut X) x ==> ($hrat_mul w x) hrat_lt d))”);

val hreal_sup = new_definition("hreal_sup",
  “hreal_sup P = hreal (\w. ?X. (P X) /\ (cut X) w)”);

val hreal_lt = new_definition("hreal_lt",
  “hreal_lt X Y = ~(X = Y) /\ !x. (cut X) x ==> (cut Y) x”);
val _ = set_fixity "hreal_lt" (Infix(NONASSOC, 450))


(*---------------------------------------------------------------------------*)
(* Prove the appropriate closure properties of the basic operations          *)
(*---------------------------------------------------------------------------*)

val HREAL_INV_ISACUT = store_thm("HREAL_INV_ISACUT",
  “!X. isacut (\w.
      ?d. d hrat_lt hrat_1 /\ (!x. cut X x ==> (w hrat_mul x) hrat_lt d))”,
  GEN_TAC THEN REWRITE_TAC[isacut] THEN REPEAT CONJ_TAC THEN BETA_TAC THENL
   [X_CHOOSE_TAC “d:hrat” (SPEC “hrat_1” HRAT_DOWN) THEN
    X_CHOOSE_TAC “z:hrat” (SPEC “X:hreal” CUT_BOUNDED) THEN
    MAP_EVERY EXISTS_TAC [“d hrat_mul (hrat_inv z)”, “d:hrat”] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP CUT_STRADDLE o
               C CONJ (ASSUME “~(cut X z)”)) THEN
    REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_LT_RMUL1, HRAT_LT_L1],

    X_CHOOSE_TAC “y:hrat” (SPEC “X:hreal” CUT_NONEMPTY) THEN
    EXISTS_TAC “hrat_inv y” THEN CONV_TAC NOT_EXISTS_CONV THEN
    GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o SPEC “y:hrat”)) THEN
    ASM_REWRITE_TAC[HRAT_MUL_LINV, HRAT_LT_GT],

    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN “d:hrat” STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC “d:hrat” THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC “z:hrat” THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_TAC THEN MATCH_MP_TAC HRAT_LT_TRANS THEN
    EXISTS_TAC “x hrat_mul z” THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[HRAT_LT_RMUL],

    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN “d:hrat” STRIP_ASSUME_TAC) THEN
    X_CHOOSE_THEN “e:hrat” STRIP_ASSUME_TAC
      (MATCH_MP HRAT_MEAN (ASSUME “d hrat_lt hrat_1”)) THEN
    EXISTS_TAC “(e hrat_mul x) hrat_mul (hrat_inv d)” THEN CONJ_TAC THENL
     [EXISTS_TAC “e:hrat” THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC “z:hrat” THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_LT_RMUL1] THEN
      ONCE_REWRITE_TAC[AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
        “a hrat_mul (b hrat_mul c) = b hrat_mul (a hrat_mul c)”] THEN
      REWRITE_TAC[HRAT_LT_L1],
      ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
      ASM_REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_GT_LMUL1, HRAT_GT_L1]]]);

val HREAL_ADD_ISACUT = store_thm("HREAL_ADD_ISACUT",
  “!X Y. isacut (\w. ?x y. (w = x hrat_add y) /\ cut X x /\ cut Y y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[isacut] THEN REPEAT CONJ_TAC THENL
   [X_CHOOSE_TAC “x:hrat” (SPEC “X:hreal” CUT_NONEMPTY) THEN
    X_CHOOSE_TAC “y:hrat” (SPEC “Y:hreal” CUT_NONEMPTY) THEN
    EXISTS_TAC “x hrat_add y” THEN BETA_TAC THEN
    MAP_EVERY EXISTS_TAC [“x:hrat”, “y:hrat”] THEN
    ASM_REWRITE_TAC[],

    X_CHOOSE_TAC “x:hrat” (SPEC “X:hreal” CUT_BOUNDED) THEN
    X_CHOOSE_TAC “y:hrat” (SPEC “Y:hreal” CUT_BOUNDED) THEN
    EXISTS_TAC “x hrat_add y” THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [“u:hrat”, “v:hrat”])
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MATCH_MP_TAC HRAT_LT_NE THEN MATCH_MP_TAC HRAT_LT_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CUT_STRADDLE THENL
     [EXISTS_TAC “X:hreal”, EXISTS_TAC “Y:hreal”] THEN
    ASM_REWRITE_TAC[],

    MAP_EVERY X_GEN_TAC [“w:hrat”, “z:hrat”] THEN BETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (EVERY_TCL (map X_CHOOSE_THEN
      [“u:hrat”, “v:hrat”]) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_ASSUM (UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY (fn tm => EXISTS_TAC “(z hrat_mul (hrat_inv (u hrat_add v)))
                                       hrat_mul ^tm”)
              [“u:hrat”, “v:hrat”]
    THEN REWRITE_TAC[GSYM HRAT_LDISTRIB, GSYM HRAT_MUL_ASSOC,
                     HRAT_MUL_LINV, HRAT_MUL_RID] THEN
    CONJ_TAC THEN MATCH_MP_TAC CUT_DOWN THENL
     [EXISTS_TAC “u:hrat”, EXISTS_TAC “v:hrat”] THEN
    ASM_REWRITE_TAC[HRAT_MUL_ASSOC, HRAT_LT_LMUL1, HRAT_LT_R1],

    X_GEN_TAC “w:hrat” THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [“x:hrat”, “y:hrat”])
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    X_CHOOSE_TAC “u:hrat” (UNDISCH_ALL (SPECL [“X:hreal”,
                                                     “x:hrat”] CUT_UP))
    THEN EXISTS_TAC “u hrat_add y” THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [“u:hrat”, “y:hrat”], ALL_TAC] THEN
    ASM_REWRITE_TAC[HRAT_LT_RADD]]);

val HREAL_MUL_ISACUT = store_thm("HREAL_MUL_ISACUT",
  “!X Y. isacut (\w. ?x y. (w = x hrat_mul y) /\ cut X x /\ cut Y y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[isacut] THEN REPEAT CONJ_TAC THENL
   [X_CHOOSE_TAC “x:hrat” (SPEC “X:hreal” CUT_NONEMPTY) THEN
    X_CHOOSE_TAC “y:hrat” (SPEC “Y:hreal” CUT_NONEMPTY) THEN
    EXISTS_TAC “x hrat_mul y” THEN BETA_TAC THEN
    MAP_EVERY EXISTS_TAC [“x:hrat”, “y:hrat”] THEN
    ASM_REWRITE_TAC[],

    X_CHOOSE_TAC “x:hrat” (SPEC “X:hreal” CUT_BOUNDED) THEN
    X_CHOOSE_TAC “y:hrat” (SPEC “Y:hreal” CUT_BOUNDED) THEN
    EXISTS_TAC “x hrat_mul y” THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [“u:hrat”, “v:hrat”])
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MATCH_MP_TAC HRAT_LT_NE THEN MATCH_MP_TAC HRAT_LT_MUL2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CUT_STRADDLE THENL
     [EXISTS_TAC “X:hreal”, EXISTS_TAC “Y:hreal”] THEN
    ASM_REWRITE_TAC[],

    MAP_EVERY X_GEN_TAC [“w:hrat”, “z:hrat”] THEN BETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (EVERY_TCL (map X_CHOOSE_THEN
      [“u:hrat”, “v:hrat”]) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_ASSUM (UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC “u:hrat” THEN
    EXISTS_TAC “v hrat_mul (z hrat_mul (hrat_inv (u hrat_mul v)))” THEN
    ASM_REWRITE_TAC[HRAT_MUL_ASSOC] THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN
    ONCE_REWRITE_TAC[HRAT_MUL_ASSOC] THEN
    REWRITE_TAC[HRAT_MUL_LINV, HRAT_MUL_LID] THEN
    MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “v:hrat” THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC
     [AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
        “(a hrat_mul b) hrat_mul c = (c hrat_mul a) hrat_mul b”]
    THEN ASM_REWRITE_TAC[HRAT_LT_LMUL1, HRAT_LT_R1],

    X_GEN_TAC “w:hrat” THEN BETA_TAC THEN
    DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [“x:hrat”, “y:hrat”])
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    X_CHOOSE_TAC “u:hrat”
                 (UNDISCH_ALL (SPECL [“X:hreal”, “x:hrat”] CUT_UP))
    THEN EXISTS_TAC “u hrat_mul y” THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [“u:hrat”, “y:hrat”], ALL_TAC] THEN
    ASM_REWRITE_TAC[HRAT_LT_RMUL]]);

(*---------------------------------------------------------------------------*)
(* Now prove the various theorems about the new type                         *)
(*---------------------------------------------------------------------------*)

val HREAL_ADD_SYM = store_thm("HREAL_ADD_SYM",
  “!X Y. X hreal_add Y = Y hreal_add X”,
  let val vars = [“a:hrat”, “b:hrat”] in
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_THEN((EVERY_TCL o map X_CHOOSE_THEN) vars ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC (rev vars) THEN ONCE_REWRITE_TAC[HRAT_ADD_SYM]
  THEN ASM_REWRITE_TAC[] end);

val HREAL_MUL_SYM = store_thm("HREAL_MUL_SYM",
  “!X Y. X hreal_mul Y = Y hreal_mul X”,
  let val vars = [“a:hrat”, “b:hrat”] in
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_mul] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_THEN((EVERY_TCL o map X_CHOOSE_THEN) vars ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC (rev vars) THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM]
  THEN ASM_REWRITE_TAC[] end);

val HREAL_ADD_ASSOC = store_thm("HREAL_ADD_ASSOC",
  “!X Y Z. X hreal_add (Y hreal_add Z) = (X hreal_add Y) hreal_add Z”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN BETA_TAC THEN
  CONV_TAC(REDEPTH_CONV(LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV))
  THEN EQ_TAC THEN
  DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["u", "v", "x", "y"]) STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXISTS_TAC [“u hrat_add x”, “y:hrat”,
                          “u:hrat”, “x:hrat”],
    MAP_EVERY EXISTS_TAC [“x:hrat”, “y hrat_add v”,
                          “y:hrat”, “v:hrat”]]
  THEN ASM_REWRITE_TAC[HRAT_ADD_ASSOC]);

val HREAL_MUL_ASSOC = store_thm("HREAL_MUL_ASSOC",
  “!X Y Z. X hreal_mul (Y hreal_mul Z) = (X hreal_mul Y) hreal_mul Z”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_mul] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_MUL_ISACUT] THEN BETA_TAC THEN
  CONV_TAC(REDEPTH_CONV(LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV))
  THEN EQ_TAC THEN
  DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["u", "v", "x", "y"]) STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXISTS_TAC [“u hrat_mul x”, “y:hrat”,
                          “u:hrat”, “x:hrat”],
    MAP_EVERY EXISTS_TAC [“x:hrat”, “y hrat_mul v”,
                          “y:hrat”, “v:hrat”]]
  THEN ASM_REWRITE_TAC[HRAT_MUL_ASSOC]);

val HREAL_LDISTRIB = store_thm("HREAL_LDISTRIB",
  “!X Y Z. X hreal_mul (Y hreal_add Z) =
              (X hreal_mul Y) hreal_add (X hreal_mul Z)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_mul, hreal_add] THEN AP_TERM_TAC THEN
  CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
  (REWRITE_TAC o map (REWRITE_RULE[hreal_tybij]))
    [HREAL_MUL_ISACUT, HREAL_ADD_ISACUT] THEN BETA_TAC THEN
  CONV_TAC(REDEPTH_CONV(LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV))
  THEN EQ_TAC THENL
   [DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["a", "b", "c", "d"]) STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [“a hrat_mul c”, “a hrat_mul d”,
        “a:hrat”, “c:hrat”, “a:hrat”, “d:hrat”] THEN
    ASM_REWRITE_TAC[HRAT_LDISTRIB],
    DISCH_THEN(EVERY_TCL (map (X_CHOOSE_THEN o C (curry mk_var) (==`:hrat`==))
     ["a", "b", "c", "d", "e", "f"]) STRIP_ASSUME_TAC) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [“c:hrat”, “e:hrat”] HRAT_LT_TOTAL) THENL
     [MAP_EVERY EXISTS_TAC [“e:hrat”, “d hrat_add f”,
                            “d:hrat”, “f:hrat”] THEN
      ASM_REWRITE_TAC[HRAT_LDISTRIB],

      MAP_EVERY EXISTS_TAC [“e:hrat”,
        “((hrat_inv e) hrat_mul (c hrat_mul d)) hrat_add f”,
        “(hrat_inv e) hrat_mul (c hrat_mul d)”, “f:hrat”] THEN
      ASM_REWRITE_TAC
       [HRAT_LDISTRIB, HRAT_MUL_ASSOC, HRAT_MUL_RINV, HRAT_MUL_LID] THEN
      MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “d:hrat” THEN
      ASM_REWRITE_TAC[HRAT_LT_LMUL1, HRAT_LT_L1],

      MAP_EVERY EXISTS_TAC [“c:hrat”,
        “d hrat_add ((hrat_inv c) hrat_mul (e hrat_mul f))”,
        “d:hrat”, “(hrat_inv c) hrat_mul (e hrat_mul f)”] THEN
      ASM_REWRITE_TAC
       [HRAT_LDISTRIB, HRAT_MUL_ASSOC, HRAT_MUL_RINV, HRAT_MUL_LID] THEN
      MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “f:hrat” THEN
      ASM_REWRITE_TAC[HRAT_LT_LMUL1, HRAT_LT_L1]]]);

val HREAL_MUL_LID = store_thm("HREAL_MUL_LID",
  “!X. hreal_1 hreal_mul X = X”,
  GEN_TAC THEN REWRITE_TAC[hreal_1, hreal_mul] THEN
  MATCH_MP_TAC EQUAL_CUTS THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_MUL_ISACUT] THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] ISACUT_HRAT] THEN
  REWRITE_TAC[cut_of_hrat] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV “w:hrat”) THEN GEN_TAC THEN BETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(REPEAT_TCL CHOOSE_THEN
     (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “y:hrat” THEN
    ASM_REWRITE_TAC[HRAT_LT_LMUL1],
    DISCH_THEN(X_CHOOSE_THEN “v:hrat” STRIP_ASSUME_TAC o MATCH_MP CUT_UP)
    THEN MAP_EVERY EXISTS_TAC [“w hrat_mul (hrat_inv v)”,“v:hrat”]
    THEN ASM_REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_RID]
    THEN ONCE_REWRITE_TAC[HRAT_MUL_SYM] THEN ASM_REWRITE_TAC[HRAT_LT_L1]]);

val HREAL_MUL_LINV = store_thm("HREAL_MUL_LINV",
  “!X. (hreal_inv X) hreal_mul X = hreal_1”,
  GEN_TAC THEN REWRITE_TAC[hreal_inv, hreal_mul, hreal_1] THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_INV_ISACUT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[cut_of_hrat] THEN
  CONV_TAC(X_FUN_EQ_CONV “z:hrat”) THEN BETA_TAC THEN GEN_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME “cut X y”)) THEN
    MATCH_MP_TAC HRAT_LT_TRANS THEN EXISTS_TAC “d:hrat” THEN
    ASM_REWRITE_TAC[],

    DISCH_THEN(X_CHOOSE_THEN “d:hrat” (CONJUNCTS_THEN2 (MP_TAC o
      ONCE_REWRITE_RULE[GSYM HRAT_GT_L1]) ASSUME_TAC) o MATCH_MP HRAT_MEAN)
    THEN DISCH_THEN(X_CHOOSE_TAC “x:hrat” o
      SPEC “X:hreal” o MATCH_MP CUT_NEARTOP_MUL) THEN
    MAP_EVERY EXISTS_TAC [“z hrat_mul (hrat_inv x)”, “x:hrat”] THEN
(* begin change *)
    GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM HRAT_MUL_ASSOC]
    THEN ASM_REWRITE_TAC[HRAT_MUL_LINV, HRAT_MUL_RID] THEN
(* end change *)
(* Rewriting change forces change in proof
 *   ASM_REWRITE_TAC[GSYM HRAT_MUL_ASSOC, HRAT_MUL_LINV, HRAT_MUL_RID] THEN
 *)
    EXISTS_TAC “d:hrat” THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC “y:hrat” THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
    DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C CONJ (CONJUNCT2 th))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CUT_STRADDLE) THEN
    SUBST1_TAC(SYM(SPECL [“y:hrat”,
                          “((hrat_inv z) hrat_mul d) hrat_mul x”,
                          “z hrat_mul (hrat_inv x)”] HRAT_LT_LMUL)) THEN
    ONCE_REWRITE_TAC[AC(HRAT_MUL_ASSOC,HRAT_MUL_SYM)
                     “(a hrat_mul b) hrat_mul ((c hrat_mul d) hrat_mul e) =
                      ((c hrat_mul a) hrat_mul (b hrat_mul e)) hrat_mul d”]
    THEN REWRITE_TAC[HRAT_MUL_LINV, HRAT_MUL_LID]]);

val HREAL_NOZERO = store_thm("HREAL_NOZERO",
  “!X Y. ~(X hreal_add Y = X)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add] THEN
  DISCH_THEN(MP_TAC o AP_TERM “cut”) THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN
  DISCH_THEN(MP_TAC o CONV_RULE (X_FUN_EQ_CONV “w:hrat”)) THEN
  REWRITE_TAC[] THEN CONV_TAC NOT_FORALL_CONV THEN BETA_TAC THEN
  X_CHOOSE_TAC “y:hrat” (SPEC “Y:hreal” CUT_NONEMPTY) THEN
  X_CHOOSE_TAC “x:hrat”
               (SPECL [“X:hreal”, “y:hrat”] CUT_NEARTOP_ADD) THEN
  EXISTS_TAC “x hrat_add y” THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [“x:hrat”, “y:hrat”] THEN
  ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Need a sequence of lemmas for totality of addition; it's convenient       *)
(* to define a "subtraction" function and prove its closure                  *)
(*---------------------------------------------------------------------------*)

val hreal_sub = new_infixl_definition("hreal_sub",
“hreal_sub Y X = hreal (\w. ?x. ~((cut X) x) /\ (cut Y) ($hrat_add x w))”,
  500);

val HREAL_LT_LEMMA = store_thm("HREAL_LT_LEMMA",
  “!X Y. X hreal_lt Y ==> ?x. ~(cut X x) /\ (cut Y x)”,
  let val lemma1 = TAUT_CONV “~(~a /\ b) = b ==> a”
      val lemma2 = TAUT_CONV “(a ==> b) /\ (b ==> a) = (a = b)”
  in
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  CONV_TAC(LAND_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[hreal_lt, lemma1] THEN
  DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C CONJ th)) THEN
  CONV_TAC(LAND_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[lemma2] THEN CONV_TAC(LAND_CONV EXT_CONV) THEN
  DISCH_THEN(MP_TAC o AP_TERM “hreal”) THEN REWRITE_TAC[hreal_tybij]
  end);

val HREAL_SUB_ISACUT = store_thm("HREAL_SUB_ISACUT",
“!X Y. X hreal_lt Y ==> isacut(\w. ?x. ~cut X x /\ cut Y(x hrat_add w))”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[isacut] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC “y:hrat” o MATCH_MP HREAL_LT_LEMMA) THEN
    FIRST_ASSUM(X_CHOOSE_THEN “z:hrat” MP_TAC
                o MATCH_MP (SPECL [“Y:hreal”, “y:hrat”] CUT_UP)
                o CONJUNCT2) THEN
    REWRITE_TAC[hrat_lt] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN “x:hrat” SUBST_ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [“x:hrat”, “y:hrat”] THEN
    ASM_REWRITE_TAC[],

    X_CHOOSE_TAC “y:hrat” (SPEC “Y:hreal” CUT_BOUNDED) THEN
    EXISTS_TAC “y:hrat” THEN CONV_TAC NOT_EXISTS_CONV THEN
    X_GEN_TAC “d:hrat” THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISJ2_TAC THEN MATCH_MP_TAC CUT_UBOUND THEN EXISTS_TAC “y:hrat” THEN
    ASM_REWRITE_TAC[HRAT_LT_ADDR],

    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN “z:hrat” STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC “z:hrat” THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “z hrat_add x” THEN
    ASM_REWRITE_TAC[HRAT_LT_LADD],

    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN “z:hrat” STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN “w:hrat” MP_TAC o MATCH_MP
     (SPECL [“Y:hreal”, “z hrat_add x”] CUT_UP)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN “d:hrat” SUBST_ALL_TAC) o REWRITE_RULE[hrat_lt]) THEN
    EXISTS_TAC “x hrat_add d” THEN REWRITE_TAC[HRAT_LT_ADDL] THEN
    EXISTS_TAC “z:hrat” THEN ASM_REWRITE_TAC[HRAT_ADD_ASSOC]]);

val HREAL_SUB_ADD = store_thm("HREAL_SUB_ADD",
  “!X Y. X hreal_lt Y ==> ((Y hreal_sub X) hreal_add X = Y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_add, hreal_sub] THEN
  DISCH_TAC THEN MATCH_MP_TAC EQUAL_CUTS THEN
  REWRITE_TAC[REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[hreal_tybij]
                   (MATCH_MP HREAL_SUB_ISACUT th)]) THEN
  CONV_TAC (X_FUN_EQ_CONV “w:hrat”) THEN BETA_TAC THEN GEN_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(REPEAT_TCL CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN “z:hrat” STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CUT_DOWN THEN
    EXISTS_TAC “z hrat_add x” THEN ASM_REWRITE_TAC[] THEN
    GEN_REWR_TAC RAND_CONV [HRAT_ADD_SYM] THEN
    REWRITE_TAC[HRAT_LT_LADD] THEN MATCH_MP_TAC CUT_STRADDLE THEN
    EXISTS_TAC “X:hreal” THEN ASM_REWRITE_TAC[],

    DISCH_TAC THEN ASM_CASES_TAC “(cut X) w” THENL
     [FIRST_ASSUM (X_CHOOSE_THEN “z:hrat” MP_TAC o MATCH_MP
       (SPECL [“X:hreal”, “Y:hreal”] HREAL_LT_LEMMA)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN “k:hrat” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o
        MATCH_MP CUT_UP)) THEN REWRITE_TAC[hrat_lt] THEN
      DISCH_THEN(X_CHOOSE_THEN “e:hrat” SUBST_ALL_TAC) THEN
      X_CHOOSE_THEN “x:hrat”
                    MP_TAC (SPECL[“e:hrat”, “w:hrat”] HRAT_DOWN2) THEN
      SUBST1_TAC(SYM(SPECL [“x:hrat”, “e:hrat”,
                            “z:hrat”] HRAT_LT_LADD)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP CUT_DOWN o
       CONJ (ASSUME “cut Y(z hrat_add e)”)) MP_TAC) THEN
      REWRITE_TAC[hrat_lt] THEN DISCH_THEN(X_CHOOSE_TAC “y:hrat”) THEN
      MAP_EVERY EXISTS_TAC [“x:hrat”, “y:hrat”] THEN ASM_REWRITE_TAC[]
      THEN CONJ_TAC THENL
       [EXISTS_TAC “z:hrat” THEN ASM_REWRITE_TAC[],
        MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “w:hrat” THEN
        ASM_REWRITE_TAC[HRAT_LT_ADDR]],

      FIRST_ASSUM(X_CHOOSE_THEN “k:hrat” MP_TAC o MATCH_MP CUT_UP) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[hrat_lt]
      THEN DISCH_THEN(X_CHOOSE_THEN “e:hrat” SUBST_ALL_TAC) THEN
      X_CHOOSE_THEN “y:hrat” STRIP_ASSUME_TAC
       (SPECL [“X:hreal”, “e:hrat”] CUT_NEARTOP_ADD) THEN
      ASM_CASES_TAC “(cut Y) (y hrat_add e)” THENL
       [SUBGOAL_THEN “y hrat_lt w” MP_TAC THENL
         [MATCH_MP_TAC CUT_STRADDLE THEN EXISTS_TAC “X:hreal” THEN
          ASM_REWRITE_TAC[], ALL_TAC] THEN REWRITE_TAC[hrat_lt] THEN
        DISCH_THEN(X_CHOOSE_THEN “x:hrat” SUBST_ALL_TAC) THEN
        MAP_EVERY EXISTS_TAC [“x:hrat”, “y:hrat”] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_ACCEPT_TAC HRAT_ADD_SYM,
          EXISTS_TAC “y hrat_add e” THEN
          ONCE_REWRITE_TAC[AC(HRAT_ADD_ASSOC,HRAT_ADD_SYM)
            “(a hrat_add b) hrat_add c = (a hrat_add c) hrat_add b”] THEN
          ASM_REWRITE_TAC[],
          FIRST_ASSUM ACCEPT_TAC],

        UNDISCH_TAC “cut X y” THEN CONV_TAC CONTRAPOS_CONV THEN
        DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC CUT_UBOUND THEN
        EXISTS_TAC “w:hrat” THEN ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(SPECL [“w:hrat”, “y:hrat”, “e:hrat”] HRAT_LT_RADD)) THEN
        MATCH_MP_TAC CUT_STRADDLE THEN EXISTS_TAC “Y:hreal” THEN
        ASM_REWRITE_TAC[]]]]);

val HREAL_LT_TOTAL = store_thm("HREAL_LT_TOTAL",
  “!X Y. (X = Y) \/ (X hreal_lt Y) \/ (Y hreal_lt X)”,
  let val lemma = TAUT_CONV “a \/ (~a /\ b) \/ (~a /\ c) = ~b /\ ~c ==> a”
      val negneg = TAUT_CONV “a = ~(~a)” in
  REPEAT GEN_TAC THEN REWRITE_TAC[hreal_lt] THEN
  SUBST1_TAC(ISPECL[“Y:hreal”, “X:hreal”] EQ_SYM_EQ) THEN
  REWRITE_TAC[lemma] THEN CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN(MP_TAC o MATCH_MP(CONTRAPOS(SPEC_ALL EQUAL_CUTS))) THEN
  CONV_TAC(ONCE_DEPTH_CONV(X_FUN_EQ_CONV “x:hrat”)) THEN
  DISCH_THEN(X_CHOOSE_THEN “z:hrat” MP_TAC o CONV_RULE NOT_FORALL_CONV) THEN
  ASM_CASES_TAC “cut X z” THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN DISCH_TAC
  THENL [DISJ2_TAC, DISJ1_TAC] THEN
  GEN_REWR_TAC I [negneg] THEN
  DISCH_THEN(X_CHOOSE_THEN “w:hrat” MP_TAC o CONV_RULE NOT_FORALL_CONV) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fn th =>
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CUT_STRADDLE o CONJ th)) THEN
  MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “z:hrat” THEN ASM_REWRITE_TAC[] end);

val HREAL_LT = store_thm("HREAL_LT",
  “!X Y. X hreal_lt Y = ?D. Y = X hreal_add D”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(curry op THEN (EXISTS_TAC “Y hreal_sub X”) o MP_TAC) THEN
    DISCH_THEN(CONV_TAC o (LAND_CONV o REWR_CONV) o
      SYM o MATCH_MP HREAL_SUB_ADD) THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM,
    DISCH_THEN(X_CHOOSE_THEN “D:hreal” SUBST_ALL_TAC) THEN
    REWRITE_TAC[hreal_lt, NOT_EQ_SYM(SPEC_ALL HREAL_NOZERO)] THEN
    X_GEN_TAC “x:hrat” THEN DISCH_TAC THEN
    X_CHOOSE_TAC “e:hrat” (SPEC “D:hreal” CUT_NONEMPTY) THEN
    X_CHOOSE_THEN “d:hrat” MP_TAC (SPECL [“x:hrat”, “e:hrat”] HRAT_DOWN2) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC “w:hrat” o REWRITE_RULE[hrat_lt])
      (ASSUME_TAC o MATCH_MP CUT_DOWN o CONJ (ASSUME “cut D e”))) THEN
    REWRITE_TAC[hreal_add, REWRITE_RULE[hreal_tybij] HREAL_ADD_ISACUT] THEN
    BETA_TAC THEN MAP_EVERY EXISTS_TAC [“w:hrat”, “d:hrat”] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC HRAT_ADD_SYM,
      MATCH_MP_TAC CUT_DOWN THEN EXISTS_TAC “x:hrat” THEN
      ASM_REWRITE_TAC[HRAT_LT_ADDR]]]);

val HREAL_ADD_TOTAL = store_thm("HREAL_ADD_TOTAL",
  “!X Y. (X = Y) \/ (?D. Y = X hreal_add D) \/ (?D. X = Y hreal_add D)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[SYM(SPEC_ALL HREAL_LT)] THEN
  MATCH_ACCEPT_TAC HREAL_LT_TOTAL);

(*---------------------------------------------------------------------------*)
(* Now prove the supremum property                                           *)
(*---------------------------------------------------------------------------*)

val HREAL_SUP_ISACUT = store_thm("HREAL_SUP_ISACUT",
  “!P. (?X:hreal. P X) /\ (?Y. (!X. P X ==> X hreal_lt Y))
        ==> isacut (\w. ?X. P X /\ cut X w)”,
  let val lemma = TAUT_CONV “~(a /\ b) = (a ==> ~b)” in
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN CHOOSE_TAC) THEN
  REWRITE_TAC[isacut] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [X_CHOOSE_TAC “x:hrat” (SPEC “X:hreal” CUT_NONEMPTY) THEN
    MAP_EVERY EXISTS_TAC [“x:hrat”, “X:hreal”] THEN ASM_REWRITE_TAC[],

    X_CHOOSE_TAC “y:hrat” (SPEC “Y:hreal” CUT_BOUNDED) THEN
    EXISTS_TAC “y:hrat” THEN CONV_TAC NOT_EXISTS_CONV THEN
    X_GEN_TAC “Z:hreal” THEN REWRITE_TAC[lemma] THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[hreal_lt] THEN
    DISCH_THEN(MP_TAC o SPEC “y:hrat” o CONJUNCT2) THEN ASM_REWRITE_TAC[],

    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC “Z:hreal”) ASSUME_TAC) THEN
    EXISTS_TAC “Z:hreal” THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CUT_DOWN THEN
    EXISTS_TAC “x:hrat” THEN ASM_REWRITE_TAC[],

    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN “Z:hreal” STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_TAC “y:hrat” o MATCH_MP
      (SPECL [“Z:hreal”, “x:hrat”] CUT_UP)) THEN
    EXISTS_TAC “y:hrat” THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC “Z:hreal” THEN ASM_REWRITE_TAC[]] end);

val HREAL_SUP = store_thm("HREAL_SUP",
  “!P. (?X. P X) /\ (?Y. (!X. P X ==> X hreal_lt Y)) ==>
         (!Y. (?X. P X /\ Y hreal_lt X) = Y hreal_lt (hreal_sup P))”,
  let val stac = FIRST_ASSUM(SUBST1_TAC o MATCH_MP
    (REWRITE_RULE[hreal_tybij] HREAL_SUP_ISACUT)) in
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[hreal_sup, hreal_lt] THEN stac THEN
    REWRITE_TAC[GSYM hreal_lt] THEN BETA_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN “X:hreal” STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [DISCH_THEN(MP_TAC o AP_TERM “cut”) THEN stac THEN
        DISCH_THEN(MP_TAC o CONV_RULE (X_FUN_EQ_CONV “x:hrat”)) THEN
        BETA_TAC THEN REWRITE_TAC[] THEN CONV_TAC NOT_FORALL_CONV THEN
        FIRST_ASSUM(X_CHOOSE_TAC “x:hrat” o MATCH_MP HREAL_LT_LEMMA) THEN
        EXISTS_TAC “x:hrat” THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC “X:hreal” THEN ASM_REWRITE_TAC[],
        X_GEN_TAC “x:hrat” THEN DISCH_THEN(ASSUME_TAC o MATCH_MP
         (CONJUNCT2(REWRITE_RULE[hreal_lt] (ASSUME “Y hreal_lt X”)))) THEN
        EXISTS_TAC “X:hreal” THEN ASM_REWRITE_TAC[]]],
    DISCH_THEN(X_CHOOSE_THEN “x:hrat” MP_TAC o MATCH_MP HREAL_LT_LEMMA) THEN
    REWRITE_TAC[hreal_sup] THEN stac THEN BETA_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC “X:hreal”)) THEN
    EXISTS_TAC “X:hreal” THEN ASM_REWRITE_TAC[] THEN
    REPEAT_TCL DISJ_CASES_THEN (fn th => SUBST_ALL_TAC th ORELSE ASSUME_TAC th)
     (SPECL [“X:hreal”, “Y:hreal”] HREAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(SUBST_ALL_TAC o EQT_INTRO o CONJUNCT2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC,
      MP_TAC (CONJUNCT2 (REWRITE_RULE[hreal_lt] (ASSUME “X hreal_lt Y”))) THEN
      CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC “x:hrat” THEN
      ASM_REWRITE_TAC[]]] end);

(*---------------------------------------------------------------------------*)
(* Required lemmas about the halfreals - mostly to drive CANCEL_TAC          *)
(*---------------------------------------------------------------------------*)

val HREAL_RDISTRIB = store_thm("HREAL_RDISTRIB",
  “!x y z. (x hreal_add y) hreal_mul z =
              (x hreal_mul z) hreal_add (y hreal_mul z)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HREAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC HREAL_LDISTRIB);

val HREAL_EQ_ADDR = store_thm("HREAL_EQ_ADDR",
  “!x y. ~(x hreal_add y = x)”,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC HREAL_NOZERO);

val HREAL_EQ_ADDL = store_thm("HREAL_EQ_ADDL",
  “!x y. ~(x = x hreal_add y)”,
  REPEAT GEN_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC HREAL_EQ_ADDR);

val HREAL_EQ_LADD = store_thm("HREAL_EQ_LADD",
  “!x y z. (x hreal_add y = x hreal_add z) = (y = z)”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (SPECL [“y:hreal”, “z:hreal”] HREAL_ADD_TOTAL) THENL
     [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM ACCEPT_TAC, ALL_TAC, ALL_TAC] THEN
    POP_ASSUM(X_CHOOSE_THEN “d:hreal” SUBST1_TAC) THEN
    REWRITE_TAC[HREAL_ADD_ASSOC, HREAL_EQ_ADDR, HREAL_EQ_ADDL],
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

val HREAL_LT_REFL = store_thm("HREAL_LT_REFL",
  “!x. ~(x hreal_lt x)”,
  GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  REWRITE_TAC[HREAL_EQ_ADDL]);

val HREAL_LT_ADDL = store_thm("HREAL_LT_ADDL",
  “!x y. x hreal_lt (x hreal_add y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  EXISTS_TAC “y:hreal” THEN REFL_TAC);

val HREAL_LT_NE = store_thm("HREAL_LT_NE",
  “!x y. x hreal_lt y  ==> ~(x = y)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  MATCH_ACCEPT_TAC HREAL_EQ_ADDL);

val HREAL_LT_ADDR = store_thm("HREAL_LT_ADDR",
  “!x y. ~((x hreal_add y) hreal_lt x)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC, HREAL_EQ_ADDL]);

val HREAL_LT_GT = store_thm("HREAL_LT_GT",
  “!x y. x hreal_lt y  ==> ~(y hreal_lt x)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC, HREAL_EQ_ADDL]);

val HREAL_LT_ADD2 = store_thm("HREAL_LT_ADD2",
  “!x1 x2 y1 y2. x1 hreal_lt y1 /\ x2 hreal_lt y2 ==>
     (x1 hreal_add x2) hreal_lt (y1 hreal_add y2)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN “d1:hreal” SUBST1_TAC)
    (X_CHOOSE_THEN “d2:hreal” SUBST1_TAC)) THEN
  EXISTS_TAC “d1 hreal_add d2” THEN
  CONV_TAC(AC_CONV(HREAL_ADD_ASSOC,HREAL_ADD_SYM)));

val HREAL_LT_LADD = store_thm("HREAL_LT_LADD",
  “!x y z. (x hreal_add y) hreal_lt (x hreal_add z) = y hreal_lt z”,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LT] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN “d:hreal” (curry op THEN (EXISTS_TAC “d:hreal”) o MP_TAC))
  THEN REWRITE_TAC[GSYM HREAL_ADD_ASSOC, HREAL_EQ_LADD]);

(*---------------------------------------------------------------------------*)
(* CANCEL_CONV - Try to cancel, rearranging using AC laws as needed          *)
(*                                                                           *)
(* The first two arguments are the associative and commutative laws, as      *)
(* given to AC_CONV. The remaining list of theorems should be of the form:   *)
(*                                                                           *)
(* |- (a & b ~ a & c) = w (e.g. b ~ c)                                       *)
(* |-    (a & b ~ a)  = x (e.g. F)                                           *)
(* |-     (a ~ a & c) = y (e.g. T)                                           *)
(* |-         (a ~ a) = z (e.g. F)                                           *)
(*                                                                           *)
(* For some operator (written as infix &) and relation (~).                  *)
(*                                                                           *)
(* Theorems may be of the form |- ~ P or |- P, rather that equations; they   *)
(* will be transformed to |- P = F and |- P = T automatically if needed.     *)
(*                                                                           *)
(* Note that terms not cancelled will remain in their original order, but    *)
(* will be flattened to right-associated form.                               *)
(*---------------------------------------------------------------------------*)

fun intro th =
  if is_eq(concl th) then th else
  if is_neg(concl th) then EQF_INTRO th
  else EQT_INTRO th;

val lhs_rator2 = rator o rator o lhs o snd o strip_forall o concl;

fun rmel i list =
    case list of
      [] => []
    | h::t => if aconv h i then t else h :: rmel i t

fun ERR s = mk_HOL_ERR "realaxScript" "CANCEL_CONV"s

fun CANCEL_CONV(assoc,sym,lcancelthms) tm =
  let val lcthms = map (intro o SPEC_ALL) lcancelthms
      val eqop = lhs_rator2 (Lib.trye hd lcthms)
      val binop = lhs_rator2 sym
      fun strip_binop tm =
        if (rator(rator tm) ~~ binop handle HOL_ERR _ => false)
        then strip_binop (rand(rator tm)) @ strip_binop(rand tm)
        else [tm]
      val mk_binop = curry mk_comb o curry mk_comb binop
      val list_mk_binop = end_itlist mk_binop
      val (c,alist) = strip_comb tm
      val _ = assert (aconv eqop) c
  in
    case alist of
      [l1,r1] => let
        val l = strip_binop l1
        and r = strip_binop r1
        val i = op_intersect aconv l r
      in
        if null i then raise ERR "unchanged"
        else let
            val itm = list_mk_binop i
            val l' = end_itlist (C (curry op o)) (map rmel i) l
            and r' = end_itlist (C (curry op o)) (map rmel i) r
            fun mk ts = mk_binop itm (list_mk_binop ts)
                handle HOL_ERR _ => itm
            val l2 = mk l'
            val r2 = mk r'
            val le = (EQT_ELIM o AC_CONV(assoc,sym) o mk_eq) (l1,l2)
            val re = (EQT_ELIM o AC_CONV(assoc,sym) o mk_eq) (r1,r2)
            val eqv = MK_COMB(AP_TERM eqop le,re)
          in
            CONV_RULE(RAND_CONV
                        (end_itlist (curry op ORELSEC) (map REWR_CONV lcthms)))
                     eqv
          end
      end
    | _ => raise ERR ""
  end

(*---------------------------------------------------------------------------*)
(* Tactic to do all the obvious simplifications via cancellation etc.        *)
(*---------------------------------------------------------------------------*)
fun mk_rewrites th =
   let val th = Drule.SPEC_ALL th
       val t = Thm.concl th
   in
   if is_eq t
   then [th]
   else if is_conj t
        then (op @ o (mk_rewrites##mk_rewrites) o Drule.CONJ_PAIR) th
        else if is_neg t
             then [Drule.EQF_INTRO th]
             else [Drule.EQT_INTRO th]
   end;

val CANCEL_TAC = (C (curry op THEN)
 (PURE_REWRITE_TAC
    (itlist (append o mk_rewrites)
            [REFL_CLAUSE, EQ_CLAUSES, NOT_CLAUSES,
               AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES,
               COND_CLAUSES, FORALL_SIMP, EXISTS_SIMP,
               ABS_SIMP] []))
 o CONV_TAC o ONCE_DEPTH_CONV o end_itlist (curry op ORELSEC))
 (map CANCEL_CONV
      [(HREAL_ADD_ASSOC,HREAL_ADD_SYM,
        [HREAL_EQ_LADD, HREAL_EQ_ADDL, HREAL_EQ_ADDR, EQ_SYM]),
       (HREAL_ADD_ASSOC,HREAL_ADD_SYM,
        [HREAL_LT_LADD, HREAL_LT_ADDL, HREAL_LT_ADDR, HREAL_LT_REFL])]);

(*---------------------------------------------------------------------------*)
(* Define operations on representatives.                                     *)
(*---------------------------------------------------------------------------*)

val treal_0 = new_definition("treal_0",
  “treal_0 = (hreal_1,hreal_1)”);

val treal_1 = new_definition("treal_1",
  “treal_1 = (hreal_1 hreal_add hreal_1,hreal_1)”);

val treal_neg = new_definition("treal_neg",
  “treal_neg (x:hreal,(y:hreal)) = (y,x)”);

val treal_add = new_infixl_definition("treal_add",
  “$treal_add (x1,y1) (x2,y2) = (x1 hreal_add x2, y1 hreal_add y2)”,500);

val treal_mul = new_infixl_definition("treal_mul",
  “treal_mul (x1,y1) (x2,y2) =
      ((x1 hreal_mul x2) hreal_add (y1 hreal_mul y2),
       (x1 hreal_mul y2) hreal_add (y1 hreal_mul x2))”, 600);

val treal_lt = new_definition("treal_lt",
“treal_lt (x1,y1) (x2,y2) = (x1 hreal_add y2) hreal_lt (x2 hreal_add y1)”);
val _ = temp_set_fixity "treal_lt" (Infix(NONASSOC, 450))

val treal_inv = new_definition("treal_inv",
  “treal_inv (x,y) =
      if (x = y) then treal_0
      else if y hreal_lt x then
        ((hreal_inv (x hreal_sub y)) hreal_add hreal_1,hreal_1)
      else (hreal_1,(hreal_inv(y hreal_sub x)) hreal_add hreal_1)”);

(*---------------------------------------------------------------------------*)
(* Define the equivalence relation and prove it *is* one                     *)
(*---------------------------------------------------------------------------*)

val treal_eq = new_definition("treal_eq",
  “treal_eq (x1,y1) (x2,y2) = (x1 hreal_add y2 = x2 hreal_add y1)”);
val _ = temp_set_fixity "treal_eq" (Infix(NONASSOC, 450))

val TREAL_EQ_REFL = store_thm("TREAL_EQ_REFL",
  “!x. x treal_eq x”,
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN REFL_TAC);

val TREAL_EQ_SYM = store_thm("TREAL_EQ_SYM",
  “!x y. x treal_eq y = y treal_eq x”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC);

val TREAL_EQ_TRANS = store_thm("TREAL_EQ_TRANS",
  “!x y z. x treal_eq y /\ y treal_eq z ==> x treal_eq z”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq] THEN
  DISCH_THEN(MP_TAC o MK_COMB o (AP_TERM “$hreal_add” ## I) o CONJ_PAIR)
  THEN CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN CANCEL_TAC);

val TREAL_EQ_EQUIV = store_thm("TREAL_EQ_EQUIV",
  “!p q. p treal_eq q = ($treal_eq p = $treal_eq q)”,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV “r:hreal#hreal”)) THEN
  EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC “q:hreal#hreal”) THEN
      REWRITE_TAC[TREAL_EQ_REFL],
      DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
       [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TREAL_EQ_SYM]), ALL_TAC] THEN
      POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
      MATCH_ACCEPT_TAC TREAL_EQ_TRANS]);

val TREAL_EQ_AP = store_thm("TREAL_EQ_AP",
  “!p q. (p = q) ==> p treal_eq q”,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC TREAL_EQ_REFL);

(*---------------------------------------------------------------------------*)
(* Prove the properties of representatives                                   *)
(*---------------------------------------------------------------------------*)

val TREAL_10 = store_thm("TREAL_10",
  “~(treal_1 treal_eq treal_0)”,
  REWRITE_TAC[treal_1, treal_0, treal_eq, HREAL_NOZERO]);

val TREAL_ADD_SYM = store_thm("TREAL_ADD_SYM",
  “!x y. x treal_add y = y treal_add x”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                  [HREAL_ADD_SYM] THEN
  REFL_TAC);

val TREAL_MUL_SYM = store_thm("TREAL_MUL_SYM",
  “!x y. x treal_mul y = y treal_mul x”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                  [HREAL_MUL_SYM] THEN
  REWRITE_TAC[PAIR_EQ] THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM);

val TREAL_ADD_ASSOC = store_thm("TREAL_ADD_ASSOC",
  “!x y z. x treal_add (y treal_add z) = (x treal_add y) treal_add z”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC]);

val TREAL_MUL_ASSOC = store_thm("TREAL_MUL_ASSOC",
  “!x y z. x treal_mul (y treal_mul z) = (x treal_mul y) treal_mul z”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul] THEN
  REWRITE_TAC[HREAL_LDISTRIB, HREAL_RDISTRIB, PAIR_EQ, GSYM HREAL_MUL_ASSOC]
  THEN CONJ_TAC THEN CANCEL_TAC);

val TREAL_LDISTRIB = store_thm("TREAL_LDISTRIB",
  “!x y z. x treal_mul (y treal_add z) =
       (x treal_mul y) treal_add (x treal_mul z)”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul, treal_add] THEN
  REWRITE_TAC[HREAL_LDISTRIB, PAIR_EQ] THEN
  CONJ_TAC THEN CANCEL_TAC);

val TREAL_ADD_LID = store_thm("TREAL_ADD_LID",
  “!x. (treal_0 treal_add x) treal_eq x”,
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_add, treal_eq] THEN
  CANCEL_TAC);

val TREAL_MUL_LID = store_thm("TREAL_MUL_LID",
  “!x. (treal_1 treal_mul x) treal_eq x”,
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_1, treal_mul, treal_eq] THEN
  REWRITE_TAC[HREAL_MUL_LID, HREAL_LDISTRIB, HREAL_RDISTRIB] THEN
  CANCEL_TAC THEN CANCEL_TAC);

val TREAL_ADD_LINV = store_thm("TREAL_ADD_LINV",
  “!x. ((treal_neg x) treal_add x) treal_eq treal_0”,
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_neg, treal_add, treal_eq, treal_0]
  THEN CANCEL_TAC);

val TREAL_INV_0 = store_thm("TREAL_INV_0",
 Term`treal_inv (treal_0) treal_eq (treal_0)`,
  REWRITE_TAC[treal_inv, treal_eq, treal_0]);

val TREAL_MUL_LINV = store_thm("TREAL_MUL_LINV",
  “!x. ~(x treal_eq treal_0) ==>
              (((treal_inv x) treal_mul x) treal_eq treal_1)”,
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_eq, treal_inv] THEN
  CANCEL_TAC THEN DISCH_TAC THEN DISJ_CASES_THEN2
    (fn th => MP_TAC th THEN ASM_REWRITE_TAC[]) (DISJ_CASES_THEN ASSUME_TAC)
    (SPECL [“FST (x:hreal#hreal)”, “SND (x:hreal#hreal)”] HREAL_LT_TOTAL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HREAL_LT_GT) THEN
  PURE_ASM_REWRITE_TAC[COND_CLAUSES, treal_mul, treal_eq, treal_1] THEN
  REWRITE_TAC[HREAL_MUL_LID, HREAL_LDISTRIB, HREAL_RDISTRIB] THEN
  CANCEL_TAC THEN W(SUBST1_TAC o SYM o C SPEC HREAL_MUL_LINV o
    find_term(fn tm => rator(rator tm) ~~ “$hreal_sub” handle _ => false) o snd)
  THEN
  REWRITE_TAC[GSYM HREAL_LDISTRIB] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP HREAL_SUB_ADD) THEN REFL_TAC);

val TREAL_LT_TOTAL = store_thm("TREAL_LT_TOTAL",
  “!x y. x treal_eq y \/ x treal_lt y \/ y treal_lt x”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_eq] THEN
  MATCH_ACCEPT_TAC HREAL_LT_TOTAL);

val TREAL_LT_REFL = store_thm("TREAL_LT_REFL",
  “!x. ~(x treal_lt x)”,
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt] THEN
  MATCH_ACCEPT_TAC HREAL_LT_REFL);

val TREAL_LT_TRANS = store_thm("TREAL_LT_TRANS",
  “!x y z. x treal_lt y /\ y treal_lt z ==> x treal_lt z”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HREAL_LT_ADD2) THEN CANCEL_TAC THEN
  DISCH_TAC THEN GEN_REWR_TAC RAND_CONV  [HREAL_ADD_SYM]
  THEN POP_ASSUM ACCEPT_TAC);

val TREAL_LT_ADD = store_thm("TREAL_LT_ADD",
  “!x y z. (y treal_lt z) ==> (x treal_add y) treal_lt (x treal_add z)”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_add] THEN
  CANCEL_TAC);

val TREAL_LT_MUL = store_thm("TREAL_LT_MUL",
  “!x y. treal_0 treal_lt x /\ treal_0 treal_lt y ==>
           treal_0 treal_lt (x treal_mul y)”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_lt, treal_mul] THEN
  CANCEL_TAC THEN DISCH_THEN(CONJUNCTS_THEN
   (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[HREAL_LT])) THEN
  REWRITE_TAC[HREAL_LDISTRIB, HREAL_RDISTRIB] THEN CANCEL_TAC THEN CANCEL_TAC);

(*---------------------------------------------------------------------------*)
(* Rather than grub round proving the supremum property for representatives, *)
(* we prove the appropriate order-isomorphism {x::R|0 < r} <-> R^+           *)
(*---------------------------------------------------------------------------*)

val treal_of_hreal = new_definition("treal_of_hreal",
  “treal_of_hreal x = (x hreal_add hreal_1,hreal_1)”);

val hreal_of_treal = new_definition("hreal_of_treal",
  “hreal_of_treal (x,y) = @d. x = y hreal_add d”);

val TREAL_BIJ = store_thm("TREAL_BIJ",
  “(!h. (hreal_of_treal(treal_of_hreal h)) = h) /\
   (!r. treal_0 treal_lt r = (treal_of_hreal(hreal_of_treal r)) treal_eq r)”,
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[treal_of_hreal, hreal_of_treal] THEN
    CANCEL_TAC THEN CONV_TAC SYM_CONV THEN
    CONV_TAC(funpow 2 RAND_CONV ETA_CONV) THEN
    MATCH_MP_TAC SELECT_AX THEN EXISTS_TAC “h:hreal” THEN REFL_TAC,
    GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_0, treal_lt, treal_eq,
      treal_of_hreal, hreal_of_treal] THEN CANCEL_TAC THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o MATCH_MP HREAL_SUB_ADD) THEN
      DISCH_THEN(CONV_TAC o RAND_CONV o REWR_CONV o SYM o SELECT_RULE o
      EXISTS(“?d. d hreal_add (SND r) = FST r”, “(FST r) hreal_sub (SND r)”))
      THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                      [HREAL_ADD_SYM] THEN
      CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN REFL_TAC,
      DISCH_THEN(SUBST1_TAC o SYM) THEN CANCEL_TAC]]);

val TREAL_ISO = store_thm("TREAL_ISO",
  “!h i. h hreal_lt i ==> (treal_of_hreal h) treal_lt (treal_of_hreal i)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[treal_of_hreal, treal_lt] THEN CANCEL_TAC THEN
  CANCEL_TAC);

val TREAL_BIJ_WELLDEF = store_thm("TREAL_BIJ_WELLDEF",
  “!h i. h treal_eq i ==> (hreal_of_treal h = hreal_of_treal i)”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_eq, hreal_of_treal] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC(X_FUN_EQ_CONV “d:hreal”) THEN
  GEN_TAC THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o C AP_THM “SND(i:hreal#hreal)” o AP_TERM “$hreal_add”)
    THEN POP_ASSUM SUBST1_TAC,
    DISCH_THEN(MP_TAC o C AP_THM “SND(h:hreal#hreal)” o AP_TERM “$hreal_add”)
    THEN POP_ASSUM(SUBST1_TAC o SYM)] THEN
  CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM);

(*---------------------------------------------------------------------------*)
(* Prove that the operations on representatives are well-defined             *)
(*---------------------------------------------------------------------------*)

val TREAL_NEG_WELLDEF = store_thm("TREAL_NEG_WELLDEF",
  “!x1 x2. x1 treal_eq x2 ==> (treal_neg x1) treal_eq (treal_neg x2)”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_neg, treal_eq] THEN
  DISCH_THEN(curry op THEN (ONCE_REWRITE_TAC[HREAL_ADD_SYM]) o SUBST1_TAC) THEN
  REFL_TAC);

val TREAL_ADD_WELLDEFR = store_thm("TREAL_ADD_WELLDEFR",
  “!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_add y) treal_eq (x2 treal_add y)”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_add, treal_eq] THEN
  CANCEL_TAC);

val TREAL_ADD_WELLDEF = store_thm("TREAL_ADD_WELLDEF",
  “!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_add y1) treal_eq (x2 treal_add y2)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC “x1 treal_add y2” THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_ADD_SYM], ALL_TAC] THEN
  MATCH_MP_TAC TREAL_ADD_WELLDEFR THEN ASM_REWRITE_TAC[]);

val TREAL_MUL_WELLDEFR = store_thm("TREAL_MUL_WELLDEFR",
  “!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_mul y) treal_eq (x2 treal_mul y)”,
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_mul, treal_eq] THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    “(a hreal_add b) hreal_add (c hreal_add d) =
     (a hreal_add d) hreal_add (b hreal_add c)”] THEN
  REWRITE_TAC[GSYM HREAL_RDISTRIB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);

val TREAL_MUL_WELLDEF = store_thm("TREAL_MUL_WELLDEF",
  “!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_mul y1) treal_eq (x2 treal_mul y2)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC “x1 treal_mul y2” THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_MUL_SYM], ALL_TAC] THEN
  MATCH_MP_TAC TREAL_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]);

val TREAL_LT_WELLDEFR = store_thm("TREAL_LT_WELLDEFR",
  “!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_lt y = x2 treal_lt y)”,
  let fun mkc v tm = SYM(SPECL (v::snd(strip_comb tm)) HREAL_LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc “SND (x1:hreal#hreal)”)) THEN
  CONV_TAC(LAND_CONV(mkc “SND (x2:hreal#hreal)”)) THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    “a hreal_add (b hreal_add c) = (b hreal_add a) hreal_add c”] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC end);

val TREAL_LT_WELLDEFL = store_thm("TREAL_LT_WELLDEFL",
  “!x y1 y2. y1 treal_eq y2 ==> (x treal_lt y1 = x treal_lt y2)”,
  let fun mkc v tm = SYM(SPECL (v::snd(strip_comb tm)) HREAL_LT_LADD) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_lt, treal_eq] THEN
  DISCH_TAC THEN CONV_TAC(RAND_CONV(mkc “FST (y1:hreal#hreal)”)) THEN
  CONV_TAC(LAND_CONV(mkc “FST (y2:hreal#hreal)”)) THEN
  ONCE_REWRITE_TAC[AC(HREAL_ADD_ASSOC,HREAL_ADD_SYM)
    “a hreal_add (b hreal_add c) = (a hreal_add c) hreal_add b”] THEN
  POP_ASSUM SUBST1_TAC THEN CANCEL_TAC THEN AP_TERM_TAC THEN CANCEL_TAC end);

val TREAL_LT_WELLDEF = store_thm("TREAL_LT_WELLDEF",
  “!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_lt y1 = x2 treal_lt y2)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC “x1 treal_lt y2” THEN CONJ_TAC THENL
   [MATCH_MP_TAC TREAL_LT_WELLDEFL, MATCH_MP_TAC TREAL_LT_WELLDEFR] THEN
  ASM_REWRITE_TAC[]);

val TREAL_INV_WELLDEF = store_thm("TREAL_INV_WELLDEF",
  “!x1 x2. x1 treal_eq x2 ==> (treal_inv x1) treal_eq (treal_inv x2)”,
  let val lemma1 = prove
   (“(a hreal_add b' = b hreal_add a') ==>
        (a' hreal_lt a = b' hreal_lt b)”,
    DISCH_TAC THEN EQ_TAC THEN
    DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[HREAL_LT]) THEN
    POP_ASSUM MP_TAC THEN CANCEL_TAC THENL
     [DISCH_THEN(SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN CANCEL_TAC)
  val lemma2 = prove
   (“(a hreal_add b' = b hreal_add a') ==>
        ((a = a') = (b = b'))”,
    DISCH_TAC THEN EQ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC
    THEN CANCEL_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC) in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[treal_inv, treal_eq] THEN
  DISCH_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP lemma1) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP lemma2) THEN COND_CASES_TAC THEN
  REWRITE_TAC[TREAL_EQ_REFL] THEN COND_CASES_TAC THEN REWRITE_TAC[treal_eq]
  THEN CANCEL_TAC THEN CANCEL_TAC THEN AP_TERM_TAC THEN
  W(FREEZE_THEN(CONV_TAC o REWR_CONV) o GSYM o C SPEC HREAL_EQ_LADD o
    mk_comb o (curry mk_comb “$hreal_add” ## I) o (rand ## rand) o dest_eq o snd)
  THEN ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [HREAL_ADD_SYM] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC] THENL
   [RULE_ASSUM_TAC GSYM,
    MP_TAC(SPECL[“FST(x2:hreal#hreal)”, “SND(x2:hreal#hreal)”]
    HREAL_LT_TOTAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[HREAL_ADD_SYM])] THEN
  FIRST_ASSUM(fn th => FIRST_ASSUM(MP_TAC o EQ_MP (MATCH_MP lemma1 th))) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert(aconv “$hreal_lt” o rator o rator) o concl)
  THEN REPEAT(DISCH_THEN(SUBST1_TAC o MATCH_MP HREAL_SUB_ADD)) THEN
  FIRST_ASSUM SUBST1_TAC THEN REFL_TAC end);

val _ = export_theory();
