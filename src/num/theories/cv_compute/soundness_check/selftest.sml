open HolKernel boolLib testutils
open arithmeticTheory cvTheory
open cv_compute_unsoundTheory
open cv_computeLib

val bad_cv_fst1 = bad_cv_fst1_lemma |> UNDISCH;

val cval_terms = [
    ("truth", boolSyntax.T),
    ("false", boolSyntax.F),
    ("cond", boolSyntax.conditional),
    ("let", boolSyntax.let_tm),
    ("alt_zero", numSyntax.alt_zero_tm),
    ("zero", numSyntax.zero_tm),
    ("suc", numSyntax.suc_tm),
    ("bit1", numSyntax.bit1_tm),
    ("bit2", numSyntax.bit2_tm),
    ("numeral", numSyntax.numeral_tm),
    ("add", numSyntax.plus_tm),
    ("sub", numSyntax.minus_tm),
    ("mul", numSyntax.mult_tm),
    ("div", numSyntax.div_tm),
    ("mod", numSyntax.mod_tm),
    ("lt", numSyntax.less_tm),
    ("cv_pair", cvSyntax.cv_pair_tm),
    ("cv_num", cvSyntax.cv_num_tm),
    ("cv_fst", bad_cv_fst2 |> concl |> lhs |> rator),
    ("cv_snd", cvSyntax.cv_snd_tm),
    ("cv_ispair", cvSyntax.cv_ispair_tm),
    ("cv_add", cvSyntax.cv_add_tm),
    ("cv_sub", cvSyntax.cv_sub_tm),
    ("cv_mul", cvSyntax.cv_mul_tm),
    ("cv_div", cvSyntax.cv_div_tm),
    ("cv_mod", cvSyntax.cv_mod_tm),
    ("cv_lt", cvSyntax.cv_lt_tm),
    ("cv_if", cvSyntax.cv_if_tm),
    ("cv_eq", cvSyntax.cv_eq_tm)
  ];

val a = mk_var ("a", alpha);
val b = mk_var ("b", alpha);
val n = mk_var ("n", numSyntax.num);
val m = mk_var ("m", numSyntax.num);
val p = mk_var ("p", cvSyntax.cv);
val q = mk_var ("q", cvSyntax.cv);
val r = mk_var ("r", cvSyntax.cv);
val s = mk_var ("s", cvSyntax.cv);

val char_eqns = [
  ("alt_zero", arithmeticTheory.ALT_ZERO),
  ("cond_T", CONJUNCT1 (SPECL [a,b] COND_CLAUSES)),
  ("cond_F", CONJUNCT2 (SPECL [a,b] COND_CLAUSES)),
  ("numeral", SPEC n NUMERAL_DEF),
  ("bit1", SPEC n BIT1),
  ("bit2", SPEC n BIT2),
  ("add1", SPEC n (CONJUNCT1 ADD)),
  ("add2", SPECL [m,n] (CONJUNCT2 ADD)),
  ("sub1", SPEC m (CONJUNCT1 SUB)),
  ("sub2", SPECL [m,n] (CONJUNCT2 SUB)),
  ("mul1", SPEC n (CONJUNCT1 MULT)),
  ("mul2", SPECL [m,n] (CONJUNCT2 MULT)),
  ("div", DIV_RECURSIVE),
  ("mod", MOD_RECURSIVE),
  ("lt1", CONJUNCT1 LT_RECURSIVE),
  ("lt2", CONJUNCT2 LT_RECURSIVE),
  ("suc1", CONJUNCT1 SUC_EQ),
  ("suc2", CONJUNCT2 SUC_EQ),
  ("cval1", cj 1 CV_EQ),
  ("cval2", cj 2 CV_EQ),
  ("cval3", cj 3 CV_EQ),
  ("cv_add1", cj 1 cv_add_def),
  ("cv_add2", cj 2 cv_add_def),
  ("cv_add3", cj 3 cv_add_def),
  ("cv_add4", cj 4 cv_add_def),
  ("cv_sub1", cj 1 cv_sub_def),
  ("cv_sub2", cj 2 cv_sub_def),
  ("cv_sub3", cj 3 cv_sub_def),
  ("cv_sub4", cj 4 cv_sub_def),
  ("cv_mul1", cj 1 cv_mul_def),
  ("cv_mul2", cj 2 cv_mul_def),
  ("cv_mul3", cj 3 cv_mul_def),
  ("cv_mul4", cj 4 cv_mul_def),
  ("cv_div1", cj 1 cv_div_def),
  ("cv_div2", cj 2 cv_div_def),
  ("cv_div3", cj 3 cv_div_def),
  ("cv_div4", cj 4 cv_div_def),
  ("cv_mod1", cj 1 cv_mod_def),
  ("cv_mod2", cj 2 cv_mod_def),
  ("cv_mod3", cj 3 cv_mod_def),
  ("cv_mod4", cj 4 cv_mod_def),
  ("cv_lt1", cj 1 cv_lt_def),
  ("cv_lt2", cj 2 cv_lt_def),
  ("cv_lt3", cj 3 cv_lt_def),
  ("cv_lt4", cj 4 cv_lt_def),
  ("cv_if1", cj 1 cv_if_def),
  ("cv_if2", cj 2 cv_if_def),
  ("cv_if3", cj 3 cv_if_def),
  ("cv_fst1", bad_cv_fst1),
  ("cv_fst2", bad_cv_fst2),
  ("cv_snd1", SPEC_ALL (cj 1 cv_snd_def)),
  ("cv_snd2", SPEC_ALL (cj 2 cv_snd_def)),
  ("cv_ispair1", SPEC_ALL (cj 1 cv_ispair_def)),
  ("cv_ispair2", SPEC_ALL (cj 2 cv_ispair_def)),
  ("cv_eq", SPEC_ALL cv_eq_def),
  ("let", SPEC_ALL LET_THM)
  ];

fun expect(str,fnname,msg) =
    str = "Thm" andalso fnname = "compute" andalso
    String.isSubstring "hypotheses" msg
val _ = shouldfail {checkexn = check_HOL_ERRexn expect,
                    printarg = K "compute w/bogus characteristic eqns",
                    printresult = K "returned a conversional",
                    testfn = Thm.compute}
                   {cval_terms = cval_terms,
                    cval_type = cvSyntax.cv,
                    num_type = numSyntax.num,
                    char_eqns = char_eqns
                   };

val p01 = “cv$Pair (cv$Num 0) (cv$Num 1)”
val p02 = “cv$Pair (cv$Num 0) (cv$Num 2)”

fun check_compute_vs_rewrite (nm, t0, rwt_ths) =
    let
      val _ = tprint ("Compute match-up/compute: " ^ nm)
      fun followup (Exn e) = die "Impossible"
        | followup (Res t) = (
          tprint ("Compute match-up/rewrite: " ^ nm);
          require_msg (check_result (aconv t))
                      term_to_string
                      (rhs o concl o REWRITE_CONV rwt_ths)
                      t0
        )
    in
      require_msgk (check_result (K true))
                   (fn t => PP.add_string (term_to_string t))
                   (rhs o concl o cv_computeLib.cv_compute [])
                   followup
                   t0
    end

val one_lt_2 = prove(“1n < 2”, REWRITE_TAC[ONE,TWO,LESS_MONO_EQ,SUC_POS])


val _ = List.app check_compute_vs_rewrite [
      ("cv_if on pair", “cv_if ^p01 (cv$Num 0) (cv$Num 1)”, [cv_if_def]),
      ("cv_mod on pair(1)", “cv_mod ^p01 (cv$Num 2)”, [cv_mod_def]),
      ("cv_mod on pair(2)", “cv_mod ^p01 (cv$Num 0)”, [cv_mod_def]),
      ("cv_div on pair(1)", “cv_div ^p01 (cv$Num 2)”, [cv_div_def]),
      ("cv_div on pair(2)", “cv_div ^p01 (cv$Num 2)”, [cv_div_def]),
      ("cv_mul on pair(1)", “cv_mul ^p01 (cv$Num 2)”, [cv_mul_def]),
      ("cv_mul on pair(2)", “cv_mul ^p01 (cv$Num 1)”, [cv_mul_def]),
      ("cv_mul on pair(3)", “cv_mul ^p01 (cv$Num 0)”, [cv_mul_def]),
      ("cv_lt num/num = T", “cv_lt (cv$Num 1) (cv$Num 2)”, [cv_lt_def,one_lt_2,GSYM ONE]),
      ("cv_lt num/num = F", “cv_lt (cv$Num 2) (cv$Num 2)”,
       [cv_lt_def,one_lt_2,GSYM ONE, prim_recTheory.LESS_REFL]),
      ("cv_lt num/pair", “cv_lt (cv$Num 0) ^p01”,
       [cv_lt_def,one_lt_2,GSYM ONE, prim_recTheory.LESS_REFL]),
      ("cv_lt pair/pair", “cv_lt ^p01 ^p02”,
       [cv_lt_def,one_lt_2,GSYM ONE, prim_recTheory.LESS_REFL]),
      ("cv_lt pair/num + T", “cv_lt ^p01 (cv$Num 1)”, [cv_lt_def,one_lt_2,GSYM ONE]),
      ("cv_lt pair/num + F", “cv_lt ^p01 (cv$Num 0)”, [cv_lt_def,one_lt_2,GSYM ONE])
    ]

val _ = shouldfail {
  checkexn = is_struct_HOL_ERR "Thm",
  printarg = K "Duplicate variables in compute code eqns",
  printresult = thm_to_string,
  testfn = cv_computeLib.cv_compute [g_xx]} “g (cv$Num 2) (cv$Num 3)”
