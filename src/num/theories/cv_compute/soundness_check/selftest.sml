open HolKernel boolLib testutils
open arithmeticTheory cvTheory
open cv_compute_unsoundTheory
open cv_computeLib
open gh2029contextTheory

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
  printresult = (fn f => "<a conversion>"),
  testfn = cv_computeLib.cv_compute} [g_xx]

fun gh2029 () =
    let
      (* -------------------------------------------------------------------------
       * Recreate cv_computeLib's characteristic theorem list.  For the CV part,
       * replace each standard cv constant in the conclusion by the corresponding
       * good (:cv option) instance above, then prove that transported conclusion.
       * ------------------------------------------------------------------------- *)

      val a = mk_var ("a", alpha);
      val b = mk_var ("b", alpha);
      val n = mk_var ("n", numSyntax.num);
      val m = mk_var ("m", numSyntax.num);
      val p = mk_var ("p", cvSyntax.cv);
      val q = mk_var ("q", cvSyntax.cv);
      val r = mk_var ("r", cvSyntax.cv);
      val s = mk_var ("s", cvSyntax.cv);

      val arithmetic_char_eqns = [
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
        ("suc2", CONJUNCT2 SUC_EQ)
      ];

      val standard_cv_char_eqns = [
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
        ("cv_fst1", SPEC_ALL (cj 1 cv_fst_def)),
        ("cv_fst2", SPEC_ALL (cj 2 cv_fst_def)),
        ("cv_snd1", SPEC_ALL (cj 1 cv_snd_def)),
        ("cv_snd2", SPEC_ALL (cj 2 cv_snd_def)),
        ("cv_ispair1", SPEC_ALL (cj 1 cv_ispair_def)),
        ("cv_ispair2", SPEC_ALL (cj 2 cv_ispair_def)),
        ("cv_eq", SPEC_ALL cv_eq_def)
      ];

      (* Explicit expected conclusions are needed here: ordinary HOL substitution
       * cannot change :cv into :cv option. *)
      val custom_cv_goals = [
        ("cval1", ``((demo_pair p q : cv option) = demo_pair r s) =
                  if p = r then q = s else F``),
        ("cval2", ``((demo_pair p q : cv option) = demo_num n) = F``),
        ("cval3", ``(demo_num m = demo_num n : cv option) = (m = n)``),
        ("cv_add1", ``(demo_add (demo_num m) (demo_num n) : cv option) =
                    demo_num (m+n)``),
        ("cv_add2", ``(demo_add (demo_num m) (demo_pair p q) : cv option) =
                    demo_num m``),
        ("cv_add3", ``(demo_add (demo_pair p q) (demo_num n) : cv option) =
                    demo_num n``),
        ("cv_add4", ``(demo_add (demo_pair p q) (demo_pair r s) : cv option) =
                    demo_num 0``),
        ("cv_sub1", ``(demo_sub (demo_num m) (demo_num n) : cv option) =
                    demo_num (m-n)``),
        ("cv_sub2", ``(demo_sub (demo_num m) (demo_pair p q) : cv option) =
                    demo_num m``),
        ("cv_sub3", ``(demo_sub (demo_pair p q) (demo_num n) : cv option) =
                    demo_num 0``),
        ("cv_sub4", ``(demo_sub (demo_pair p q) (demo_pair r s) : cv option) =
                    demo_num 0``),
        ("cv_mul1", ``(demo_mul (demo_num m) (demo_num n) : cv option) =
                    demo_num (m*n)``),
        ("cv_mul2", ``(demo_mul (demo_num m) (demo_pair p q) : cv option) =
                    demo_num 0``),
        ("cv_mul3", ``(demo_mul (demo_pair p q) (demo_num n) : cv option) =
                    demo_num 0``),
        ("cv_mul4", ``(demo_mul (demo_pair p q) (demo_pair r s) : cv option) =
                    demo_num 0``),
        ("cv_div1", ``(demo_div (demo_num m) (demo_num n) : cv option) =
                    demo_num (m DIV n)``),
        ("cv_div2", ``(demo_div (demo_num m) (demo_pair p q) : cv option) =
                    demo_num 0``),
        ("cv_div3", ``(demo_div (demo_pair p q) (demo_num n) : cv option) =
                    demo_num 0``),
        ("cv_div4", ``(demo_div (demo_pair p q) (demo_pair r s) : cv option) =
                    demo_num 0``),
        ("cv_mod1", ``(demo_mod (demo_num m) (demo_num n) : cv option) =
                    demo_num (m MOD n)``),
        ("cv_mod2", ``(demo_mod (demo_num m) (demo_pair p q) : cv option) =
                    demo_num m``),
        ("cv_mod3", ``(demo_mod (demo_pair p q) (demo_num n) : cv option) =
                    demo_num 0``),
        ("cv_mod4", ``(demo_mod (demo_pair p q) (demo_pair r s) : cv option) =
                    demo_num 0``),
        ("cv_lt1", ``(demo_lt (demo_num m) (demo_num n) : cv option) =
                   demo_num (if m < n then SUC 0 else 0)``),
        ("cv_lt2", ``(demo_lt (demo_num m) (demo_pair p q) : cv option) =
                   demo_num 0``),
        ("cv_lt3", ``(demo_lt (demo_pair p q) (demo_num n) : cv option) =
                   demo_num 0``),
        ("cv_lt4", ``(demo_lt (demo_pair p q) (demo_pair r s) : cv option) =
                   demo_num 0``),
        ("cv_if1", ``(demo_if (demo_num (SUC m)) p q : cv option) = p``),
        ("cv_if2", ``(demo_if (demo_num 0) p q : cv option) = q``),
        ("cv_if3", ``(demo_if (demo_pair r s) p q : cv option) = q``),
        ("cv_fst1", ``(demo_fst (demo_pair p q) : cv option) = p``),
        ("cv_fst2", ``(demo_fst (demo_num m) : cv option) = demo_num 0``),
        ("cv_snd1", ``(demo_snd (demo_pair p q) : cv option) = q``),
        ("cv_snd2", ``(demo_snd (demo_num m) : cv option) = demo_num 0``),
        ("cv_ispair1", ``(demo_ispair (demo_pair p q) : cv option) =
                       demo_num (SUC 0)``),
        ("cv_ispair2", ``(demo_ispair (demo_num m) : cv option) = demo_num 0``),
        ("cv_eq", ``(demo_eq p q : cv option) =
                  demo_num (if p = q then SUC 0 else 0)``)
      ] : (string * term) list;

      val transport_rewrites = [
        demo_pair_def, demo_fst_def, demo_snd_def, demo_ispair_def,
        demo_add_def, demo_sub_def, demo_mul_def, demo_div_def, demo_mod_def,
        demo_lt_def, demo_if_def, demo_eq_def,
        demo_num_good, demo_dec_enc_good, demo_enc_dec_good,
        demo_enc_11_good, demo_dec_11_good
      ];

      val _ = quietly BasicProvers.srw_ss ()
      fun simp ths = simpLib.SIMP_TAC (BasicProvers.srw_ss()) ths
      fun transport_char_eqn ((name, th), (goal_name, goal)) =
          if name <> goal_name then
            raise Fail ("characteristic equation order mismatch at " ^ name)
          else
            (name, TAC_PROOF (([], goal),
                              simp(th :: transport_rewrites)
                                  >> rewrite_tac[demo_enc_11_good]
                                  >> rewrite_tac[demo_dec_11_good]
                                  >> goalStack.print_tac"here"));

      val transported_cv_char_eqns =
          map transport_char_eqn (zip standard_cv_char_eqns custom_cv_goals);

      val char_eqns =
          arithmetic_char_eqns @ transported_cv_char_eqns @
          [("let", SPEC_ALL LET_THM)];

      (* Here is the mismatch: these terms are all at the bad :one option
         instance, while cval_type and the characteristic equations use
         :cv option. *)
      val bad_cval_terms = [
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
        ("cv_pair", ``demo_pair : one option -> one option -> one option``),
        ("cv_num", ``demo_num : num -> one option``),
        ("cv_fst", ``demo_fst : one option -> one option``),
        ("cv_snd", ``demo_snd : one option -> one option``),
        ("cv_ispair", ``demo_ispair : one option -> one option``),
        ("cv_add", ``demo_add : one option -> one option -> one option``),
        ("cv_sub", ``demo_sub : one option -> one option -> one option``),
        ("cv_mul", ``demo_mul : one option -> one option -> one option``),
        ("cv_div", ``demo_div : one option -> one option -> one option``),
        ("cv_mod", ``demo_mod : one option -> one option -> one option``),
        ("cv_lt", ``demo_lt : one option -> one option -> one option``),
        ("cv_if",
         ``demo_if : one option -> one option -> one option -> one option``),
        ("cv_eq", ``demo_eq : one option -> one option -> one option``)
      ];

      val bad_compute =
          Thm.compute {
            cval_terms = bad_cval_terms,
            cval_type = ``:cv option``,
                           num_type = ``:num``,
                                         char_eqns = char_eqns
          } [];

      (* The interpreter regards its internal Num 1 and Num 2 as different and
       * therefore returns internal Num 0. *)
      val bad_eq = bad_compute
                     ``demo_eq (demo_num 1) (demo_num 2) : one option``;

      val EVAL = computeLib.EVAL_CONV
      val _ = computeLib.add_funs [CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV demo_num_def]
                                  (* In HOL, however, every element of :one is equal.  Thus demo_num 1 and
                                   * demo_num 2 are both SOME one, demo_eq returns demo_num 1, and bad_eq
                                   * reduces to SOME one = NONE. *)
    in
      TAC_PROOF (([], “F”),
                 MP_TAC bad_eq >>
                 simp[demo_eq_def, demo_num_def] >>
                 simp[EVAL``demo_num 1``, EVAL``demo_num 2``, EVAL``demo_num 0``])
    end

val _ = shouldfail {
  checkexn = is_struct_HOL_ERR "Thm",
  printarg = K ("Test for gh2029 soundness issue with bad cv-polymorphism"),
  printresult = thm_to_string, testfn = gh2029} ();
