(* Test file. Uses:
    val ilogPath = "/homes/mjcg/Helene/newOpsem/xmlterm2csp/";
*)

(* Stuff needed when running interactively *)

quietdec := true; (* turn off printing *)

loadPath := "../java2opsem/testFiles/opsemFiles" :: ".." :: "solvers" :: (!loadPath);

app load ["newOpsemTheory","pairSyntax", "intLib","intSimps",
          "computeLib", "finite_mapTheory",
          "relationTheory", "stringLib",
          "PATH_EVAL",
          "IndDefLib", "IndDefRules",
          "term2xml","execSymb","extSolv",
          "AbsMinusTheory", "TritypeTheory"];

open newOpsemTheory bossLib pairSyntax intLib intSimps
     computeLib finite_mapTheory relationTheory stringLib
     PATH_EVAL IndDefLib IndDefRules term2xml execSymb extSolv
     AbsMinusTheory TritypeTheory;

quietdec := false; (* turn printing back on *)

(* Set up the compset for computeLib.EVAL *)
add_funs
 [outcome_case_def,
  outcome_case_if,
  pair_case_if,
  RUN,
  STEP1,
  FAPPLY_FUPDATE_THM,
  FUPDATE_LIST_THM,
  DOMSUB_FUPDATE_THM,
  DOMSUB_FEMPTY,
  FDOM_FUPDATE,
  FAPPLY_FUPDATE_THM,
  FDOM_FEMPTY,
  pred_setTheory.IN_INSERT,
  pred_setTheory.NOT_IN_EMPTY
 ];

(* Cause assumptions and tags to be printed 
show_assums := true;
show_tags := true;
*)


(* Various solvers *)

val ilogSolv = elim_state_CONV(satSolv(extSolv "ILOG"));

val AbsMinus_def =
 Define
  `AbsMinus =
    Seq (Assign "result" (Const 0))
        (Seq (Assign "k" (Const 0))
           (Seq
              (Cond (LessEq (Var "i") (Var "j"))
                 (Assign "k" (Plus (Var "k") (Const 1))) Skip)
              (Seq
                 (Cond
                    (And (Equal (Var "k") (Const 1))
                       (Not (Equal (Var "i") (Var "j"))))
                    (Assign "result" (Sub (Var "j") (Var "i")))
                    (Assign "result" (Sub (Var "i") (Var "j"))))
                 (Assign "Result" (Var "result")))))`;

g ``IMP (\state. ScalarOf (state ' "i") < ScalarOf (state ' "j"))
          (\initial_state state.
            ScalarOf (state ' "Result") =
            ScalarOf (state ' "j") - ScalarOf (state ' "i"))
          AbsMinus``;

e (IMP_EVAL_TAC(holSolv OMEGA_CONV));

e (CONV_TAC EVAL THEN SIMP_TAC arith_ss []);

val AbsMinusTh1 =
   time prove
    (``IMP (\state. ScalarOf (state ' "i") < ScalarOf (state ' "j"))
           (\initial_state state.
             ScalarOf (state ' "Result") =
             ScalarOf (state ' "j") - ScalarOf (state ' "i"))
           AbsMinus``,
     IMP_EVAL_TAC(holSolv OMEGA_CONV)
      THEN CONV_TAC EVAL
      THEN SIMP_TAC arith_ss []);

val AbsMinusTh2 =
   time prove
    (``IMP (\state. T)
           (\initial_state state.
             ScalarOf (initial_state ' "i") < ScalarOf (initial_state ' "j") ==>
             (ScalarOf (state ' "Result") = ScalarOf (state ' "j") - ScalarOf (state ' "i")))
           AbsMinus``,
     IMP_EVAL_TAC(holSolv OMEGA_CONV)
      THEN CONV_TAC(EVAL THENC elim_state_CONV COOPER_CONV));

val AbsMinusTh3 =
   time prove
    (``IMP (\state. T)
           (\initial_state state.
             ScalarOf (initial_state ' "i") <
             ScalarOf (initial_state ' "j") ==>
             (ScalarOf (state ' "Result") =
              ScalarOf (state ' "j") - ScalarOf (state ' "i")))
           AbsMinus``,
     IMP_EVAL_TAC ilogSolv
      THEN CONV_TAC EVAL
      THEN CONV_TAC(elim_state_CONV COOPER_CONV)); 

val Tritype_def =
 Define
  `Tritype =
       Seq (Assign "trityp" (Const 0))
         (Seq
            (Cond
               (Or
                  (Or (Equal (Var "i") (Const 0))
                     (Equal (Var "j") (Const 0)))
                  (Equal (Var "k") (Const 0))) (Assign "trityp" (Const 4))
               (Seq (Assign "trityp" (Const 0))
                  (Seq
                     (Cond (Equal (Var "i") (Var "j"))
                        (Assign "trityp" (Plus (Var "trityp") (Const 1)))
                        Skip)
                     (Seq
                        (Cond (Equal (Var "i") (Var "k"))
                           (Assign "trityp" (Plus (Var "trityp") (Const 2)))
                           Skip)
                        (Seq
                           (Cond (Equal (Var "j") (Var "k"))
                              (Assign "trityp"
                                 (Plus (Var "trityp") (Const 3))) Skip)
                           (Cond (Equal (Var "trityp") (Const 0))
                              (Cond
                                 (Or
                                    (LessEq (Plus (Var "i") (Var "j"))
                                       (Var "k"))
                                    (Or
                                       (LessEq (Plus (Var "j") (Var "k"))
                                          (Var "i"))
                                       (LessEq (Plus (Var "i") (Var "k"))
                                          (Var "j"))))
                                 (Assign "trityp" (Const 4))
                                 (Assign "trityp" (Const 1)))
                              (Cond (Less (Const 3) (Var "trityp"))
                                 (Assign "trityp" (Const 3))
                                 (Cond
                                    (And (Equal (Var "trityp") (Const 1))
                                       (Less (Var "k")
                                          (Plus (Var "i") (Var "j"))))
                                    (Assign "trityp" (Const 2))
                                    (Cond
                                       (And (Equal (Var "trityp") (Const 2))
                                          (Less (Var "j")
                                             (Plus (Var "i") (Var "k"))))
                                       (Assign "trityp" (Const 2))
                                       (Cond
                                          (And
                                             (Equal (Var "trityp")
                                                (Const 3))
                                             (Less (Var "i")
                                                (Plus (Var "j") (Var "k"))))
                                          (Assign "trityp" (Const 2))
                                          (Assign "trityp"
                                             (Const 4))))))))))))
            (Assign "Result" (Var "trityp")))`;

val TritypeTh1 =
  time prove
  (``IMP(\state.
          0 <= ScalarOf (state ' "i") /\ 0 <= ScalarOf (state ' "j") /\ 0 <= ScalarOf (state ' "k")
          /\
          (ScalarOf (state ' "i") + ScalarOf (state ' "j") <=
           ScalarOf (state ' "k") \/
           ScalarOf (state ' "j") + ScalarOf (state ' "k") <=
           ScalarOf (state ' "i") \/
           ScalarOf (state ' "i") + ScalarOf (state ' "k") <=
           ScalarOf (state ' "j")))
        (\initial_state state. ScalarOf (state ' "Result") = 4)
        Tritype /\
      IMP(\state.
          0 <= ScalarOf (state ' "i") /\ 0 <= ScalarOf (state ' "j") /\ 0 <= ScalarOf (state ' "k")
          /\
          (~(ScalarOf (state ' "i") + ScalarOf (state ' "j") <=
             ScalarOf (state ' "k") \/
             ScalarOf (state ' "j") + ScalarOf (state ' "k") <=
             ScalarOf (state ' "i") \/
             ScalarOf (state ' "i") + ScalarOf (state ' "k") <=
             ScalarOf (state ' "j")) /\
           (ScalarOf (state ' "i") = ScalarOf (state ' "j")) /\
           (ScalarOf (state ' "j") = ScalarOf (state ' "k"))))
         (\initial_state state. ScalarOf (state ' "Result") = 3)
         Tritype /\
      IMP(\state.
          0 <= ScalarOf (state ' "i") /\ 0 <= ScalarOf (state ' "j") /\ 0 <= ScalarOf (state ' "k")
          /\
          (~(ScalarOf (state ' "i") + ScalarOf (state ' "j") <=
             ScalarOf (state ' "k") \/
             ScalarOf (state ' "j") + ScalarOf (state ' "k") <=
             ScalarOf (state ' "i") \/
             ScalarOf (state ' "i") + ScalarOf (state ' "k") <=
             ScalarOf (state ' "j")) /\
           ~((ScalarOf (state ' "i") = ScalarOf (state ' "j")) /\
             (ScalarOf (state ' "j") = ScalarOf (state ' "k"))) /\
           ((ScalarOf (state ' "i") = ScalarOf (state ' "j")) \/
            (ScalarOf (state ' "j") = ScalarOf (state ' "k")) \/
            (ScalarOf (state ' "i") = ScalarOf (state ' "k")))))
         (\initial_state state. ScalarOf (state ' "Result") = 2)
         Tritype /\
      IMP(\state.
          0 <= ScalarOf (state ' "i") /\ 0 <= ScalarOf (state ' "j") /\ 0 <= ScalarOf (state ' "k")
          /\
          (~(ScalarOf (state ' "i") + ScalarOf (state ' "j") <=
             ScalarOf (state ' "k") \/
             ScalarOf (state ' "j") + ScalarOf (state ' "k") <=
             ScalarOf (state ' "i") \/
             ScalarOf (state ' "i") + ScalarOf (state ' "k") <=
             ScalarOf (state ' "j")) /\
           ~((ScalarOf (state ' "i") = ScalarOf (state ' "j")) /\
             (ScalarOf (state ' "j") = ScalarOf (state ' "k"))) /\
           ~((ScalarOf (state ' "i") = ScalarOf (state ' "j")) \/
             (ScalarOf (state ' "j") = ScalarOf (state ' "k")) \/
             (ScalarOf (state ' "i") = ScalarOf (state ' "k")))))
         (\initial_state state. ScalarOf (state ' "Result") = 1)
         Tritype``,
   REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC(holSolv COOPER_CONV)
    THEN elim_state_TAC
    THEN RW_TAC (srw_ss()) []
    THEN OMEGA_TAC);


val TritypeTh2 =
  time prove
  (``IMP (\state. T)
         (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (ScalarOf (initial_state ' "i") +
           ScalarOf (initial_state ' "j") <=
           ScalarOf (initial_state ' "k") \/
           ScalarOf (initial_state ' "j") +
           ScalarOf (initial_state ' "k") <=
           ScalarOf (initial_state ' "i") \/
           ScalarOf (initial_state ' "i") +
           ScalarOf (initial_state ' "k") <=
           ScalarOf (initial_state ' "j") ==>
           (ScalarOf (state ' "Result") = 4)))
         Tritype /\
      IMP (\state. T)
          (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (~(ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "j") <=
             ScalarOf (initial_state ' "k") \/
             ScalarOf (initial_state ' "j") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "i") \/
             ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "j")) /\
           (ScalarOf (initial_state ' "i") =
            ScalarOf (initial_state ' "j")) /\
           (ScalarOf (initial_state ' "j") =
            ScalarOf (initial_state ' "k")) ==>
           (ScalarOf (state ' "Result") = 3)))
          Tritype /\
      IMP (\state. T)
          (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (~(ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "j") <=
             ScalarOf (initial_state ' "k") \/
             ScalarOf (initial_state ' "j") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "i") \/
             ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "j")) /\
           ~((ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "j")) /\
             (ScalarOf (initial_state ' "j") =
              ScalarOf (initial_state ' "k"))) /\
           ((ScalarOf (initial_state ' "i") =
             ScalarOf (initial_state ' "j")) \/
            (ScalarOf (initial_state ' "j") =
             ScalarOf (initial_state ' "k")) \/
            (ScalarOf (initial_state ' "i") =
             ScalarOf (initial_state ' "k"))) ==>
           (ScalarOf (state ' "Result") = 2)))
          Tritype /\
      IMP (\state. T)
          (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (~(ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "j") <=
             ScalarOf (initial_state ' "k") \/
             ScalarOf (initial_state ' "j") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "i") \/
             ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "j")) /\
           ~((ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "j")) /\
             (ScalarOf (initial_state ' "j") =
              ScalarOf (initial_state ' "k"))) /\
           ~((ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "j")) \/
             (ScalarOf (initial_state ' "j") =
              ScalarOf (initial_state ' "k")) \/
             (ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "k"))) ==>
           (ScalarOf (state ' "Result") = 1)))
          Tritype``,
   REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC(holSolv COOPER_CONV)
    THEN elim_state_TAC
    THEN RW_TAC (srw_ss()) []
    THEN OMEGA_TAC);


val TritypeTh3 =
  time prove
  (``IMP (\state. T)
         (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (ScalarOf (initial_state ' "i") +
           ScalarOf (initial_state ' "j") <=
           ScalarOf (initial_state ' "k") \/
           ScalarOf (initial_state ' "j") +
           ScalarOf (initial_state ' "k") <=
           ScalarOf (initial_state ' "i") \/
           ScalarOf (initial_state ' "i") +
           ScalarOf (initial_state ' "k") <=
           ScalarOf (initial_state ' "j") ==>
           (ScalarOf (state ' "Result") = 4)))
         Tritype /\
      IMP (\state. T)
          (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (~(ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "j") <=
             ScalarOf (initial_state ' "k") \/
             ScalarOf (initial_state ' "j") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "i") \/
             ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "j")) /\
           (ScalarOf (initial_state ' "i") =
            ScalarOf (initial_state ' "j")) /\
           (ScalarOf (initial_state ' "j") =
            ScalarOf (initial_state ' "k")) ==>
           (ScalarOf (state ' "Result") = 3)))
          Tritype /\
      IMP (\state. T)
          (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (~(ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "j") <=
             ScalarOf (initial_state ' "k") \/
             ScalarOf (initial_state ' "j") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "i") \/
             ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "j")) /\
           ~((ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "j")) /\
             (ScalarOf (initial_state ' "j") =
              ScalarOf (initial_state ' "k"))) /\
           ((ScalarOf (initial_state ' "i") =
             ScalarOf (initial_state ' "j")) \/
            (ScalarOf (initial_state ' "j") =
             ScalarOf (initial_state ' "k")) \/
            (ScalarOf (initial_state ' "i") =
             ScalarOf (initial_state ' "k"))) ==>
           (ScalarOf (state ' "Result") = 2)))
          Tritype /\
      IMP (\state. T)
          (\initial_state state.
          0 <= ScalarOf (initial_state ' "i") /\ 0 <= ScalarOf (initial_state ' "j") /\ 0 <= ScalarOf (initial_state ' "k")
          ==>
          (~(ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "j") <=
             ScalarOf (initial_state ' "k") \/
             ScalarOf (initial_state ' "j") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "i") \/
             ScalarOf (initial_state ' "i") +
             ScalarOf (initial_state ' "k") <=
             ScalarOf (initial_state ' "j")) /\
           ~((ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "j")) /\
             (ScalarOf (initial_state ' "j") =
              ScalarOf (initial_state ' "k"))) /\
           ~((ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "j")) \/
             (ScalarOf (initial_state ' "j") =
              ScalarOf (initial_state ' "k")) \/
             (ScalarOf (initial_state ' "i") =
              ScalarOf (initial_state ' "k"))) ==>
           (ScalarOf (state ' "Result") = 1)))
          Tritype``,
   REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC(elim_state_CONV(satSolv(extSolv "ILOG")))
    THEN elim_state_TAC
    THEN RW_TAC (srw_ss()) []
    THEN OMEGA_TAC);

