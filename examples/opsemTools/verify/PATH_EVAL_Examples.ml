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

open newOpsemTheory bossLib pairSyntax intLib Omega intSimps
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

(* Cause assumptions and tags to be printed *)
show_assums := true;
show_tags := true;



(* Various solvers *)
val CooperSimpSat = (SIMP_CONV (srw_ss()++COOPER_ss) [], "SIMP_CONV (srw_ss()++COOPER_ss)");
val OmegaSimpSat  = (SIMP_CONV (srw_ss()++OMEGA_ss) [],  "SIMP_CONV (srw_ss()++OMEGA_ss)");
val OmegaSat  = (OMEGA_CONV,  "OMEGA_CONV");

val ilogSolv = elim_state_CONV(satSolv(extSolv "ILOG"));
val solv = holSolv OMEGA_CONV;

val holSatSolv = elim_state_CONV(satSolv (hol_sat CooperSimpSat));
val holSatSolv = elim_state_CONV(satSolv (hol_sat OmegaSimpSat));
val holSatSolv = elim_state_CONV(satSolv (hol_sat OmegaSat));



(*
 result := 0;
 k := 0;
 if i <= j then k := k+1 else skip;
 if k=1 /\ ~(i=j) then result := j-i else result := i-j
*)
val absMinus =
 ``Seq
    (Assign "result" (Const 0))
    (Seq
      (Assign "k" (Const 0))
      (Seq
        (Cond (LessEq (Var "i") (Var "j"))
              (Assign "k" (Plus (Var "k") (Const 1)))
              Skip)
        (Cond (And (Equal (Var "k") (Const 1)) (Not(Equal (Var "i") (Var "j"))))
              (Assign "result" (Sub (Var "j") (Var "i")))
              (Assign "result" (Sub (Var "i") (Var "j"))))))``; 


val absMinus_run_th1 = SYM_RUN solv (EVAL_ASSUME ``(\s:state. T) s``) ``[^absMinus]``;
val absMinus_run_th1 = SYM_RUN solv (EVAL_ASSUME ``(\s. ScalarOf (s ' "i") <  ScalarOf (s ' "j")) s``) ``[^absMinus]``;
val absMinus_run_th2 = SYM_RUN solv (EVAL_ASSUME ``(\s. ScalarOf (s ' "j") <= ScalarOf (s ' "i")) s``) ``[^absMinus]``;

val absMinus_eval_th  = PATH_EVAL solv ``\s:state. T``  absMinus;
val absMinus_eval_th1 = PATH_EVAL solv ``\s. ScalarOf (s ' "i") <  ScalarOf (s ' "j")`` absMinus;
val absMinus_eval_th2 = PATH_EVAL solv ``\s. ScalarOf (s ' "j") <= ScalarOf (s ' "i")`` absMinus;

(* More examples: AbsMinus and Tritype *)

val AbsMinusHOL_th =  
 time prove
  (rhs(concl(AbsMinusTheory.MAIN_def)),
   REWRITE_TAC[IMP_INTRO_THM]
    THEN REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC holSatSolv
    THEN CONV_TAC(EVAL THENC elim_state_CONV COOPER_CONV));

(*
val AbsMinusILOG_th =  
 time prove
  (rhs(concl(AbsMinusTheory.MAIN_def)),
   REWRITE_TAC[IMP_INTRO_THM]
    THEN REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC ilogSolv
    THEN CONV_TAC(EVAL THENC elim_state_CONV COOPER_CONV));
*)

val TritypeHOL_th =  
 time prove
  (rhs(concl(TritypeTheory.MAIN_def)),
   REWRITE_TAC[IMP_INTRO_THM]
    THEN REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC holSatSolv
    THEN CONV_TAC(EVAL THENC elim_state_CONV COOPER_CONV));

(*
val TritypeILOG_th =  
 time prove
  (rhs(concl(TritypeTheory.MAIN_def)),
   REWRITE_TAC[IMP_INTRO_THM]
    THEN REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC ilogSolv
    THEN CONV_TAC(EVAL THENC elim_state_CONV COOPER_CONV));
*)

