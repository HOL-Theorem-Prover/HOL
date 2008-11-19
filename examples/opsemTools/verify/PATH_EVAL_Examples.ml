(* Stuff needed when running interactively *)

quietdec := true; (* turn off printing *)

loadPath := "../extract" :: "../java2opsem/testFiles/opsemFiles" :: ".." :: "solvers" :: (!loadPath);

app load ["newOpsemTheory","pairSyntax", "intLib","intSimps",
          "computeLib", "finite_mapTheory",
          "relationTheory", "stringLib",
          "PATH_EVAL",
          "IndDefLib", "IndDefRules",
(*        "term2xml",
          "execSymb",
          "extSolv",     *)
          "AbsMinusTheory", "TritypeTheory", 
          "GeneratedFlasherManagerTheory","F1Theory"];

open newOpsemTheory bossLib pairSyntax intLib Omega intSimps
     computeLib finite_mapTheory relationTheory stringLib
     PATH_EVAL IndDefLib IndDefRules 
(*   term2xml 
     execSymb
     extSolv             *)
     AbsMinusTheory TritypeTheory 
     GeneratedFlasherManagerTheory F1Theory;

quietdec := false; (* turn printing back on *)

(* Set up the compset for computeLib.EVAL
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
*)

(* Cause assumptions and tags to be printed *)
show_assums := true;
show_tags := true;



(* Various solvers *)
val CooperSimpSat = (SIMP_CONV (srw_ss()++COOPER_ss) [], "SIMP_CONV (srw_ss()++COOPER_ss)");
val OmegaSimpSat  = (SIMP_CONV (srw_ss()++OMEGA_ss) [],  "SIMP_CONV (srw_ss()++OMEGA_ss)");
val OmegaSat  = (OMEGA_CONV,  "OMEGA_CONV");

(*
val ilogSolv = elim_state_CONV(satSolv(extSolv "ILOG"));
*)
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


val absMinus_run_th1 = 
 SYM_RUN solv (EVAL_ASSUME ``(\s:state. T) s``) ``[^absMinus]``;
val absMinus_run_th1 = 
 SYM_RUN solv (EVAL_ASSUME ``(\s. ScalarOf (s ' "i") <  ScalarOf (s ' "j")) s``) ``[^absMinus]``;
val absMinus_run_th2 = 
 SYM_RUN solv (EVAL_ASSUME ``(\s. ScalarOf (s ' "j") <= ScalarOf (s ' "i")) s``) ``[^absMinus]``;

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

(*
fun VARS_IN_CONV t =
 let val th1 =  EVAL t
     val th2 = EQT_INTRO(prove(rhs(concl th1), REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]));
 in
  TRANS th1 th2
 end;

fun STRAIGHT_EVAL_SYM c =
let val l = MAKE_STATE_LIST c
    val STRAIGHT_th = EQT_ELIM(print "\nSTRAIGHT:     "; time EVAL ``STRAIGHT ^c``)
    val VARS_IN_th =  EQT_ELIM(print "VARS_IN:      "; time VARS_IN_CONV ``VARS_IN ^c ^l``)
    val DISTINCT_th = EQT_ELIM(print "DISTINCT:     "; time EVAL ``DISTINCT_VARS ^l``)
    val STRAIGHT_RUN_th = (print "STRAIGHT_RUN: "; time EVAL ``STRAIGHT_RUN ^c ^l``)
    val STRAIGHT_RUN_EVAL_th1 = SPECL [c,l] STRAIGHT_RUN_EVAL
    val STRAIGHT_RUN_EVAL_th2 = LIST_MP [STRAIGHT_th,VARS_IN_th,DISTINCT_th] STRAIGHT_RUN_EVAL_th1 
in
 CONV_RULE (RAND_CONV(RAND_CONV(REWR_CONV STRAIGHT_RUN_th))) STRAIGHT_RUN_EVAL_th2
end;
*)

val AbsMinusProg = 
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl AbsMinusTheory.MAIN_def))))));

val AbsMinus_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^AbsMinusProg ^(MAKE_STATE_LIST AbsMinusProg)``;

val AbsMinus_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM AbsMinusProg;

val TritypeProg = 
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl TritypeTheory.MAIN_def))))));

val Tritype_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^TritypeProg ^(MAKE_STATE_LIST TritypeProg)``;

val Tritype_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM TritypeProg;

val GeneratedFlasherManagerProg = 
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl GeneratedFlasherManagerTheory.MAIN_def))))));

val GeneratedFlasherManager_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^GeneratedFlasherManagerProg ^(MAKE_STATE_LIST GeneratedFlasherManagerProg)``;

val GeneratedFlasherManager_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM GeneratedFlasherManagerProg;

val F1Prog = 
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl F1Theory.MAIN_def))))));

val F1_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^F1Prog ^(MAKE_STATE_LIST F1Prog)``;

val F1_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM F1Prog;




