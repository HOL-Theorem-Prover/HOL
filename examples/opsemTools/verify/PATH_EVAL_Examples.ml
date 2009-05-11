(*
This is a collection of test examples and experiments used by Mike. It is not
intended to be used by anyone else. It should load into an interactive
session with the ML function "use".
*)


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
val OmegaSat      = (OMEGA_CONV,  "OMEGA_CONV");

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


val absMinus_run_th = 
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

val AbsMinusHOL_th2 =  
 time prove
  (rhs(concl(AbsMinusTheory.MAIN_def)),
   SIMP_TAC std_ss [RSPEC_SP]
    THEN CONV_TAC EVAL
    THEN RW_TAC arith_ss[]
    THEN CONV_TAC EVAL
    THEN OMEGA_TAC
    THEN RW_TAC arith_ss[]);

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
val TritypeHOL_th2 =  
 time prove
  (rhs(concl(TritypeTheory.MAIN_def)),
   SIMP_TAC std_ss [RSPEC_SP]
    THEN CONV_TAC EVAL
    THEN RW_TAC arith_ss[]
    THEN CONV_TAC EVAL
    THEN OMEGA_TAC
    THEN RW_TAC arith_ss[]);
*)

(*
val TritypeILOG_th =  
 time prove
  (rhs(concl(TritypeTheory.MAIN_def)),
   REWRITE_TAC[IMP_INTRO_THM]
    THEN REPEAT CONJ_TAC
    THEN IMP_EVAL_TAC ilogSolv
    THEN CONV_TAC(EVAL THENC elim_state_CONV COOPER_CONV));
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

(*
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
*)

load "ArraySwapElementTheory";

(* 
 {i>0 /\ i<aLength /\ j>0 /\ j < aLength}
 tmp := a[i]; a[i] := a[j]; a[j] := tmp 
 {(a[i_] = a_[j_]) /\ (a[j_] = a_[i_]}
*)
val ArraySwapElementProg =
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl ArraySwapElementTheory.MAIN_def))))));

val ArraySwapElement_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^ArraySwapElementProg ^(MAKE_STATE_LIST ArraySwapElementProg)``;

val ArraySwapElement_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM ArraySwapElementProg;

(*
SIMP_RULE std_ss [ArraySwapElement_STRAIGHT_RUN_EVAL,RSPEC_def] ArraySwapElementTheory.MAIN_def
*)

load "PartitionTheory";

val PartitionProg =
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl PartitionTheory.MAIN_def))))));

(*
val Partition_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^PartitionProg ^(MAKE_STATE_LIST PartitionProg)``;

val Partition_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM PartitionProg;
*)

load "SelectionSortTheory";

val SelectionSortProg =
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl SelectionSortTheory.MAIN_def))))));

(*
val SelectionSort_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^SelectionSortProg ^(MAKE_STATE_LIST SelectionSortProg)``;

val SelectionSort_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM SelectionSortProg;
*)

load "BsearchTheory";

val BsearchProg =
 el 2 (snd(strip_comb(el 2 (snd(strip_comb(concl BsearchTheory.MAIN_def))))));

(*
val Bsearch_STRAIGHT_RUN = 
 time EVAL ``STRAIGHT_RUN ^BsearchProg ^(MAKE_STATE_LIST BsearchProg)``;

val Bsearch_STRAIGHT_RUN_EVAL = 
  time STRAIGHT_EVAL_SYM BsearchProg;
*)

load "opsem_translatorLib";
open  opsem_translatorLib;

val (th,ArraySwapElement_def) = 
 time (DERIVE_SEP_TOTAL_SPEC "ArraySwapElement") ArraySwapElementProg;

val (th,Partition_def) = 
 time (DERIVE_SEP_TOTAL_SPEC "Partition") PartitionProg;

val (th,SelectionSort_def) = 
 time (DERIVE_SEP_TOTAL_SPEC "SelectionSort") SelectionSortProg;

val (th,Bsearch_def) = 
 time (DERIVE_SEP_TOTAL_SPEC "Bsearch") BsearchProg;

(*

ArraySwapElement, Partition, SelectionSort, Bsearch

i := 0; 
j := 0; 
indMin := 0; 
aux := 0;
WHILE i < aLength DO
 (indMin := i; 
  j := i+1;
  WHILE j < aLength DO (if a[j] < a[indMin] then indMin := j else SKIP);
  aux := a[i];
  a[i] := a[indMin];
  a[indMin] := aux
  i := i+1)

let i = 0 in
let j = 0 in
let indMin = 0 in
let aux = 0 in
 SelectionSort1 (aLength,aux,i,indMin,j,a)

SelectionSort (aLength,aux,i,indMin,j,a) =
 SelectionSort1 (aLength,0,0,0,0,a)

SelectionSort1 (aLength,aux,i,indMin,j,a) =
 if j < aLength
  then let (aLength',indMin',j',a') = SelectionSort2 (aLength,i,i+1,a)
       in (aLength',i',indMin',j',a')
  else (aLength,aux,i,indMin,j,a)

SelectionSort2 (aLength,aux,i,indMin,j,a) =
 if 


(SelectionSort (aLength,aux,i,indMin,j,a) = (aLength',aux',i',indMin',j',a'))
==> !i. i >= 0 /\ i < aLength-1 ==> a' ' i <= a' ' (i+1)

*)

(* 
Code to multiply "m" and "n" and return result in "Result".
Would like to prove:

 |- EVAL_FUN MultProg s = 
      s |+ ("Result", Scalar(ScalarOf(s ' "m") * ScalarOf(s ' "n")))))
*)
val MultProg_def =
 Define
  `MultProg =
    Locals ["result"; "count"]
     ("result" ::= C 0;;
      "count"  ::= C 0;;
      While (V"count" < V"m")
       ("result" ::= V"result" + V"n" ;;
        "count" ::= V"count" + C 1)   ;;
      "Result" ::= V"result")`;

(* Procedure using MultProc *)
val MultProc_def = 
 Define
 `MultProc m n res =
    Locals ["m";"n"] 
     ("m" ::= V m;; 
      "n" ::= V n;; 
      Proc (THE o EVAL_FUN MultProg);;
      res ::= V"Result")`;;

(* 
Proc defined directly. Would like to prove:
 |- MultFunProc m n res = MultProc m n res
*)
val MultFunProc_def = 
 Define
 `MultFunProc m n res =
   Proc (\s. s |+ (res, Scalar(ScalarOf(s ' m) * ScalarOf(s ' n))))`;

(* Factorial on n using primitive multiplication *)
val FactProg1_def =
 Define
  `FactProg1 =
    Locals ["result"; "count"]
     ("result" ::= C 1;;
      "count"  ::= C 1;;
      While (V"count" <= V"n")
       ("result" ::= V"result" * V"count" ;;
        "count" ::= V"count" + C 1)   ;;
      "Result" ::= V"result")`;

(* Factorial using MultProc for multiplication *)
val FactProg2_def =
 Define
  `FactProg2 =
    Locals ["result"; "count"]
     ("result" ::= C 1;;
      "count"  ::= C 1;;
      While (V"count" <= V"n")
       (MultProc "result" "count" "result" ;;
        "count" ::= V"count" + C 1)   ;;
      "Result" ::= V"result")`;

(* Factorial using MultFunProc for multiplication *)
val FactProg3_def =
 Define
  `FactProg3 =
    Locals ["result"; "count"]
     ("result" ::= C 1;;
      "count"  ::= C 1;;
      While (V"count" <= V"n")
       (MultFunProc "result" "count" "result" ;;
        "count" ::= V"count" + C 1)   ;;
      "Result" ::= V"result")`;

(* Test examples *)

val EVAL_FactProg1_4 = time EVAL ``EVAL_FUN FactProg1 (FEMPTY |+ ("n",Scalar 4))``;
val EVAL_FactProg1_6 = time EVAL ``EVAL_FUN FactProg1 (FEMPTY |+ ("n",Scalar 6))``;

val EVAL_FactProg2_4 = time EVAL ``EVAL_FUN FactProg2 (FEMPTY |+ ("n",Scalar 4))``;
val EVAL_FactProg2_6 = time EVAL ``EVAL_FUN FactProg2 (FEMPTY |+ ("n",Scalar 6))``;

val EVAL_FactProg3_4 = time EVAL ``EVAL_FUN FactProg3 (FEMPTY |+ ("n",Scalar 4))``;
val EVAL_FactProg3_6 = time EVAL ``EVAL_FUN FactProg3 (FEMPTY |+ ("n",Scalar 6))``;


val EVAL_CONT_FactProg1_4 = time EVAL ``EVAL_CONT FactProg1 cont (FEMPTY |+ ("n",Scalar 4))``;
val EVAL_CONT_FactProg1_6 = time EVAL ``EVAL_CONT FactProg1 cont (FEMPTY |+ ("n",Scalar 6))``;

val EVAL_CONT_FactProg2_4 = time EVAL ``EVAL_CONT FactProg2 cont (FEMPTY |+ ("n",Scalar 4))``;
val EVAL_CONT_FactProg2_6 = time EVAL ``EVAL_CONT FactProg2 cont (FEMPTY |+ ("n",Scalar 6))``;

val EVAL_CONT_FactProg3_4 = time EVAL ``EVAL_CONT FactProg3 cont (FEMPTY |+ ("n",Scalar 4))``;
val EVAL_CONT_FactProg3_6 = time EVAL ``EVAL_CONT FactProg3 cont (FEMPTY |+ ("n",Scalar 6))``;

val th1 = EVAL ``SP (\s. ScalarOf (s ' "i") <  ScalarOf (s ' "j")) ^absMinus s ==> Q s``;

val th1 = EVAL ``SP (\s. (ScalarOf (s ' "i") = 0)  /\ (ScalarOf (s ' "j") = 1)) ^absMinus s ==> Q s``;

val th1a = EVAL ``SP (\s. (s = s0) /\ ScalarOf (s0 ' "i") <  ScalarOf (s0 ' "j")) ^absMinus``;

val th1a = 
 SIMP_CONV arith_ss
  [ASSIGN_SP_EX,IF_SP_EX,SEQ_SP]
  ``SP (\s. (s = s0) /\ ScalarOf (s0 ' "i") <  ScalarOf (s0 ' "j")) ^absMinus``;

val th1b = EVAL ``SP (\s. (s = s0) /\ ScalarOf (s0 ' "i") <  ScalarOf (s0 ' "j")) ^absMinus s``;

val th1c = EVAL ``SP (\s. (s = s0) /\ ScalarOf (s0 ' "i") <  ScalarOf (s0 ' "j")) ^absMinus s ==> Q s``;

val th1d = EVAL ``SP (\s. (s =  FEMPTY |+ ("i",Scalar i) |+("j",Scalar j)) /\ i < j) ^absMinus s ==> Q(s ' "i", s ' "j", s ' "k")``;

val th2 = EVAL ``SP (\s. ScalarOf (s ' "i") < ScalarOf (s ' "j")) ("j" ::= V"j"+C 1) s``;

val th2a = EVAL ``SP (\s. ScalarOf (s ' "i") < ScalarOf (s ' "j")) (("j" ::= V"j"+C 1) ;; ("j" ::= V"j"+C 2)) s``;

val th2b = EVAL ``SP (\s. (ScalarOf (s ' "i")  = i) /\ (ScalarOf (s ' "j") = j) /\ i < j) (("j" ::= V"j"+C 1) ;; ("j" ::= V"j"+C 2)) s``;

val th2c = EVAL ``SP (\s. (ScalarOf (s ' "i")  = i) /\ (ScalarOf (s ' "j") = j) /\ (i=0) /\  (j=0)) (("j" ::= V"j"+C 1) ;; ("j" ::= V"j"+C 2))``;

val th2d = EVAL ``SP (\s. (s = FEMPTY |+ ("i",Scalar i) |+("j",Scalar j)) /\ (i=0) /\  (j=0)) (("j" ::= V"j"+C 1) ;; ("j" ::= V"j"+C 2))``;

val th2e = EVAL ``SP (\s. (s = FEMPTY |+ ("i",Scalar i) |+("j",Scalar j)) /\ i < j) (("j" ::= V"j"+C 1) ;; ("j" ::= V"j"+C 2))``;

val th2f = REWRITE_CONV [ASSIGN_SP_EX,SEQ_SP]
            ``SP (\s. (s = (\(i,j). FEMPTY |+ ("i",Scalar i) |+("j",Scalar j))(i,j)) /\ (\(i,j).i < j)(i,j)) (("j" ::= V"j"+C(1:int)) ;; ("j" ::= V"j"+C(2:int)))``;

val th2g = EVAL ``SP (\s. (s = s0) /\ ScalarOf(s0 ' "i") < ScalarOf(s0 ' "j")) (("j" ::= V"j"+C 1) ;; ("j" ::= V"j"+C 2) ;; ("i" ::= V"i" + V"j"))``;

(*
REWRITE_RULE
 [pairLib.GEN_BETA_RULE(ISPECL[``\(i,j). FEMPTY |+ ("i",Scalar i) |+ ("j",Scalar j)``,``((i:int),(j:int))``,``\((i:int),(j:int)). i<j``]ASSIGN_SP_EX)]
 th2f;

val th3 = EVAL ``ACC_PRED (\s. ScalarOf (s ' "i") < ScalarOf (s ' "j")) ("j" ::= V"j"+C 1) ^(MAKE_STATE absMinus)``;

val th3 = EVAL ``ACC_PRED (\s. ScalarOf (s ' "i") < ScalarOf (s ' "j")) ("j" ::= V"j"+C 1) 
                 (FEMPTY |++ [("k",Scalar k); ("result",Scalar result); ("i",Scalar i); ("j",Scalar j)])
                 (FEMPTY |++ [("k",Scalar k'); ("result",Scalar result'); ("i",Scalar i'); ("j",Scalar j')])``;
*)


(* Scratch:

val MKSPRED_def =
 Define
  `(MKSPRED [] s = T)
   /\
   (MKSPRED ((v,e) :: sl) s = (s ' v = e) /\ MKSPRED sl s)`;

*)



(*
Would like to prove:

 |- EVAL MultProg s1 s2 = 
     (s2 = (s1 |+ (res, Scalar(ScalarOf(s1 ' m) * ScalarOf(s1 ' n)))))

 |- EVAL_FUN MultProg s = 
     s |+ (res, Scalar(ScalarOf(s ' m) * ScalarOf(s ' n)))))
*)


