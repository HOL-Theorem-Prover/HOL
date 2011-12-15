(*---------------------------------------------------------------------------*)
(* Register machines                                                         *)
(*---------------------------------------------------------------------------*)

open HolKernel bossLib boolLib Parse
open finite_mapTheory arithmeticTheory pred_setTheory;

val _ = new_theory "reg"

(*---------------------------------------------------------------------------*)
(* Register machines have two instructions:                                  *)
(*                                                                           *)
(*   INC r j     -- increment register r and goto instruction j              *)
(*   TST r i j   -- if register r = 0 then goto instr. i else                *)
(*                  decrement r and goto j                                   *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype
  `instr = INC of num => num
         | TST of num => num => num`;

(*---------------------------------------------------------------------------*)
(* A machine configuration is the current state of the registers and the     *)
(* current instruction index. The final result of a computation will be held *)
(* in register 0.                                                            *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `config = <| pc : num; regs : num |-> num |>`
val _ = hide "config"

val saferead_def = Define`
  saferead f i = case FLOOKUP f i of NONE => 0 | SOME v => v
`;
val _ = set_fixity "''" (Infixl 2000)
val _ = overload_on ("''", ``saferead``)

val reg0_def = Define `reg0 config = config.regs '' 0`;

(*---------------------------------------------------------------------------*)
(* A step of computation is represented as a relation between configurations.*)
(* A configuration (Regs,i) holds the contents of the registers and the pc.  *)
(* A program is represented by a finite map from the pc to the instruction   *)
(* to be executed. If the pc is not in the domain of the program, no change  *)
(* is made to the configuration.                                             *)
(*---------------------------------------------------------------------------*)

val Step_def = Define `
  Step prog cfg =
     case FLOOKUP prog cfg.pc of
       NONE => cfg
     | SOME(INC r j) => cfg with <|
                              regs updated_by (\R. R |+ (r, R '' r + 1));
                              pc := j
                        |>
     | SOME(TST r a b) =>
           if cfg.regs '' r = 0 then cfg with pc := a
           else cfg with <| regs updated_by (\R. R |+ (r, R '' r - 1));
                            pc := b |>`;

(* ----------------------------------------------------------------------
    Translate a list into a finite map.
   ---------------------------------------------------------------------- *)

val fmapOf_def =
 Define
   `fmapOf list = FEMPTY |++ GENLIST (λn. (n, EL n list)) (LENGTH list)`

(*---------------------------------------------------------------------------*)
(* A sequence f is an execution of prog on inputs args starting at pc, just  *)
(* when the first element of f is the initial configuration of the machine,  *)
(* and each subsequent element follows by making a step of computation. An   *)
(* execution is finite just in case some configuration in it has a pc not in *)
(* the domain of prog. In that case, all subsequent configs are identical.   *)
(* This is distinguishable from  an infinite execution where all configs are *)
(* identical, since each config in the latter will have the pc in the domain *)
(* of prog.                                                                  *)
(*---------------------------------------------------------------------------*)

val isExecution_def =
 Define
  `isExecution prog pc args f =
     (f 0 = <| regs := fmapOf args; pc := pc|>) /\
     (!n. f (n+1) = Step prog (f n))`;

val Executions_Exist = store_thm(
  "Executions_Exist",
  ``!prog pc args. ?f. isExecution prog pc args f``,
 RW_TAC arith_ss [isExecution_def] THEN
 Q.EXISTS_TAC `\n. FUNPOW (Step prog) n <| regs := fmapOf args; pc := pc|>` THEN
 RW_TAC arith_ss [FUNPOW] THEN RW_TAC arith_ss [GSYM ADD1] THEN
 RW_TAC arith_ss [FUNPOW_SUC]);

val Executions_Unique = store_thm(
  "Executions_Unique",
  ``!prog pc args f1 f2.
     isExecution prog pc args f1 /\
     isExecution prog pc args f2 ==> (f1=f2)``,
 RW_TAC arith_ss [isExecution_def, FUN_EQ_THM] THEN
 Induct_on `x` THEN RW_TAC arith_ss [] THEN METIS_TAC [ADD1]);

(*---------------------------------------------------------------------------*)
(* Execution is deterministic, so we can talk of "the" execution of prog on  *)
(* args starting at pc:                                                      *)
(*                                                                           *)
(*   |- isExecution prog pc args (execOf prog pc args)                       *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val execOf_def =
 new_specification
  ("execOf_def",
   ["execOf"],
    SIMP_RULE std_ss [SKOLEM_THM] Executions_Exist);

(*---------------------------------------------------------------------------*)
(* val execOf_thm =                                                          *)
(*   |- !prog pc args.                                                       *)
(*       (execOf prog pc args 0 = (fmapOf args,pc)) /\                       *)
(*       !n. execOf prog pc args (SUC n) = Step prog (execOf prog pc args n) *)
(*---------------------------------------------------------------------------*)

val execOf_thm = save_thm(
  "execOf_thm",
  SIMP_RULE arith_ss [isExecution_def, GSYM ADD1] execOf_def);

val execOf_recn = store_thm(
  "execOf_recn",
  ``execOf prog pc args n =
      if n=0 then <| regs := fmapOf args; pc := pc|>
      else Step prog (execOf prog pc args (n-1))``,
  Cases_on `n` THEN RW_TAC arith_ss [execOf_thm]);

val _ = computeLib.add_funs [execOf_recn,FLOOKUP_DEF];

(*---------------------------------------------------------------------------*)
(* The index of the first terminated configuration in a sequence.            *)
(*---------------------------------------------------------------------------*)

val haltedConfig_def = Define `
   haltedConfig prog cnfg = cnfg.pc ∉ FDOM prog
`

val haltsAt_def =
 Define
  `haltsAt (prog:num |-> instr) (seq:num -> config) =
    if (?n. haltedConfig prog (seq n))
     then SOME (LEAST n. haltedConfig prog (seq n))
      else NONE`;

val haltsSuffix = store_thm(
  "haltsSuffix",
  ``!prog pc args seq m.
       isExecution prog pc args seq /\
       haltedConfig prog (seq m) ==>
       !q. m <= q ==> haltedConfig prog (seq q)``,
  SRW_TAC [][haltedConfig_def,isExecution_def,GSYM ADD1] THEN
  `?k. q = m + k` by METIS_TAC [LESS_EQUAL_ADD] THEN
  SRW_TAC [][] THEN POP_ASSUM (K ALL_TAC) THEN
  Induct_on `k` THEN SRW_TAC [][ADD_CLAUSES] THEN
  Q.SPEC_THEN `seq (m + k)` FULL_STRUCT_CASES_TAC
              (theorem "config_literal_nchotomy") THEN
  SRW_TAC [][Step_def,FLOOKUP_DEF] THEN FULL_SIMP_TAC (srw_ss()) []);

val haltsSuffixThm = store_thm(
  "haltsSuffixThm",
  ``!prog pc args m q.
      haltedConfig prog (execOf prog pc args m) /\  m <= q ==>
      haltedConfig prog (execOf prog pc args q)``,
  METIS_TAC [execOf_def,haltsSuffix]);

val Halts_def =
 Define
  `Halts prog pc args = ?n. haltsAt prog (execOf prog pc args) = SOME n`;

(*---------------------------------------------------------------------------*)
(* The function computed by program prog is given by funOf prog.             *)
(*---------------------------------------------------------------------------*)

val funOf_def =
 Define
  `funOf prog args =
     let seq = execOf prog 1 args
     in case haltsAt prog seq of
          SOME m => SOME (reg0 (seq m))
        | NONE => NONE`;

(*---------------------------------------------------------------------------*)
(* Accept/reject inputs.                                                     *)
(*---------------------------------------------------------------------------*)

val Accepts_def =
 Define
  `Accepts prog pc args =
     ?m. (haltsAt prog (execOf prog pc args) = SOME m) /\
         (reg0(execOf prog pc args m) = 1)`;

val Rejects_def =
 Define
  `Rejects prog pc args =
     ?m. (haltsAt prog (execOf prog pc args) = SOME m) /\
         (reg0(execOf prog pc args m) = 0)`;

(*---------------------------------------------------------------------------*)
(* The set of computable functions. Needs a notion of arity of the function. *)
(*---------------------------------------------------------------------------*)

val nComputable_def =
 Define
  `nComputable n (f:num list -> num option) =
      ?prog. !args. (LENGTH args = n) ==> (f args = funOf prog args)`;

val Computable_def =
 Define
  `Computable = BIGUNION {nComputable n | n IN UNIV}`;

val IN_Computable = Q.prove
(`f IN Computable =
   ?n prog. !args. (LENGTH args = n) ==> (f args = funOf prog args)`,
 SRW_TAC [] [IN_BIGUNION, Computable_def,EQ_IMP_THM,nComputable_def] THEN
 METIS_TAC [nComputable_def, SPECIFICATION]);


(*---------------------------------------------------------------------------*)
(* While instruction 0 is not entered, make a Step, thereby updating the     *)
(* registers and the next instruction. By convention, programs start at      *)
(* pc 1.                                                                     *)
(*---------------------------------------------------------------------------*)

val Run_def =
 Define
  `Run prog args n = FUNPOW (Step prog) n <| regs := fmapOf args; pc := 1|>`;

(*---------------------------------------------------------------------------*)
(* Example Register program executions.                                      *)
(*---------------------------------------------------------------------------*)

(*
(* Halt immediately *)
val prog1 = ``FEMPTY |++ [(1,TST 0 0 0)]``;

(* Add R0 and R1, leaving result in R0 and trashing R1 *)
val prog2 = ``FEMPTY |++ [(1,TST 1 0 2); (2, INC 0 1)]``;

EVAL ``reg0(Run ^prog1 [0;1;2] 1)``;
EVAL ``reg0(Run ^prog2 [3;4] 8)``;
EVAL ``reg0(Run ^prog2 [3;19] 40)``;
Count.apply EVAL ``reg0(Run ^prog2 [19;52] 400)``;
*)

val _ = export_theory();
