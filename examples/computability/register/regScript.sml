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
   haltedConfig (prog : num |-> instr) cnfg = cnfg.pc ∉ FDOM prog
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

val funOf_def = Define `
  funOf prog args =
     let seq = execOf prog 1 (0::args)
     in case haltsAt prog seq of
          SOME m => SOME (reg0 (seq m))
        | NONE => NONE
`;

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
  `Run prog args n =
     FUNPOW (Step prog) n <| regs := fmapOf (0::args); pc := 1|>`;

val whileRun_def = Define`
  whileRun prog args =
    WHILE (λc. ¬haltedConfig prog c) (Step prog)
          <| regs := fmapOf (0::args); pc := 1 |>
`

(*---------------------------------------------------------------------------*)
(* Example Register program executions.                                      *)
(*---------------------------------------------------------------------------*)

val predOf_def = Define`
  predOf P s <=> P s.pc (saferead s.regs)
`

val firstHaltsAt_def = Define`
  firstHaltsAt prog n s <=>
    haltedConfig prog (FUNPOW (Step prog) n s) ∧
    ∀m. m < n ⇒ ¬haltedConfig prog (FUNPOW (Step prog) m s)
`;

val HOARE_def = Define`
  HOARE P prog Q <=>
    ∀s0. predOf P s0 ⇒
         ∃n. firstHaltsAt prog n s0 ∧
             predOf Q (FUNPOW (Step prog) n s0)
`


val _ = temp_add_rule {fixity = Infix(NONASSOC, 450),
                       term_name = "HOARE",
                       block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [HardSpace 1, TOK (UTF8.chr 0x22A2),
                                      BreakSpace(1,2), TM, BreakSpace(1,0),
                                      TOK (UTF8.chr 0x22A3), HardSpace 1]}


val saferead_update = store_thm(
  "saferead_update",
  ``((fm |+ (k1,v)) '' k1 = v) ∧
    (k1 ≠ k2 ⇒ ((fm |+ (k1,v)) '' k2 = fm '' k2))``,
  SRW_TAC [][saferead_def, FLOOKUP_UPDATE]);

val _ = overload_on("RM*", ``λp n s. FUNPOW (Step p) n s``)
open lcsymtacs
val haltedConfig_suffix = store_thm(
  "haltedConfig_suffix",
  ``haltedConfig p (RM* p m s) ∧ m ≤ n ⇒ haltedConfig p (RM* p n s)``,
  Induct_on `n` >| [
    strip_tac >> `m = 0` by decide_tac >> fsrw_tac [][],
    Cases_on `m = SUC n` >- srw_tac [][] >>
    strip_tac >> `m ≤ n` by decide_tac >>
    srw_tac [][FUNPOW_SUC] >>
    `haltedConfig p (RM* p n s)` by METIS_TAC [] >>
    `(RM* p n s).pc ∉ FDOM p` by METIS_TAC [haltedConfig_def] >>
    srw_tac [][Step_def, FLOOKUP_DEF]
  ]);

val firstHaltsAt_prefix = store_thm(
  "firstHaltsAt_prefix",
  ``∀m n plus_mn s0.
       firstHaltsAt prog n (FUNPOW (Step prog) m s0) ∧
       ¬haltedConfig prog (FUNPOW (Step prog)m s0) ∧ (plus_mn = m + n) ⇒
       firstHaltsAt prog (plus_mn) s0``,
  SIMP_TAC (srw_ss()) [firstHaltsAt_def] THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [GSYM FUNPOW_ADD],
    Cases_on `m' ≤ m` >- METIS_TAC [haltedConfig_suffix] >>
    `m < m'` by decide_tac >>
    first_x_assum (qspec_then `m' - m` mp_tac) >>
    srw_tac [ARITH_ss][GSYM FUNPOW_ADD]
  ]);

val firstHaltsAt_ZERO = store_thm(
  "firstHaltsAt_ZERO",
  ``firstHaltsAt p 0 s ⇔ haltedConfig p s``,
  srw_tac [][firstHaltsAt_def]);
val _ = export_rewrites ["firstHaltsAt_ZERO"]


val firstHaltsAt_SUC = store_thm(
  "firstHaltsAt_SUC",
  ``firstHaltsAt p (SUC n) s ⇔
      firstHaltsAt p n (Step p s) ∧ ¬haltedConfig p s``,
  srw_tac [][firstHaltsAt_def, FUNPOW, EQ_IMP_THM] >| [
    first_x_assum (qspec_then `SUC m` mp_tac) >>
    srw_tac [][FUNPOW],
    first_x_assum (qspec_then `0` mp_tac) >> srw_tac [][],
    Cases_on `m = 0` >- srw_tac [][] >>
    `∃m₀. m = SUC m₀` by (Cases_on `m` >> srw_tac [][]) >>
    fsrw_tac [][FUNPOW]
  ]);

val firstHaltsAt_ADD = store_thm(
  "firstHaltsAt_ADD",
  ``0 < m ⇒ (firstHaltsAt p (m + n) s ⇔ firstHaltsAt p m (RM* p n s))``,
  srw_tac [][firstHaltsAt_def, EQ_IMP_THM, FUNPOW_ADD] >| [
    first_x_assum (qspec_then `m' + n` mp_tac) >>
    srw_tac [][FUNPOW_ADD],
    Cases_on `n ≤ m'` >-
      (first_x_assum (qspec_then `m' - n` mp_tac) >>
       srw_tac [ARITH_ss][GSYM FUNPOW_ADD]) >>
    first_x_assum (qspec_then `0` mp_tac) >>
    srw_tac [][] >>
    `m' ≤ n` by DECIDE_TAC >>
    metis_tac [haltedConfig_suffix]
  ]);

val unused_instructions = store_thm(
  "unused_instructions",
  ``∀n m s.
      firstHaltsAt prog₁ n s ∧ DISJOINT (FDOM prog₁) (FDOM prog₂) ∧ m ≤ n ⇒
      (RM* (FUNION prog₁ prog₂) m s = RM* prog₁ m s)``,
  Induct_on `n` >- srw_tac [][] >>
  srw_tac [][firstHaltsAt_SUC] >>
  `(m = 0) ∨ ∃m₀. m = SUC m₀` by (Cases_on `m` >> srw_tac [][])
     >- srw_tac [][] >>
  `m₀ ≤ n` by fsrw_tac [][] >>
  `s.pc ∈ FDOM prog₁` by fsrw_tac [][haltedConfig_def] >>
  `s.pc ∉ FDOM prog₂`
    by (fsrw_tac [][DISJOINT_DEF, EXTENSION] >> metis_tac []) >>
  srw_tac [][FUNPOW] >>
  `Step (FUNION prog₁ prog₂) s = Step prog₁ s`
    by srw_tac [][Step_def, FLOOKUP_DEF, FUNION_DEF] >>
  srw_tac [][]);

val haltedConfig_bigger_prog = store_thm(
  "haltedConfig_bigger_prog",
  ``haltedConfig (FUNION p₁ p₂) s ⇒ haltedConfig p₁ s``,
  srw_tac [][haltedConfig_def, FUNION_DEF]);

val predOf_AND_def = Define`
  predOf_AND p q pc rf ⇔ p pc rf ∧ q pc rf
`;

val _ = set_fixity "&&" (Infixr 400)
val _ = overload_on("&&", ``predOf_AND``)

val PCNOTIN_def = Define`
  PCNOTIN s pc rf ⇔ pc ∉ s
`
val _ = overload_on("PC∉", ``PCNOTIN``)

val predOf_AND_thm = store_thm(
  "predOf_AND_thm",
  ``predOf (P && Q) s ⇔ predOf P s ∧ predOf Q s``,
  srw_tac [][predOf_AND_def, predOf_def])

val predOf_PCNOTIN = store_thm(
  "predOf_PCNOTIN",
  ``predOf (PC∉ s) c ⇔ c.pc ∉ s``,
  srw_tac [][PCNOTIN_def, predOf_def]);

val HOARE_sequence = store_thm(
  "HOARE_sequence",
  ``HOARE P prog1 R ∧ HOARE R prog2 (Q && PC∉ (FDOM prog1)) ∧
    DISJOINT (FDOM prog1) (FDOM prog2) ⇒
    HOARE P (FUNION prog1 prog2) Q``,
  SRW_TAC [][HOARE_def] THEN
  `∃n₁. firstHaltsAt prog1 n₁ s0 ∧ predOf R (RM* prog1 n₁ s0)`
    by METIS_TAC [] THEN
  Q.ABBREV_TAC `s1 = RM* prog1 n₁ s0` THEN
  `∃n₂. firstHaltsAt prog2 n₂ s1 ∧
        predOf (Q && PC∉(FDOM prog1)) (RM* prog2 n₂ s1)`
    by METIS_TAC [] THEN
  Q.EXISTS_TAC `n₂ + n₁` THEN ASM_SIMP_TAC (srw_ss()) [FUNPOW_ADD] THEN
  `∀m. m ≤ n₁ ⇒ (RM* (FUNION prog1 prog2) m s0 = RM* prog1 m s0)`
    by metis_tac[unused_instructions] >>
  asm_simp_tac (srw_ss()) [] >>
  Cases_on `n₂ = 0` >-
    (fsrw_tac [][firstHaltsAt_def, predOf_AND_thm] >> conj_tac >-
       fsrw_tac [][haltedConfig_def, FUNION_DEF] >>
     srw_tac [ARITH_ss][] >> metis_tac [haltedConfig_bigger_prog]) >>
  `0 < n₂` by decide_tac >>
  asm_simp_tac (srw_ss()) [firstHaltsAt_ADD] >>
  `FUNION prog1 prog2 = FUNION prog2 prog1`
     by metis_tac [FUNION_COMM] >>
  pop_assum SUBST_ALL_TAC >>
  `∀m. m ≤ n₂ ⇒ (RM* (FUNION prog2 prog1) m s1 = RM* prog2 m s1)`
     by metis_tac [DISJOINT_SYM, unused_instructions] >>
  REVERSE conj_tac >- fsrw_tac [][predOf_AND_thm] >>
  fsrw_tac [][firstHaltsAt_def] >> conj_tac >-
    fsrw_tac [][haltedConfig_def, predOf_PCNOTIN, predOf_AND_thm,
                FUNION_DEF] >>
  srw_tac [ARITH_ss][] >> metis_tac [haltedConfig_bigger_prog]);

val RPWhile_def = Define`
  RPWhile reg bi ei pbi p =
    FUNION (FEMPTY |+ (bi, TST reg ei pbi)) p
`

val IN_FDOM_RPWhile = store_thm(
  "IN_FDOM_RPWhile",
  ``x ∈ FDOM (RPWhile reg bi ei pbi p) ⇔ (x = bi) ∨ x ∈ FDOM p``,
  srw_tac [][RPWhile_def, FUNION_DEF]);
val _ = export_rewrites ["IN_FDOM_RPWhile"]

val rP_def = Define`
  rP r P pc reg = P (reg r)
`;

val rP_thm = store_thm(
  "rP_thm",
  ``predOf (rP r P) s ⇔ P (s.regs '' r)``,
  srw_tac [][predOf_def, rP_def]);
val _ = augment_srw_ss [rewrites [rP_thm]]

val PCeq_def = Define`
  PCeq n pc reg = (pc = n)
`;

val PCeq_thm = store_thm(
  "PCeq_thm",
  ``predOf (PCeq c) s ⇔ (s.pc = c)``,
  srw_tac [][predOf_def, PCeq_def]);
val _ = augment_srw_ss  [rewrites [PCeq_thm]]

val PCsub_def = Define`
  PCsub P v pc reg = P v reg
`

val PCsub_AND = store_thm(
  "PCsub_AND",
  ``PCsub (P && Q) v = PCsub P v && PCsub Q v``,
  srw_tac [][FUN_EQ_THM, PCsub_def, predOf_AND_def]);
val _ = augment_srw_ss [rewrites [PCsub_AND]]

val PCsub_PCsub = store_thm(
  "PCsub_PCsub",
  ``PCsub (PCsub P v1) v2 = PCsub P v1``,
  srw_tac [][FUN_EQ_THM, PCsub_def]);
val _ = augment_srw_ss [rewrites [PCsub_PCsub]]

val PCsub_rP = store_thm(
  "PCsub_rP",
  ``PCsub (rP r P) v = rP r P``,
  srw_tac [][PCsub_def, rP_def, FUN_EQ_THM]);
val _ = augment_srw_ss [rewrites [PCsub_rP]]

val PCsub_K = store_thm(
  "PCsub_K",
  ``PCsub (K P) v = K P``,
  srw_tac [][PCsub_def, FUN_EQ_THM]);
val _ = augment_srw_ss [rewrites [PCsub_K]]

val PCsub_PCeq = store_thm(
  "PCsub_PCeq",
  ``PCsub (PCeq v1) v2 = K (K (v2 = v1))``,
  srw_tac [][PCsub_def, PCeq_def, FUN_EQ_THM]);
val _ = augment_srw_ss [rewrites [PCsub_PCeq]]

val PCsub_PCNOTIN = store_thm(
  "PCsub_PCNOTIN",
  ``PCsub (PC∉ s) v = K (K (v ∉ s))``,
  srw_tac [][PCsub_def, PCNOTIN_def, FUN_EQ_THM]);
val _ = augment_srw_ss [rewrites [PCsub_PCNOTIN]]

val PCsub_ABS = store_thm(
  "PCsub_ABS",
  ``PCsub (λp:num. f p) v = (λp:num. f v)``,
  srw_tac [][PCsub_def, FUN_EQ_THM]);
val _ = augment_srw_ss [rewrites [PCsub_ABS]]

val REGfRsub_def = Define`
  REGfRsub P r f pc reg = P pc ((r =+ f reg) reg)
`

val REGfRsub_ABS = store_thm(
  "REGfRsub_ABS",
  ``REGfRsub (λp r. f1 p r) rg f = (λp r. f1 p ((rg =+ f r) r))``,
  srw_tac [][FUN_EQ_THM, REGfRsub_def]);

val REGfRsub_AND = store_thm(
  "REGfRsub_AND",
  ``REGfRsub (P && Q) r f = REGfRsub P r f && REGfRsub Q r f``,
  srw_tac [][predOf_AND_def, REGfRsub_def, FUN_EQ_THM]);
val _ = augment_srw_ss [rewrites [REGfRsub_AND]]

val REGfRsub_PCsub = store_thm(
  "REGfRsub_PCsub",
  ``REGfRsub (PCsub P v) r f = PCsub (REGfRsub P r f) v``,
  srw_tac [][REGfRsub_def, PCsub_def, FUN_EQ_THM])
val _ = augment_srw_ss [rewrites [SYM REGfRsub_PCsub]]

val REGfRsub_rP1 = store_thm(
  "REGfRsub_rP1",
  ``REGfRsub (rP r P) r f = K (P o f)``,
  srw_tac [][FUN_EQ_THM, REGfRsub_def, rP_def,
             combinTheory.APPLY_UPDATE_THM]);

val REGfRsub_rP2 = store_thm(
  "REGfRsub_rP2",
  ``r1 ≠ r2 ⇒ (REGfRsub (rP r1 P) r2 f = rP r1 P)``,
  srw_tac [][FUN_EQ_THM, REGfRsub_def, rP_def,
             combinTheory.APPLY_UPDATE_THM]);
val _ = augment_srw_ss [rewrites [REGfRsub_rP1, REGfRsub_rP2]]

val REGfRsub_PCeq = store_thm(
  "REGfRsub_PCeq",
  ``REGfRsub (PCeq v) r f = PCeq v``,
  srw_tac [][FUN_EQ_THM, PCeq_def, REGfRsub_def]);
val _ = augment_srw_ss [rewrites [REGfRsub_PCeq]]

val REGfRsub_PCNOTIN = store_thm(
  "REGfRsub_PCNOTIN",
  ``REGfRsub (PC∉ s) r f = PC∉ s``,
  srw_tac [][REGfRsub_def, PCNOTIN_def, FUN_EQ_THM]);
val _ = augment_srw_ss [rewrites [REGfRsub_PCNOTIN]]

val RPWhile_rule = store_thm(
  "RPWhile_rule",
  ``ei ≠ bi ∧ bi ∉ FDOM p ∧ ei ∉ FDOM p ∧
    (∀n. HOARE (rP reg ($= n) && REGfRsub (PCsub Inv ei) reg (λr. r reg + 1)  &&
                PCeq pbi)
               p
               (rP reg (λx. x <= n) && PCsub Inv ei && PCeq bi)) ==>
    HOARE (PCsub Inv ei && PCeq bi)
              (RPWhile reg bi ei pbi p)
          (Inv && rP reg ($= 0) && PCeq ei)``,
  srw_tac [][HOARE_def] >>
  pop_assum mp_tac >> qabbrev_tac `v = s0.regs '' reg` >>
  pop_assum (mp_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  map_every qid_spec_tac [`s0`, `v`] >>
  completeInduct_on `v` >> fsrw_tac [][GSYM RIGHT_FORALL_IMP_THM] >>
  srw_tac [][] >>
  pop_assum (mp_tac o
             SIMP_RULE (srw_ss()) [predOf_def, predOf_AND_thm, PCeq_def,
                                   PCsub_def]) >>
  qabbrev_tac `N = s0.regs '' reg` >>
  Cases_on `N = 0` >-
    (strip_tac >> qexists_tac `1` >>
     `Step (RPWhile reg bi ei pbi p) s0 = s0 with pc := ei`
        by srw_tac [][RPWhile_def, Step_def, FLOOKUP_UPDATE,
                      FLOOKUP_FUNION] >>
     asm_simp_tac (srw_ss()) [RPWhile_def, firstHaltsAt_def, predOf_def,
                              predOf_AND_thm, DECIDE ``m < 1 ⇔ (m = 0)``,
                              PCeq_def, rP_def, haltedConfig_def,
                              FUNION_DEF]) >>
  strip_tac >>
  qabbrev_tac
    `s1 = s0 with <| pc := pbi; regs := s0.regs |+ (reg, N - 1) |>` >>
  `Step (RPWhile reg bi ei pbi p) s0 = s1`
     by (srw_tac [][RPWhile_def, Step_def, FLOOKUP_UPDATE, FLOOKUP_FUNION,
                    Abbr`s1`] >>
         srw_tac [][theorem "config_component_equality"]) >>
  first_x_assum
    (qspecl_then [`N - 1`, `s1`]
                 (mp_tac o SIMP_RULE (srw_ss())
                                     [predOf_def, predOf_AND_thm, rP_def,
                                      PCsub_def, PCeq_def, REGfRsub_def])) >>
  `(s1.pc = pbi) ∧ (s1.regs = s0.regs |+ (reg,N-1))`
     by srw_tac [][Abbr`s1`] >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [saferead_update]>>
  qmatch_abbrev_tac `(Inv ei f ==> Q) ==> R` >>
  `f = (saferead s0.regs)`
     by (srw_tac [][Abbr`f`, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM,
                    saferead_update] >> srw_tac [][] >> srw_tac [][]) >>
  pop_assum SUBST1_TAC >> asm_simp_tac (srw_ss()) [] >>
  map_every qunabbrev_tac [`Q`, `R`] >>
  disch_then (Q.X_CHOOSE_THEN `c` strip_assume_tac) >>
  qabbrev_tac `s2 = RM* p c s1` >>
  `RM* (RPWhile reg bi ei pbi p) c s1 = s2`
     by (srw_tac [][RPWhile_def, Abbr`s2`] >>
         qmatch_abbrev_tac `RM* (FUNION gp p) c s1 = RM* p c s1` >>
         `DISJOINT (FDOM gp) (FDOM p)`
            by srw_tac [][Abbr`gp`, DISJOINT_DEF, EXTENSION] >>
         srw_tac [][Once FUNION_COMM] >>
         match_mp_tac unused_instructions >>
         metis_tac [DECIDE ``x ≤ x``, DISJOINT_SYM]) >>
  first_x_assum (qspec_then `s2` mp_tac) >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  `predOf (PCsub Inv ei && PCeq bi) s2`
     by srw_tac [][PCsub_def, PCeq_def, predOf_AND_thm, predOf_def] >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (Q.X_CHOOSE_THEN `M` STRIP_ASSUME_TAC) >>
  qexists_tac `SUC (M + c)` >>
  asm_simp_tac (srw_ss()) [firstHaltsAt_SUC, haltedConfig_def] >>
  asm_simp_tac (srw_ss()) [FUNPOW] >>
  Cases_on `M = 0` >- fsrw_tac [][haltedConfig_def] >>
  `0 < M` by decide_tac >>
  asm_simp_tac (srw_ss()) [FUNPOW_ADD, firstHaltsAt_ADD]);


(*
(* Halt immediately *)
val prog1 = ``FEMPTY |++ [(1,TST 0 0 0)]``;

(* Add R1 and R2, putting result in R0 and trashing R1 *)
val prog2 = ``FUNION (RPmove 1 0 1 3) (RPmove 2 0 3 0)``

EVAL ``reg0(Run ^prog1 [0;1;2] 1)``;
EVAL ``reg0(Run ^prog2 [3;4] 8)``;
EVAL ``reg0(Run ^prog2 [3;19] 40)``;
Count.apply EVAL ``reg0(Run ^prog2 [19;52] 400)``;

Count.apply EVAL ``reg0 (whileRun ^prog2 [19;52])``;

val zero_nb1 = prove(
  ``~(0 = NUMERAL (BIT1 n))``,
  REWRITE_TAC [NUMERAL_DEF, BIT1, ADD_CLAUSES, SUC_NOT]);
val nb12 = prove(
  ``NUMERAL (BIT1 n) <> NUMERAL (BIT2 m)``,
  REWRITE_TAC [NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES, SUC_NOT,
               prim_recTheory.INV_SUC_EQ] THEN
  DISCH_THEN (MP_TAC o AP_TERM ``EVEN``) THEN
  SRW_TAC [][EVEN_ADD, EVEN]);

val keycollapse1 = prove(
  ``fm |+ (0, v1) |+ (NUMERAL (BIT1 n), v2) |+ (0, v3) =
    fm |+ (0, v3) |+ (NUMERAL (BIT1 n), v2)``,
  SRW_TAC [][fmap_EXT, EXTENSION, FAPPLY_FUPDATE_THM, zero_nb1] THEN1
    PROVE_TAC [] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [zero_nb1]);

val keycollapse2 = prove(
  ``fm |+ (NUMERAL (BIT1 n), v1) |+ (NUMERAL (BIT2 m), v2)
       |+ (NUMERAL (BIT1 n), v3) =
    fm |+ (NUMERAL (BIT1 n), v3) |+ (NUMERAL (BIT2 m), v2)``,
  SRW_TAC [][fmap_EXT, EXTENSION, FAPPLY_FUPDATE_THM, nb12] THEN1
    PROVE_TAC [] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [nb12]);

SIMP_CONV (srw_ss()) [Run_def, FUNION_DEF, numeralTheory.numeral_funpow, Step_def, FLOOKUP_FUNION, RPmove_def, FLOOKUP_UPDATE, fmapOf_def, saferead_def, FUPDATE_LIST_THM, keycollapse1, keycollapse2] ``Run ^prog2 [19;52] 41``

*)

val RPimp_def = Define`
  RPimp P Q pc reg ⇔ (P pc reg ⇒ Q pc reg)
`

val _ = set_mapped_fixity {tok = "=R=>", fixity = Infixr 200,
                           term_name = "RPimp"}

val RPimp_thm = store_thm(
  "RPimp_thm",
  ``predOf (P =R=> Q) s ⇔ (predOf P s ==> predOf Q s)``,
  srw_tac [][RPimp_def, predOf_def])

val _ = overload_on ("TT", ``K (K T) : num -> (num -> num) -> bool``)
val RPimp_rwt = store_thm(
  "RPimp_rwt",
  ``(P =R=> P) = TT``,
  srw_tac [][FUN_EQ_THM, RPimp_def]);
val predOf_KK = store_thm(
  "predOf_KK",
  ``predOf (K (K v)) s = v``,
  srw_tac [][predOf_def]);
val REGfRsub_KK = store_thm(
  "REGfRsub_KK",
  ``REGfRsub (K (K v)) r f = K (K v)``,
  srw_tac [][REGfRsub_def, FUN_EQ_THM]);
val pAND_rwt = store_thm(
  "pAND_rwt",
  ``(TT && P = P) ∧ (P && TT = P)``,
  srw_tac [][FUN_EQ_THM, predOf_AND_def]);
val _ = augment_srw_ss [rewrites [RPimp_rwt, predOf_KK, REGfRsub_KK, pAND_rwt]]


val prepost_munge = store_thm(
  "prepost_munge",
  ``∀P Q P' Q'.
       HOARE P' c Q' ∧
       (∀s. predOf (P =R=> P') s) ∧ (∀s. predOf (Q' =R=> Q) s) ⇒
       HOARE P c Q``,
  srw_tac [][HOARE_def, RPimp_def, predOf_def] >> metis_tac []);

(* adjust while rule to have generic conclusion *)
val RPWhile = save_thm(
  "RPWhile",
  RPWhile_rule |> UNDISCH
               |> MATCH_MP (prepost_munge
                                |> REWRITE_RULE [Once (GSYM AND_IMP_INTRO)])
               |> SPEC_ALL |> DISCH_ALL
               |> REWRITE_RULE [AND_IMP_INTRO]
               |> (fn th => foldl (fn (v, th) => Q.GEN v th) th
                            [`pbi`, `ei`, `bi`, `p`, `reg`,
                             `Inv`, `Q`, `P`]))

val INC_correct = store_thm(
  "INC_correct",
  ``ei ≠ bi ∧
    (∀s. predOf (P =R=> PCeq bi &&
                 REGfRsub (PCsub Q ei) r (λR. R r + 1))
                s) ⇒
    P ⊢ FEMPTY |+ (bi, INC r ei) ⊣ Q``,
  srw_tac [][HOARE_def, predOf_def, PCeq_def, predOf_AND_def, RPimp_def,
             REGfRsub_def, PCsub_def] >>
  qexists_tac `1` >>
  res_tac >>
  srw_tac [][Step_def, firstHaltsAt_def, FLOOKUP_UPDATE, haltedConfig_def,
             DECIDE ``m < 1 ⇔ (m = 0)``] >>
  pop_assum mp_tac >>
  qmatch_abbrev_tac `Q ei f1 ⇒ Q ei f2` >>
  qsuff_tac `f1 = f2` >> srw_tac [][] >>
  srw_tac [][Abbr`f2`, Abbr`f1`, saferead_update,
             combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] >>
  srw_tac [][saferead_update]);

(* Implementations of the recursive functions *)
(* results put into register 0; arguments in registers 1 .. n *)

val zeroRP_def = Define`
  zeroRP zr bi ei = RPWhile zr bi ei bi FEMPTY
`;

val zeroRP_correct = store_thm(
  "zeroRP_correct",
  ``bi ≠ ei ∧
    (∀s. predOf (P =R=> PCeq bi && REGfRsub (PCsub Q ei) zr (K 0)) s) ⇒
    HOARE P (zeroRP zr bi ei) Q``,
  srw_tac [][zeroRP_def] >>
  match_mp_tac RPWhile >>
  qexists_tac `REGfRsub (PCsub Q ei) zr (K 0)` >>
  srw_tac [][] >| [
    srw_tac [][HOARE_def, predOf_AND_def, predOf_def, PCeq_def, rP_def,
               REGfRsub_def, PCsub_def] >> qexists_tac `0` >>
    fsrw_tac [][haltedConfig_def, combinTheory.UPDATE_EQ],
    fsrw_tac [][RPimp_thm, predOf_AND_def, predOf_def, PCsub_def,
                PCeq_def] >>
    srw_tac [][predOf_def, PCsub_def, predOf_AND_def] >>
    fsrw_tac [][REGfRsub_def, PCsub_def],
    srw_tac [][predOf_def, REGfRsub_def, PCsub_def, predOf_AND_def,
               RPimp_def, PCeq_def, rP_def] >>
    metis_tac [combinTheory.APPLY_UPDATE_ID]
  ])

val RPmove_def = Define`
  RPmove src dest basei exiti =
    RPWhile src basei exiti (basei + 1)
            (FEMPTY |+ (basei + 1, INC dest basei))
`

val SchirmerConseqAux = store_thm(
  "SchirmerConseqAux",
  ``∀P' Q' P Q.
       (∀Z. P' Z ⊢ p ⊣ Q' Z) ∧
       (∀pc reg. P pc reg ⇒
                 ∃Z. P' Z pc reg ∧ ∀s. predOf (Q' Z =R=> Q) s) ⇒
       P ⊢ p ⊣ Q``,
  srw_tac [][HOARE_def, predOf_def, RPimp_def] >> metis_tac []);

val move_correct = store_thm(
  "move_correct",
  ``exiti ≠ basei ∧ exiti ≠ basei + 1 ∧ src ≠ dest ∧
    (∀s. predOf
           (P =R=> PCeq basei &&
                   REGfRsub (REGfRsub (PCsub Q exiti) src (K 0))
                            dest
                            (λr. r dest + r src))
           s) ⇒
    P ⊢ (RPmove src dest basei exiti) ⊣ Q``,
  strip_tac >>
  match_mp_tac (INST_TYPE [alpha |-> ``:num``] SchirmerConseqAux) >>
  map_every qexists_tac [`λn. P && (λpc reg. reg src + reg dest = n)`,
                         `λn. Q`] >>
  reverse (srw_tac [][])
    >- srw_tac [][predOf_AND_def, predOf_def, RPimp_def] >>
  srw_tac [][RPmove_def] >>
  match_mp_tac RPWhile >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  qexists_tac `(λpc reg. reg src + reg dest = Z) &&
               REGfRsub (REGfRsub (PCsub Q exiti) src (K 0))
                        dest
                        (λr. r dest + r src)` >>
  rpt strip_tac
    >- (match_mp_tac INC_correct >>
        srw_tac [ARITH_ss][RPimp_thm, predOf_AND_thm, REGfRsub_ABS,
                           combinTheory.APPLY_UPDATE_THM] >>
        fsrw_tac [][predOf_def, PCsub_def, REGfRsub_def,
                    combinTheory.APPLY_UPDATE_THM] >>
        qpat_assum `Q exiti f` mp_tac >>
        asm_simp_tac (srw_ss()) [combinTheory.UPDATE_EQ] >>
        qpat_assum `x + y = z` mp_tac >>
        asm_simp_tac (srw_ss()) [] >>
        strip_tac >>
        asm_simp_tac (srw_ss()) [Once combinTheory.UPDATE_COMMUTES,
                                 SimpL ``(==>)``,
                                 combinTheory.UPDATE_EQ] >>
        srw_tac [ARITH_ss][Once combinTheory.UPDATE_COMMUTES])
    >- (srw_tac [ARITH_ss][RPimp_thm, predOf_AND_thm] >>
        fsrw_tac [][predOf_def, RPimp_def] >> res_tac >>
        fsrw_tac [][predOf_AND_def, PCeq_def]) >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [RPimp_thm, predOf_AND_thm] >>
  srw_tac [] [predOf_def, PCsub_def, REGfRsub_def] >>
  qpat_assum `Q s.pc f` mp_tac >>
  qpat_assum `0 = s.regs '' src` (assume_tac o SYM) >>
  asm_simp_tac (srw_ss()) [] >>
  asm_simp_tac (srw_ss()) [combinTheory.UPDATE_APPLY_IMP_ID]);

val RPcopy_def = Define`
  RPcopy src dest tmp bi ei =
   FUNION
     (RPWhile src bi (bi + 3) (bi + 1)
       (FUNION
          (FEMPTY |+ (bi + 1, INC dest (bi + 2)))
          (FEMPTY |+ (bi + 2, INC tmp bi))))
     (RPmove tmp src (bi + 3) ei)
`

val FDOM_RPWhile = store_thm(
  "FDOM_RPWhile",
  ``FDOM (RPWhile src bi ei pbi p) = bi INSERT FDOM p``,
  srw_tac [][RPWhile_def, FUNION_DEF, EXTENSION]);

val FDOM_RPmove = store_thm(
  "FDOM_RPmove",
  ``FDOM (RPmove src dest bi ei) = {bi; bi + 1}``,
  srw_tac [][RPmove_def, FUNION_DEF, FDOM_RPWhile]);

val HOARE_skip = store_thm(
  "HOARE_skip",
  ``(∀s. predOf (P =R=> Q) s) ==> P ⊢ FEMPTY ⊣ Q``,
  srw_tac [][HOARE_def, predOf_def, RPimp_def] >>
  qexists_tac `0` >> srw_tac [][haltedConfig_def]);


val RPcopy_correct = store_thm(
  "RPcopy_correct",
  ``ALL_DISTINCT [src; dest; tmp] ∧
    ei ∉ { bi; bi + 1; bi + 2; bi + 3; bi + 4 } ∧
    (∀s. predOf
          (P =R=>
           PCeq bi && rP tmp ((=) 0) &&
           REGfRsub (PCsub Q ei) dest (λr. r dest + r src)) s) ⇒
    P ⊢ RPcopy src dest tmp bi ei ⊣ Q``,
  srw_tac [][RPcopy_def] >>
  match_mp_tac (GEN_ALL HOARE_sequence) >>
  asm_simp_tac (srw_ss() ++ ARITH_ss)
               [FDOM_RPWhile, FUNION_DEF, FDOM_RPmove] >>
  qexists_tac `PCeq (bi + 3) &&
               REGfRsub (REGfRsub
                             (PCsub (Q && PC∉ {bi; bi + 1; bi + 2}) ei)
                             tmp
                             (K 0))
                        src
                        (λr. r src + r tmp)` >>
  reverse conj_tac
    >- (match_mp_tac move_correct >>
        asm_simp_tac (srw_ss() ++ ARITH_ss) [RPimp_thm, predOf_AND_thm]) >>
  qmatch_abbrev_tac `P ⊢ prog ⊣ (PCeq (bi + 3) && QQ)` >>
  match_mp_tac (INST_TYPE [alpha |-> ``:num # num``] SchirmerConseqAux) >>
  map_every qexists_tac [
    `λ(S0,D0). rP src ((=) S0) && rP dest ((=)D0) && P`,
    `λSD. PCeq (bi + 3) && QQ`
  ] >>
  simp_tac (srw_ss()) [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] >>
  reverse conj_tac
    >- srw_tac [][rP_def, predOf_AND_def, predOf_def, RPimp_def] >>
  map_every qx_gen_tac [`S0`, `D0`] >>
  qunabbrev_tac `prog` >> match_mp_tac RPWhile >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [FUNION_DEF] >>
  qexists_tac `
    REGfRsub QQ dest (λr. r dest + r src) &&
    (λpc reg. (reg tmp + reg src = S0) ∧ (reg dest + reg src = S0 + D0))
  ` >> srw_tac [][] >| [
    (* invariant preserved by body *)
    match_mp_tac (GEN_ALL HOARE_sequence) >>
    asm_simp_tac (srw_ss()) [] >>
    qmatch_abbrev_tac `∃R. Pre ⊢ c1 ⊣ R ∧ R ⊢ c2 ⊣ Post` >>
    qexists_tac `
      PCeq (bi + 2) && REGfRsub (PCsub Post bi) tmp (λr. r tmp + 1)
    ` >>
    reverse conj_tac
      >- (qunabbrev_tac `c2` >> match_mp_tac INC_correct >>
          srw_tac [ARITH_ss][]) >>
    qunabbrev_tac `c1` >> match_mp_tac INC_correct >>
    srw_tac [ARITH_ss][Abbr`Pre`, Abbr`Post`, Abbr`QQ`, RPimp_thm,
                       predOf_AND_thm, REGfRsub_ABS,
                       combinTheory.APPLY_UPDATE_THM] >>
    qpat_assum `predOf (REGfRsub QQQ rrr fff) s` mp_tac >>
    asm_simp_tac (srw_ss()) [predOf_def, REGfRsub_def, PCsub_def,
                             combinTheory.APPLY_UPDATE_THM] >>
    qmatch_abbrev_tac `Q ei f1 ==> Q ei f2` >>
    qsuff_tac `f1 = f2` >- srw_tac [][] >>
    srw_tac [ARITH_ss][Abbr`f1`, Abbr`f2`, FUN_EQ_THM,
                       combinTheory.APPLY_UPDATE_THM],

    (* invariant true initially *)
    fsrw_tac [][RPimp_thm, predOf_AND_thm, Abbr`QQ`] >> strip_tac >>
    res_tac >>
    fsrw_tac [ARITH_ss][predOf_def, REGfRsub_def, PCsub_def,
                        combinTheory.APPLY_UPDATE_THM] >>
    pop_assum mp_tac >>
    qpat_assum `P pccc rrrr` (K ALL_TAC) >>
    qpat_assum `0 = s.regs '' tmp` (assume_tac o SYM) >>
    asm_simp_tac (srw_ss()) [combinTheory.UPDATE_APPLY_IMP_ID,
                             combinTheory.APPLY_UPDATE_THM],

    (* post-condition established *)
    asm_simp_tac (srw_ss()) [RPimp_thm, predOf_AND_thm] >>
    srw_tac [][REGfRsub_def, predOf_def] >>
    fsrw_tac [][] >>
    qpat_assum `0 = s.regs '' src` (assume_tac o SYM) >>
    fsrw_tac [][] >>
    qpat_assum `QQ (bi + 3) f2` mp_tac >>
    qmatch_abbrev_tac `QQ (bi + 3) f1 ==> QQ (bi + 3) f2` >>
    qsuff_tac `f1 = f2` >- srw_tac [][] >>
    srw_tac [][Abbr`f1`, Abbr`f2`, combinTheory.APPLY_UPDATE_THM,
               combinTheory.UPDATE_APPLY_IMP_ID]
  ])

val implements_def = Define`
  implements rm f i =
    ∀l r.
     (LENGTH l = i) ∧ (f l = SOME r) ==>
     (λpc r. (∀j. j < i ==> (r (j + 1) = EL j l)) ∧ (pc = 1) ∧ (r 0 = 0)) ⊢
        rm
     ⊣ ((λpc r. (∀j. j < i ==> (r (j + 1) = EL j l))) && rP 0 ((=) r))
`;


val implements_zero = store_thm(
  "implements_zero",
  ``implements FEMPTY (SOME o K 0) 1``,
  srw_tac [][implements_def] >>
  match_mp_tac HOARE_skip >>
  srw_tac [][predOf_def, RPimp_def, predOf_AND_def, rP_def]);


(* val implements_SUC = store_thm(
  "implements_SUC",
  ``implements (
*)

val _ = export_theory();
