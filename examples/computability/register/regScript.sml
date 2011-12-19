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


val RPmove_def = Define`
  RPmove src dest basei exiti =
    FEMPTY |+ (basei, TST src exiti (basei + 1))
           |+ (basei + 1, INC dest basei)
`

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

val move_correct = store_thm(
  "move_correct",
  ``exiti ≠ basei ∧ exiti ≠ basei + 1 ∧ src ≠ dest ∧
    (∀pc regs. P pc regs ⇒
               (pc = basei) ∧
               Q exiti ((src =+ 0) ((dest =+ regs src + regs dest) regs))) ⇒
    HOARE P (RPmove src dest basei exiti) Q``,
  SRW_TAC [][RPmove_def, HOARE_def, predOf_def] THEN RES_TAC THEN
  Q.EXISTS_TAC `2 * s0.regs '' src + 1` THEN
  Q.PAT_ASSUM `Q XX YY` MP_TAC THEN
  Q.PAT_ASSUM `s0.pc = basei` MP_TAC THEN
  Q.ABBREV_TAC `n = s0.regs '' src` THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) THEN
  Q.PAT_ASSUM `P XX YY` (K ALL_TAC) THEN
  MAP_EVERY Q.ID_SPEC_TAC [`s0`, `n`] THEN Induct THENL [
    REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
    REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
    SIMP_TAC (srw_ss()) [] THEN
    Q.MATCH_ABBREV_TAC `firstHaltsAt prog 1 s0 ∧ QQ` THEN
    Q.RM_ABBREV_TAC `QQ` THEN
    Q.MATCH_ABBREV_TAC `firstHaltsAt prog 1 s0 ∧ Q s.pc ($'' s.regs)` THEN
    `s = s0 with pc := exiti`
       by (ASM_SIMP_TAC (srw_ss()) [Step_def, Abbr`s`, Abbr`prog`] THEN
           ASM_SIMP_TAC (srw_ss()) [FLOOKUP_UPDATE]) THEN
    SRW_TAC [][] THENL [
      SRW_TAC [][Abbr`prog`, firstHaltsAt_def, haltedConfig_def,
                 DECIDE ``∀x. x < 1 ⇔ (x = 0)``],
      Q.PAT_ASSUM `Q PP SS` MP_TAC THEN
      Q.MATCH_ABBREV_TAC `Q exiti fm1 ==> Q exiti fm2` THEN
      Q_TAC SUFF_TAC `fm1 = fm2` THEN1 SRW_TAC [][] THEN
      SRW_TAC [][Abbr`fm1`, Abbr`fm2`, FUN_EQ_THM,
                 combinTheory.APPLY_UPDATE_THM] THEN
      SRW_TAC [][] THEN SRW_TAC [][]
    ],
    GEN_TAC THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
    REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
    Q.MATCH_ABBREV_TAC `firstHaltsAt prog m s0 ∧ QQ` THEN
    Q.RM_ABBREV_TAC `QQ` THEN
    Q.MATCH_ABBREV_TAC `firstHaltsAt prog m s0 ∧ Q s.pc ($'' s.regs)` THEN
    `s = FUNPOW (Step prog) (2 * n + 1) (FUNPOW (Step prog) 2 s0)`
      by SRW_TAC [ARITH_ss][Abbr`s`, Abbr`m`, MULT_CLAUSES,
                            GSYM FUNPOW_ADD] THEN
    Q.ABBREV_TAC `s1 = FUNPOW (Step prog) 2 s0` THEN
    `s1 = <| pc := basei;
             regs := s0.regs |+ (src,n) |+ (dest,s0.regs '' dest + 1) |>`
       by (RES_TAC THEN
           SRW_TAC [][Abbr`s1`, Step_def, numeralTheory.numeral_funpow,
                      Abbr`prog`, FLOOKUP_UPDATE] THEN
           SRW_TAC [][theorem "config_component_equality",
                      saferead_update]) THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `s1` MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [saferead_update] THEN
    Q.MATCH_ABBREV_TAC `
      (Q exiti f ==> firstHaltsAt prog (2 * n + 1) s1' ∧
                     Q s'.pc ($'' s'.regs)) ⇒
      firstHaltsAt prog m s0 ∧ Q s'.pc ($'' s'.regs)
    ` THEN
    `Q exiti f`
       by (Q.PAT_ASSUM `Q exiti f0` MP_TAC THEN
           Q.MATCH_ABBREV_TAC `Q exiti f0 ⇒ Q exiti f` THEN
           Q_TAC SUFF_TAC `f0 = f` THEN SRW_TAC [][] THEN
           SRW_TAC [][Abbr`f0`, Abbr`f`, saferead_update, FUN_EQ_THM,
                      combinTheory.APPLY_UPDATE_THM] THEN
           SRW_TAC [ARITH_ss][]) >>
    pop_assum (fn th => srw_tac [][th]) >>
    match_mp_tac firstHaltsAt_prefix >>
    map_every qexists_tac [`2`, `2 * n + 1`] >>
    `¬haltedConfig prog (RM* prog 2 s0)`
      by srw_tac [ARITH_ss][Abbr`s1`, Abbr`prog`, haltedConfig_def] >>
    srw_tac [ARITH_ss][Abbr`m`]
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

val PCeq_def = Define`
  PCeq n pc reg = (pc = n)
`;

val PCsub_def = Define`
  PCsub P v pc reg = P v reg
`

val REGfsub_def = Define`
  REGfsub P r f pc reg = P pc ((r =+ f (reg r)) reg)
`

val RPWhile_rule = store_thm(
  "RPWhile_rule",
  ``ei ≠ bi ∧ bi ∉ FDOM p ∧ ei ∉ FDOM p ∧
    (∀n. HOARE (rP reg ($= n) && REGfsub (PCsub Inv ei) reg ((+) 1)  &&
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
                                      PCsub_def, PCeq_def, REGfsub_def])) >>
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

(* Implementations of the recursive functions *)
(* results put into register 0; arguments in registers 1 .. n *)

val zeroRP_def = Define`
  zeroRP zr bi ei = RPWhile zr bi ei bi FEMPTY
`;

val zeroRP_correct = store_thm(
  "zeroRP_correct",
  ``bi ≠ ei ∧
    (∀s. predOf (P =R=> PCeq bi && REGfsub (PCsub Q ei) zr (K 0)) s) ⇒
    HOARE P (zeroRP zr bi ei) Q``,
  srw_tac [][zeroRP_def] >>
  match_mp_tac RPWhile >>
  qexists_tac `REGfsub (PCsub Q ei) zr (K 0)` >>
  srw_tac [][] >| [
    srw_tac [][HOARE_def, predOf_AND_def, predOf_def, PCeq_def, rP_def,
               REGfsub_def, PCsub_def] >> qexists_tac `0` >>
    fsrw_tac [][haltedConfig_def, combinTheory.UPDATE_EQ],
    fsrw_tac [][RPimp_thm, predOf_AND_def, predOf_def, PCsub_def,
                PCeq_def] >>
    srw_tac [][predOf_def, PCsub_def, predOf_AND_def] >>
    fsrw_tac [][REGfsub_def, PCsub_def],
    srw_tac [][predOf_def, REGfsub_def, PCsub_def, predOf_AND_def,
               RPimp_def, PCeq_def, rP_def] >>
    metis_tac [combinTheory.APPLY_UPDATE_ID]
  ])

val _ = export_theory();
