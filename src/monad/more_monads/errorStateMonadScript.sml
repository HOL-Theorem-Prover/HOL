open HolKernel Parse boolLib bossLib pairTheory pairSyntax combinTheory
     optionTheory listTheory;

val _ = new_theory "errorStateMonad"

val DEF = Lib.with_flag (boolLib.def_suffix, "_DEF") TotalDefn.Define

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

Type M[local] = “:'state -> ('a # 'state) option”

val UNIT_DEF = DEF `UNIT (x:'b) : ('b,'a) M = \(s:'a). SOME (x, s)`;

val BIND_DEF = DEF `
  BIND (g: ('b, 'a) M) (f: 'b -> ('c, 'a) M) (s0:'a) =
    case g s0 of
      NONE => NONE
    | SOME (b,s) => f b s
`

val IGNORE_BIND_DEF = DEF `
  IGNORE_BIND (f:('a,'b)M) (g:('c,'b)M) : ('c,'b)M = BIND f (\x. g)`;

val MMAP_DEF = DEF `MMAP (f: 'c -> 'b) (m: ('c, 'a) M) = BIND m (UNIT o f)`;

val JOIN_DEF = DEF `JOIN (z: (('b, 'a) M, 'a) M) = BIND z I`;

val EXT_DEF = DEF `EXT g m = BIND m g` ;

(* composition in the Kleisli category:
  can compose any monad with the state transformer monad in this way *)
val MCOMP_DEF = DEF `MCOMP g f = CURRY (OPTION_MCOMP (UNCURRY g) (UNCURRY f))`;

val FOR_def = TotalDefn.tDefine "FOR"
 `(FOR : num # num # (num -> (unit, 'state) M) -> (unit, 'state) M) (i, j, a) =
     if i = j then
        a i
     else
        BIND (a i) (\u. FOR (if i < j then i + 1 else i - 1, j, a))`
  (TotalDefn.WF_REL_TAC `measure (\(i, j, a). if i < j then j - i else i - j)`)

val FOREACH_def = TotalDefn.Define`
   ((FOREACH : 'a list # ('a -> (unit, 'state) M) -> (unit, 'state) M) ([], a) =
       UNIT ()) /\
   (FOREACH (h :: t, a) = BIND (a h) (\u. FOREACH (t, a)))`

val READ_def = TotalDefn.Define`
   (READ : ('state -> 'a) -> ('a, 'state) M) f = \s. SOME (f s, s)`;

val WRITE_def = TotalDefn.Define`
   (WRITE : ('state -> 'state) -> (unit, 'state) M) f = \s. SOME ((), f s)`;

val NARROW_def = TotalDefn.Define`
   (NARROW : 'b -> ('a, 'b # 'state) M -> ('a, 'state) M) v f =
   \s. case f (v, s) of
           NONE => NONE
         | SOME (r, s1) => SOME (r, SND s1)`

val WIDEN_def = TotalDefn.Define`
   (WIDEN : ('a, 'state) M -> ('a, 'b # 'state) M) f =
   \(s1, s2). case f s2 of
                  NONE => NONE
                | SOME (r, s3) => SOME (r, (s1, s3))`

val sequence_def = TotalDefn.Define`
   sequence = FOLDR (\m ms. BIND m (\x. BIND ms (\xs. UNIT (x::xs)))) (UNIT [])`

val mapM_def = TotalDefn.Define`
   mapM f = sequence o MAP f`

open simpLib BasicProvers boolSimps metisLib

Definition mwhile_step_def:
  mwhile_step P g x 0 s = BIND (P x) (\b. UNIT (b,x)) s /\
  mwhile_step P g x (SUC n) s = BIND (P x)
    (\b. if b then BIND (g x) (\gx. mwhile_step P g gx n) else UNIT (b,x)) s
End

Theorem mwhile_exists[local]:
  !P g. ?f .
    !x s. f x s = BIND (P x) (\b. if b then BIND (g x) f else UNIT x) s
Proof
  qx_gen_tac `P` >> qx_gen_tac `g` >>
  qexists_tac `\x s.
    if ?n. !y t. mwhile_step P g x n s <> SOME ((T,y), t) then
      let n = @n. !y t. mwhile_step P g x n s <> SOME ((T,y), t) /\
        !m. m < n ==> ?y t. mwhile_step P g x m s = SOME ((T,y), t) in
      case mwhile_step P g x n s of NONE => NONE | SOME ((_,y),t) => SOME (y,t)
    else ARB` >>
  qx_gen_tac `x` >> qx_gen_tac `s` >> BETA_TAC >>
  reverse (IF_CASES_TAC)
  >- (
    fs[BIND_DEF, UNIT_DEF, COND_RATOR] >>
    first_assum (qspec_then `0` assume_tac) >>
    fs[mwhile_step_def, BIND_DEF, UNIT_DEF] >>
    full_case_tac >> fs[] >> full_case_tac >> fs[] >>
    rpt (var_eq_tac) >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    fs[mwhile_step_def, BIND_DEF, UNIT_DEF] >> rfs[BIND_DEF] >>
    full_case_tac >> fs[] >> full_case_tac >> fs[] >>
    IF_CASES_TAC >> simp[LET_DEF] >>
    pop_assum (qx_choose_then `n` assume_tac) >>
    first_x_assum (qspec_then `SUC n` assume_tac) >>
    fs[mwhile_step_def, BIND_DEF, UNIT_DEF] >> rfs[BIND_DEF]
    ) >>
  pop_assum (qx_choose_then `n` assume_tac) >>
  SELECT_ELIM_TAC >> conj_tac
  >- (
    completeInduct_on `n` >> strip_tac >>
    Cases_on `!m. m < n ==> ?y t. mwhile_step P g x m s = SOME ((T,y), t)` >>
    fs[BIND_DEF, mwhile_step_def] >- (qexists_tac `n` >> fs[]) >>
    first_x_assum irule >> goal_assum drule >>
    asm_rewrite_tac []
    ) >>
  fs[BIND_DEF, UNIT_DEF, COND_RATOR, LET_DEF] >>
  pop_assum kall_tac >> qx_gen_tac `n` >> rpt strip_tac >>
  fs[GSYM PULL_FORALL] >> Cases_on `n`
  >- (
    fs[mwhile_step_def, BIND_DEF, UNIT_DEF] >>
    Cases_on `P x s` >> simp[] >> rename1 `P x s = SOME y` >>
    PairCases_on `y` >> fs[]
    ) >>
  rename1 `SUC n` >> fs[mwhile_step_def, BIND_DEF, UNIT_DEF, COND_RATOR] >>
  Cases_on `P x s` >> simp[] >>
  rename1 `P x s = SOME y` >> PairCases_on `y` >> Cases_on `y0` >> fs[] >>
  Cases_on `g x y1` >> fs[] >> rename1 `g x y1 = SOME z` >>
  PairCases_on `z` >> fs[] >>
  reverse (IF_CASES_TAC)
  >- (fs[] >> pop_assum (qspec_then `n` assume_tac) >> rfs[]) >>
  SELECT_ELIM_TAC >> conj_tac
  >- (
    ntac 4 (last_x_assum kall_tac) >>
    pop_assum (qx_choose_then `n` assume_tac) >>
    completeInduct_on `n` >> strip_tac >>
    Cases_on `!m. m < n ==> ?y t. mwhile_step P g z0 m z1 = SOME ((T,y),t)`
    >- (goal_assum drule >> fs[]) >>
    pop_assum mp_tac >> simp[]
    ) >>
  qx_gen_tac `m` >> strip_tac >>
  qsuff_tac `m = n` >> fs[] >>
  fs[arithmeticTheory.EQ_LESS_EQ, GSYM arithmeticTheory.NOT_LESS] >>
  conj_tac >> CCONTR_TAC >> fs[]
  >- (first_x_assum drule >> strip_tac >> rfs[]) >>
  last_x_assum (qspec_then `SUC m` assume_tac) >>
  rfs[mwhile_step_def, BIND_DEF, UNIT_DEF]
QED

val MWHILE_DEF = new_specification(
  "MWHILE_DEF", ["MWHILE"],
  mwhile_exists |> SIMP_RULE bool_ss [SKOLEM_THM]);

Definition mwhile_unit_step_def:
  mwhile_unit_step P g 0 s = P s /\
  mwhile_unit_step P g (SUC n) s = BIND P
    (\b. if b then IGNORE_BIND g (mwhile_unit_step P g n) else UNIT b) s
End

Theorem mwhile_unit_exists[local]:
  !P g. ?f. !s.
    f s = BIND P (\b. if b then IGNORE_BIND g f else UNIT ()) s
Proof
  qx_gen_tac `P` >> qx_gen_tac `g` >>
  qexists_tac `\s.
    if ?n. !t. mwhile_unit_step P g n s <> SOME (T, t) then
      let n = @n. !t. mwhile_unit_step P g n s <> SOME (T, t) /\
        !m. m < n ==> ?t. mwhile_unit_step P g m s = SOME (T, t) in
      case mwhile_unit_step P g n s of NONE => NONE | SOME (_,t) => SOME ((),t)
    else ARB` >>
  qx_gen_tac `s` >> BETA_TAC >>
  reverse (IF_CASES_TAC)
  >- (
    fs[BIND_DEF, UNIT_DEF, COND_RATOR] >>
    first_assum (qspec_then `0` assume_tac) >>
    fs[mwhile_unit_step_def, BIND_DEF, IGNORE_BIND_DEF, UNIT_DEF] >>
    first_assum (qspec_then `SUC 0` assume_tac) >>
    fs[mwhile_unit_step_def, BIND_DEF, UNIT_DEF, COND_RATOR, IGNORE_BIND_DEF] >>
    rfs[] >> full_case_tac >> fs[] >> full_case_tac >> fs[] >>
    IF_CASES_TAC >> simp[] >>
    pop_assum (qx_choose_then `n` assume_tac) >>
    first_x_assum (qspec_then `SUC n` assume_tac) >>
    fs[mwhile_unit_step_def, BIND_DEF, IGNORE_BIND_DEF, UNIT_DEF, COND_RATOR] >>
    rfs[]
    ) >>
  pop_assum (qx_choose_then `n` assume_tac) >>
  SELECT_ELIM_TAC >> conj_tac
  >- (
    completeInduct_on `n` >> strip_tac >>
    Cases_on `!m. m < n ==> ?t. mwhile_unit_step P g m s = SOME (T, t)` >>
    fs[BIND_DEF, mwhile_unit_step_def] >- (qexists_tac `n` >> fs[]) >>
    first_x_assum irule >> goal_assum drule >>
    asm_rewrite_tac []
    ) >>
  fs[BIND_DEF, UNIT_DEF, COND_RATOR, IGNORE_BIND_DEF] >>
  pop_assum kall_tac >> qx_gen_tac `n` >> rpt strip_tac >>
  fs[GSYM PULL_FORALL] >> Cases_on `n`
  >- (
    fs[mwhile_unit_step_def, BIND_DEF, UNIT_DEF] >>
    Cases_on `P s` >> simp[] >> rename1 `P s = SOME y` >>
    PairCases_on `y` >> fs[]
    ) >>
  rename1 `SUC n` >>
  fs[mwhile_unit_step_def, BIND_DEF, UNIT_DEF, COND_RATOR, IGNORE_BIND_DEF] >>
  Cases_on `P s` >> simp[] >>
  rename1 `P s = SOME y` >> PairCases_on `y` >> Cases_on `y0` >> fs[] >>
  Cases_on `g y1` >> fs[] >> rename1 `g y1 = SOME z` >>
  PairCases_on `z` >> fs[] >>
  reverse (IF_CASES_TAC)
  >- (fs[] >> pop_assum (qspec_then `n` assume_tac) >> rfs[]) >>
  SELECT_ELIM_TAC >> conj_tac
  >- (
    ntac 4 (last_x_assum kall_tac) >>
    pop_assum (qx_choose_then `n` assume_tac) >>
    completeInduct_on `n` >> strip_tac >>
    Cases_on `!m. m < n ==> ?t. mwhile_unit_step P g m z1 = SOME (T,t)`
    >- (goal_assum drule >> fs[]) >>
    pop_assum mp_tac >> simp[]
    ) >>
  qx_gen_tac `m` >> strip_tac >>
  qsuff_tac `m = n` >> fs[] >>
  fs[arithmeticTheory.EQ_LESS_EQ, GSYM arithmeticTheory.NOT_LESS] >>
  conj_tac >> CCONTR_TAC >> fs[]
  >- (first_x_assum drule >> strip_tac >> rfs[]) >>
  last_x_assum (qspec_then `SUC m` assume_tac) >>
  rfs[mwhile_unit_step_def, BIND_DEF, UNIT_DEF, IGNORE_BIND_DEF]
QED

val MWHILE_UNIT_DEF = new_specification(
  "MWHILE_UNIT_DEF", ["MWHILE_UNIT"],
  mwhile_unit_exists |> SIMP_RULE bool_ss [SKOLEM_THM]);


(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

open BasicProvers
val BIND_LEFT_UNIT = store_thm
  ("BIND_LEFT_UNIT[simp]",
   ``!k x. BIND (UNIT x) k = k x``,
   SRW_TAC [][BIND_DEF, UNIT_DEF, FUN_EQ_THM]);

val option_case_eq = prove_case_eq_thm{
  case_def= option_case_def,
  nchotomy = option_CASES
               |> ONCE_REWRITE_RULE [DISJ_COMM]
};

val MCOMP_THM = store_thm ("MCOMP_THM",
  ``MCOMP g f = EXT g o f``,
  REWRITE_TAC [MCOMP_DEF, EXT_DEF, FUN_EQ_THM, o_THM,
      OPTION_MCOMP_def, CURRY_DEF, UNCURRY_DEF]
    THEN REPEAT GEN_TAC
    THEN Cases_on `f x x'`
    THEN ASM_SIMP_TAC bool_ss [ OPTION_BIND_def, BIND_DEF, UNCURRY_VAR,
      option_case_def, pair_CASE_def]) ;

val MCOMP_ASSOC = store_thm ("MCOMP_ASSOC",
   ``MCOMP f (MCOMP g h) = MCOMP (MCOMP f g) h``,
  REWRITE_TAC [MCOMP_DEF, OPTION_MCOMP_ASSOC, UNCURRY_CURRY_THM]);

val UNIT_CURRY = store_thm ("UNIT_CURRY",
  ``UNIT = CURRY SOME``,
  REWRITE_TAC [FUN_EQ_THM, UNIT_DEF, CURRY_DEF]
    THEN BETA_TAC THEN REPEAT GEN_TAC THEN REFL_TAC);

val MCOMP_ID = store_thm
  ("MCOMP_ID",
   ``(MCOMP g UNIT = g) /\ (MCOMP UNIT f = f)``,
  REWRITE_TAC [MCOMP_DEF, UNIT_CURRY, OPTION_MCOMP_ID,
    UNCURRY_CURRY_THM, CURRY_UNCURRY_THM]);

(* could also derive following two theorems from MCOMP_ASSOC and MCOMP_ID,
  using MCOMP_THM and EXT_DEF *)

val BIND_RIGHT_UNIT = store_thm
  ("BIND_RIGHT_UNIT[simp]",
   ``!k. BIND k UNIT = k``,
   SRW_TAC [boolSimps.CONJ_ss]
           [BIND_DEF, UNIT_DEF, FUN_EQ_THM, option_case_eq, pair_case_eq] THEN
   (Q.RENAME1_TAC `k v = NONE` ORELSE Q.RENAME1_TAC `NONE = k v`) THEN
   Cases_on `k v` THEN SRW_TAC [][] THEN
   metisLib.METIS_TAC [TypeBase.nchotomy_of ``:'a # 'b``]);

val BIND_ASSOC = store_thm
  ("BIND_ASSOC",
   ``!k m n. BIND k (\a. BIND (m a) n) = BIND (BIND k m) n``,
   SRW_TAC [][BIND_DEF, FUN_EQ_THM] THEN
   Q.RENAME1_TAC `option_CASE (k v) NONE _` THEN
   Cases_on `k v` THEN SRW_TAC [][] THEN
   Q.RENAME1_TAC `pair_CASE p _` THEN Cases_on `p` THEN
   SRW_TAC [][]);

val MMAP_ID = store_thm
  ("MMAP_ID[simp]",
   ``MMAP I = I``,
   SRW_TAC[][FUN_EQ_THM, MMAP_DEF]);

val MMAP_COMP = store_thm
  ("MMAP_COMP",
   ``!f g. MMAP (f o g) = MMAP f o MMAP g``,
   SRW_TAC[][FUN_EQ_THM, MMAP_DEF, o_DEF, GSYM BIND_ASSOC]);

val MMAP_UNIT = store_thm
  ("MMAP_UNIT",
   ``!f. MMAP f o UNIT = UNIT o f``,
   SRW_TAC[][FUN_EQ_THM, MMAP_DEF]);

val MMAP_JOIN = store_thm
  ("MMAP_JOIN",
   ``!f. MMAP f o JOIN = JOIN o MMAP (MMAP f)``,
   SRW_TAC [][MMAP_DEF, o_DEF, JOIN_DEF, FUN_EQ_THM, GSYM BIND_ASSOC]);

val JOIN_UNIT = store_thm
  ("JOIN_UNIT",
   ``JOIN o UNIT = I``,
   SRW_TAC[][FUN_EQ_THM, JOIN_DEF, o_DEF]);

val JOIN_MMAP_UNIT = store_thm
  ("JOIN_MMAP_UNIT[simp]",
   ``JOIN o MMAP UNIT = I``,
   SRW_TAC[boolSimps.ETA_ss]
          [JOIN_DEF, o_DEF, MMAP_DEF, FUN_EQ_THM, GSYM BIND_ASSOC]);

val JOIN_MAP_JOIN = store_thm
  ("JOIN_MAP_JOIN",
   ``JOIN o MMAP JOIN = JOIN o JOIN``,
   SRW_TAC [][FUN_EQ_THM, JOIN_DEF, o_DEF, MMAP_DEF, GSYM BIND_ASSOC]);

val JOIN_MAP = store_thm
  ("JOIN_MAP",
   ``!k m. BIND k m = JOIN (MMAP m k)``,
   SRW_TAC [boolSimps.ETA_ss]
           [JOIN_DEF, o_DEF, MMAP_DEF, FUN_EQ_THM, GSYM BIND_ASSOC]);

val sequence_nil = store_thm("sequence_nil[simp]",
  ``sequence [] = UNIT []``,
  SRW_TAC[][sequence_def])

val mapM_nil = store_thm("mapM_nil[simp]",
  ``mapM f [] = UNIT []``,
  SRW_TAC[][mapM_def])

val mapM_cons = store_thm("mapM_cons",
  ``mapM f (x::xs) = BIND (f x) (\y. BIND (mapM f xs) (\ys. UNIT (y::ys)))``,
  SRW_TAC[][mapM_def,sequence_def])

(* fail and choice *)
val ES_FAIL_DEF = DEF`
  ES_FAIL s = NONE
`;

val ES_CHOICE_DEF = DEF`
  ES_CHOICE xM yM s =
    case xM s of
       NONE => yM s
     | xr => xr
`;

val ES_GUARD_DEF = DEF`
  ES_GUARD b = if b then UNIT () else ES_FAIL
`

val _ =
    monadsyntax.declare_monad (
      "errorState",
      { bind = “BIND”, ignorebind = SOME “IGNORE_BIND”, unit = “UNIT”,
        choice = SOME “ES_CHOICE”, fail = SOME “ES_FAIL”,
        guard = SOME “ES_GUARD”
      }
    )


val ES_CHOICE_ASSOC = store_thm(
  "ES_CHOICE_ASSOC",
  ``ES_CHOICE xM (ES_CHOICE yM zM) = ES_CHOICE (ES_CHOICE xM yM) zM``,
  SRW_TAC[][FUN_EQ_THM, ES_CHOICE_DEF] THEN
  Q.RENAME1_TAC `option_CASE (xM s)` THEN Cases_on `xM s` THEN SRW_TAC[][]);

val ES_CHOICE_FAIL_LID = store_thm(
  "ES_CHOICE_FAIL_LID[simp]",
  ``ES_CHOICE ES_FAIL xM = xM``,
  SRW_TAC[][FUN_EQ_THM, ES_CHOICE_DEF, ES_FAIL_DEF]);

val ES_CHOICE_FAIL_RID = store_thm(
  "ES_CHOICE_FAIL_RID[simp]",
  ``ES_CHOICE xM ES_FAIL = xM``,
  SRW_TAC[][FUN_EQ_THM, ES_CHOICE_DEF, ES_FAIL_DEF] THEN
  Q.RENAME1_TAC `option_CASE (xM s)` THEN Cases_on `xM s` THEN SRW_TAC[][]);

val BIND_FAIL_L = store_thm(
  "BIND_FAIL_L[simp]",
  ``BIND ES_FAIL fM = ES_FAIL``,
  SRW_TAC[][FUN_EQ_THM, ES_FAIL_DEF, BIND_DEF]);

val BIND_ESGUARD = store_thm(
  "BIND_ESGUARD[simp]",
  ``(BIND (ES_GUARD F) fM = ES_FAIL) /\
    (BIND (ES_GUARD T) fM = fM ())``,
  SRW_TAC[][ES_GUARD_DEF]);

val IGNORE_BIND_ESGUARD = store_thm(
  "IGNORE_BIND_ESGUARD[simp]",
  ``(IGNORE_BIND (ES_GUARD F) xM = ES_FAIL) /\
    (IGNORE_BIND (ES_GUARD T) xM = xM)``,
  SRW_TAC[][ES_GUARD_DEF, IGNORE_BIND_DEF]);

val IGNORE_BIND_FAIL = store_thm(
  "IGNORE_BIND_FAIL[simp]",
  ``(IGNORE_BIND ES_FAIL xM = ES_FAIL) /\
    (IGNORE_BIND xM ES_FAIL = ES_FAIL)``,
  SRW_TAC[][IGNORE_BIND_DEF] THEN
  SRW_TAC[][ES_FAIL_DEF, BIND_DEF, FUN_EQ_THM] THEN
  Q.RENAME1_TAC `option_CASE (xM s)` THEN Cases_on `xM s` THEN
  SRW_TAC [][] THEN Q.RENAME1_TAC `xM s = SOME rs` THEN Cases_on `rs` THEN
  SRW_TAC[][])

(* applicative *)
val ES_APPLY_DEF = DEF`
  ES_APPLY fM xM = BIND fM (\f. BIND xM (\x. UNIT (f x)))
`
val _ = overload_on ("APPLICATIVE_FAPPLY", ``ES_APPLY``)

val APPLY_UNIT = store_thm(
  "APPLY_UNIT",
  ``UNIT f <*> xM = MMAP f xM``,
  SRW_TAC[][ES_APPLY_DEF, MMAP_DEF, o_DEF]);

val APPLY_UNIT_UNIT = store_thm(
  "APPLY_UNIT_UNIT[simp]",
  ``UNIT f <*> UNIT x = UNIT (f x)``,
  SRW_TAC[][ES_APPLY_DEF]);

val ES_LIFT2_DEF = DEF`
  ES_LIFT2 f xM yM = MMAP f xM <*> yM
`;


(* ------------------------------------------------------------------------- *)

val _ = export_theory ()
