open HolKernel Parse boolLib pairTheory pairSyntax combinTheory
     optionTheory listTheory;

val _ = new_theory "errorStateMonad"

val DEF = Lib.with_flag (boolLib.def_suffix, "_DEF") TotalDefn.Define

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val () = Parse.temp_type_abbrev ("M",``:'state -> ('a # 'state) option``)

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

(*
val mwhile_exists = prove(
  ``!g b. ?f.
      f = BIND g (\gv. if gv then IGNORE_BIND b f else UNIT ())``,
  MAP_EVERY Q.X_GEN_TAC [`g`, `b`] THEN
  Q.EXISTS_TAC
    `\s0. if ?n. ~FST (g (FUNPOW (SND o b o SND o g) n s0)) then
            let n = LEAST n. ~FST (g (FUNPOW (SND o b o SND o g) n s0))
            in
              ((), SND (g (FUNPOW (SND o b o SND o g) n s0)))
          else ARB` THEN
  SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `s` THEN
  COND_CASES_TAC THENL [
    POP_ASSUM (Q.X_CHOOSE_THEN `n0` ASSUME_TAC) THEN
    SIMP_TAC (srw_ss()) [SimpLHS, LET_THM] THEN
    numLib.LEAST_ELIM_TAC THEN CONJ_TAC THEN1 METIS_TAC[] THEN
    Q.X_GEN_TAC `n` THEN SIMP_TAC (srw_ss()) [] THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss()) [BIND_DEF] THEN
    Q.ISPEC_THEN `g s` (Q.X_CHOOSE_THEN `gv1`
                                       (Q.X_CHOOSE_THEN `s1` ASSUME_TAC))
                pairTheory.pair_CASES THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN REVERSE (Cases_on `gv1`)
    THEN1 (`n = 0`
             by (SPOSE_NOT_THEN ASSUME_TAC THEN
                 `0 < n` by SRW_TAC [numSimps.ARITH_ss][] THEN
                 FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
                 SRW_TAC [][]) THEN
           SRW_TAC [][UNIT_DEF]) THEN
    ASM_SIMP_TAC (srw_ss()) [IGNORE_BIND_DEF, BIND_DEF] THEN
    Q.ISPEC_THEN `b s1` (Q.X_CHOOSE_THEN `bv1`
                                       (Q.X_CHOOSE_THEN `s2` ASSUME_TAC))
                pairTheory.pair_CASES THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    `?m. n = SUC m`
      by (Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    Q.SUBGOAL_THEN `?n. ~FST (g (FUNPOW (SND o b o SND o g) n s2))`
      ASSUME_TAC
    THEN1 (Q.EXISTS_TAC `m` THEN
           FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.FUNPOW]) THEN
    ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.FUNPOW] THEN
    Q_TAC SUFF_TAC
       `(LEAST n. ~FST (g (FUNPOW (SND o b o SND o g) n s2))) = m`
       THEN1 SRW_TAC [][] THEN
    numLib.LEAST_ELIM_TAC THEN CONJ_TAC THEN1 SRW_TAC [][] THEN
    Q.X_GEN_TAC `p` THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `~(m < p) /\ ~(p < m)` THEN1 numLib.ARITH_TAC THEN
    REPEAT STRIP_TAC THENL [
      `FST (g (FUNPOW (SND o b o SND o g) m s2))` by METIS_TAC[] THEN
      `FST (g (FUNPOW (SND o b o SND o g) (SUC m) s))`
         by (SIMP_TAC (srw_ss())[arithmeticTheory.FUNPOW] THEN
             SRW_TAC [][]),
      `SUC p < SUC m` by SRW_TAC [numSimps.ARITH_ss][] THEN
      RES_THEN MP_TAC THEN
      SIMP_TAC (srw_ss()) [arithmeticTheory.FUNPOW] THEN
      SRW_TAC [][]
    ],
    FULL_SIMP_TAC (srw_ss()) [BIND_DEF] THEN
    Q.ISPEC_THEN `g s` (Q.X_CHOOSE_THEN `gv1`
                                       (Q.X_CHOOSE_THEN `s1` ASSUME_TAC))
                pairTheory.pair_CASES THEN
    REVERSE (SRW_TAC [][])
      THEN1(FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][]) THEN
    SRW_TAC [][IGNORE_BIND_DEF, BIND_DEF] THEN
    Q.ISPEC_THEN `b s1` (Q.X_CHOOSE_THEN `bv1`
                                       (Q.X_CHOOSE_THEN `s2` ASSUME_TAC))
                pairTheory.pair_CASES THEN
    SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `SUC m` (MP_TAC o Q.GEN `m`)) THEN
    SRW_TAC [][arithmeticTheory.FUNPOW]
  ])

val MWHILE_DEF = new_specification(
  "MWHILE_DEF", ["MWHILE"],
  mwhile_exists |> SIMP_RULE bool_ss [SKOLEM_THM]);
*)

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
val pair_case_eq = prove_case_eq_thm{
  case_def= TypeBase.case_def_of ``:'a # 'b``
            |> INST_TYPE [alpha |-> gamma, beta |-> alpha, gamma |-> beta]
            |> GENL [``x:'a``, ``y:'b``, ``f:'a -> 'b -> 'c``] ,
  nchotomy = TypeBase.nchotomy_of ``:'a # 'b``
};


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

val BIND_FAIL = store_thm(
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
