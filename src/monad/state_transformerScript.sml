open HolKernel Parse boolLib pairTheory pairSyntax combinTheory listTheory;

val _ = new_theory "state_transformer"

infixr 0 ||
infix 1 >>;

val DEF = Lib.with_flag (boolLib.def_suffix, "_DEF") TotalDefn.Define

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val () = Parse.temp_type_abbrev ("M",``:'state -> 'a # 'state``)

val UNIT_DEF = DEF `UNIT (x:'b) = \(s:'a). (x, s)`;

val BIND_DEF = DEF `BIND (g: ('b, 'a) M) (f: 'b -> ('c, 'a) M) = UNCURRY f o g`;

val IGNORE_BIND_DEF = DEF `IGNORE_BIND f g = BIND f (\x. g)`;

val MMAP_DEF = DEF `MMAP (f: 'c -> 'b) (m: ('c, 'a) M) = BIND m (UNIT o f)`;

val JOIN_DEF = DEF `JOIN (z: (('b, 'a) M, 'a) M) = BIND z I`;

val FOR_def = TotalDefn.tDefine "FOR"
 `(FOR : num # num # (num -> (unit, 'state) M) -> (unit, 'state) M) (i, j, a) =
     if i = j then
        a i
     else
        BIND (a i) (\u. FOR (if i < j then i + 1 else i - 1, j, a))`
  (TotalDefn.WF_REL_TAC `measure (\(i, j, a). if i < j then j - i else i - j)`)

val READ_def = TotalDefn.Define`
   (READ : ('state -> 'a) -> ('a, 'state) M) f = \s. (f s, s)`;

val WRITE_def = TotalDefn.Define`
   (WRITE : ('state -> 'state) -> (unit, 'state) M) f = \s. ((), f s)`;

val NARROW_def = TotalDefn.Define`
   (NARROW : 'b -> ('a, 'b # 'state) M -> ('a, 'state) M) v f =
   \s. let (r, s1) = f (v, s) in (r, SND s1)`

val WIDEN_def = TotalDefn.Define`
   (WIDEN : ('a, 'state) M -> ('a, 'b # 'state) M) f =
   \(s1, s2). let (r, s3) = f s2 in (r, (s1, s3))`

val sequence_def = TotalDefn.Define`
   sequence = FOLDR (\m ms. BIND m (\x. BIND ms (\xs. UNIT (x::xs)))) (UNIT [])`

val mapM_def = TotalDefn.Define`
   mapM f = sequence o MAP f`

open simpLib BasicProvers boolSimps metisLib

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

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val op++ = op THEN
val op|| = op ORELSE
val op>> = op THEN1
val Suff = Q_TAC SUFF_TAC
val Know = Q_TAC KNOW_TAC
val FUN_EQ_TAC = CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)

val BIND_LEFT_UNIT = store_thm
  ("BIND_LEFT_UNIT",
   ``!(k:'a->'b->'c#'b) x. BIND (UNIT x) k = k x``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [BIND_DEF, UNIT_DEF, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [UNCURRY_DEF]);

val UNIT_UNCURRY = store_thm
  ("UNIT_UNCURRY",
   ``!(s:'a#'b). UNCURRY UNIT s = s``,
   REWRITE_TAC [UNCURRY_VAR, UNIT_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [PAIR]);

val BIND_RIGHT_UNIT = store_thm
  ("BIND_RIGHT_UNIT",
   ``!(k:'a->'b#'a). BIND k UNIT = k``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [BIND_DEF, UNIT_UNCURRY, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val BIND_ASSOC = store_thm
  ("BIND_ASSOC",
   ``!(k:'a->'b#'a) (m:'b->'a->'c#'a) (n:'c->'a->'d#'a).
       BIND k (\a. BIND (m a) n) = BIND (BIND k m) n``,
   REWRITE_TAC [BIND_DEF, UNCURRY_VAR, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val MMAP_ID = store_thm
  ("MMAP_ID",
   ``MMAP I = (I:('a->'b#'a)->('a->'b#'a))``,
   MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, I_THM, o_DEF]
   ++ CONV_TAC (DEPTH_CONV ETA_CONV)
   ++ REWRITE_TAC [BIND_RIGHT_UNIT]);

val MMAP_COMP = store_thm
  ("MMAP_COMP",
   ``!f g. (MMAP (f o g):('a->'b#'a)->('a->'d#'a))
           = (MMAP f:('a->'c#'a)->('a->'d#'a)) o MMAP g``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ Suff `(\x. UNIT (f (g x)))
                  = (\a. BIND ((\x. UNIT (g x)) a) (\x. UNIT (f x)))`
      >> (STRIP_TAC ++ ASM_REWRITE_TAC [])
   ++ MATCH_MP_TAC EQ_EXT
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [BIND_LEFT_UNIT]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val MMAP_UNIT = store_thm
  ("MMAP_UNIT",
   ``!(f:'b->'c). MMAP f o UNIT = (UNIT:'c->'a->'c#'a) o f``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, o_DEF, BIND_LEFT_UNIT]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val MMAP_JOIN = store_thm
  ("MMAP_JOIN",
   ``!f. MMAP f o JOIN = JOIN o MMAP (MMAP f:('a->'b#'a)->('a->'c#'a))``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, o_DEF, JOIN_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [GSYM BIND_ASSOC, I_THM]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]);

val JOIN_UNIT = store_thm
  ("JOIN_UNIT",
   ``JOIN o UNIT = (I:('a->'b#'a)->('a->'b#'a))``,
   REWRITE_TAC [JOIN_DEF, o_DEF, BIND_LEFT_UNIT, I_DEF, S_DEF, K_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val JOIN_MMAP_UNIT = store_thm
  ("JOIN_MMAP_UNIT",
   ``JOIN o MMAP UNIT = (I:('a->'b#'a)->('a->'b#'a))``,
   REWRITE_TAC [JOIN_DEF, o_DEF, MMAP_DEF]
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]
   ++ MATCH_MP_TAC EQ_EXT
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [BIND_RIGHT_UNIT, I_THM]);

val JOIN_MAP_JOIN = store_thm
  ("JOIN_MAP_JOIN",
   ``JOIN o MMAP JOIN = ((JOIN o JOIN)
       :('a -> ('a -> ('a -> 'b # 'a) # 'a) # 'a) -> 'a -> 'b # 'a)``,
   REWRITE_TAC [JOIN_DEF, o_DEF, MMAP_DEF]
   ++ MATCH_MP_TAC EQ_EXT
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]);

val JOIN_MAP = store_thm
  ("JOIN_MAP",
   ``!k (m:'b->'a->'c#'a). BIND k m = JOIN (MMAP m k)``,
   REWRITE_TAC [JOIN_DEF, o_DEF, MMAP_DEF]
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC []);

val FST_o_UNIT = store_thm
  ("FST_o_UNIT",
   ``!x. FST o UNIT x = K x``,
   FUN_EQ_TAC
   ++ REWRITE_TAC [o_THM, UNIT_DEF, K_THM]
   ++ BETA_TAC
   ++ REWRITE_TAC [FST]);

val SND_o_UNIT = store_thm
  ("SND_o_UNIT",
   ``!x. SND o UNIT x = I``,
   FUN_EQ_TAC
   ++ REWRITE_TAC [o_THM, UNIT_DEF, I_THM]
   ++ BETA_TAC
   ++ REWRITE_TAC [SND]);

val FST_o_MMAP = store_thm
  ("FST_o_MMAP",
   ``!f g. FST o MMAP f g = f o FST o g``,
   FUN_EQ_TAC
   ++ REWRITE_TAC [MMAP_DEF, BIND_DEF, UNCURRY, o_THM, UNIT_DEF]
   ++ BETA_TAC
   ++ REWRITE_TAC [FST]);

val sequence_nil = store_thm("sequence_nil",
  ``sequence [] = UNIT []``,
  BasicProvers.SRW_TAC[][sequence_def])
val _ = BasicProvers.export_rewrites["sequence_nil"]

val mapM_nil = store_thm("mapM_nil",
  ``mapM f [] = UNIT []``,
  BasicProvers.SRW_TAC[][mapM_def])
val _ = BasicProvers.export_rewrites["mapM_nil"]

val mapM_cons = store_thm("mapM_cons",
  ``mapM f (x::xs) = BIND (f x) (\y. BIND (mapM f xs) (\ys. UNIT (y::ys)))``,
  BasicProvers.SRW_TAC[][mapM_def,sequence_def])

(* ------------------------------------------------------------------------- *)

val _ = export_theory ()
