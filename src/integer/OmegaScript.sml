open HolKernel boolLib integerTheory

infix THEN THENL THEN1 |->
infix 8 by

local open listTheory in end;

val _ = new_theory "Omega";

open simpLib boolSimps SingleStep BasicProvers

val _ = augment_srw_ss [intSimps.INT_REDUCE_ss, numSimps.REDUCE_ss]

val MAP2_def = TotalDefn.Define
  `(MAP2 pad f [] [] = []) /\
   (MAP2 pad f [] (y::ys) = (f pad y) :: MAP2 pad f [] ys) /\
   (MAP2 pad f (x::xs) [] = (f x pad) :: MAP2 pad f xs []) /\
   (MAP2 pad f (x::xs) (y::ys) = f x y :: MAP2 pad f xs ys)`;

val MAP2_zero_ADD = store_thm(
  "MAP2_zero_ADD",
  ``!xs. (MAP2 0i $+ [] xs = xs) /\
         (MAP2 0 $+ xs [] = xs)``,
  Induct THEN ASM_SIMP_TAC bool_ss [MAP2_def, INT_ADD_LID, INT_ADD_RID]);

val sumc_def = TotalDefn.Define
  `(sumc _ [] = 0i) /\
   (sumc [] _ = 0) /\
   (sumc (c::cs) (v::vs) = c * v + sumc cs vs)`;

val sumc_ind = theorem "sumc_ind"

val sumc_thm = store_thm(
  "sumc_thm",
  ``!cs vs c v.
       (sumc [] vs = 0) /\
       (sumc cs [] = 0) /\
       (sumc (c::cs) (v::vs) = c * v + sumc cs vs)``,
  HO_MATCH_MP_TAC sumc_ind THEN SIMP_TAC bool_ss [sumc_def]);

val sumc_ADD = store_thm(
  "sumc_ADD",
  ``!cs vs ds. sumc cs vs + sumc ds vs =
               sumc (MAP2 0 $+ cs ds) vs``,
  HO_MATCH_MP_TAC sumc_ind THEN REPEAT STRIP_TAC THENL [
    SIMP_TAC bool_ss [sumc_thm, MAP2_def, INT_ADD_LID],
    SIMP_TAC bool_ss [sumc_thm, MAP2_def, INT_ADD_LID],
    SIMP_TAC bool_ss [sumc_thm, MAP2_def, INT_ADD_LID,
                      MAP2_zero_ADD],
    Cases_on `ds` THEN
    SIMP_TAC bool_ss [sumc_thm, MAP2_zero_ADD, INT_ADD_RID, MAP2_def,
                      INT_RDISTRIB] THEN
    POP_ASSUM (fn th => REWRITE_TAC [GSYM th]) THEN
    CONV_TAC (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM))
  ]);

val sumc_MULT = store_thm(
  "sumc_MULT",
  ``!cs vs f. f * sumc cs vs = sumc (MAP (\x. f * x) cs) vs``,
  Induct THEN SRW_TAC [][sumc_thm] THEN
  Cases_on `vs` THEN SRW_TAC [][sumc_thm, INT_LDISTRIB]);

val modhat_def = TotalDefn.Define
  `modhat x y = x - y * ((2 * x + y) / (2 * y))`;

val MAP_MAP = prove(
  ``!l f g. MAP f (MAP g l) = MAP (f o g) l``,
  Induct THEN SRW_TAC [][combinTheory.o_THM]);

val MAP2_MAP = prove(
  ``!l f g pad. MAP2 pad f (MAP g l) l = MAP (\x. f (g x) x) l``,
  Induct THEN SRW_TAC [][MAP2_def]);

val MAP_MAP2 = prove(
  ``!l f g h. MAP (\x. f (g x) (h x)) l = MAP2 0i f (MAP g l) (MAP h l)``,
  Induct THEN SRW_TAC [][MAP2_def]);

val equality_removal = store_thm(
  "equality_removal",
  ``!c x cs vs.
       0 < c /\ (c * x + sumc cs vs = 0) ==>
       ?s. x = ~(c + 1) * s + sumc (MAP (\x. modhat x (c + 1)) cs) vs``,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [INT_ADD_COMM] THEN
  SIMP_TAC (srw_ss()) [GSYM int_sub, INT_EQ_SUB_LADD, GSYM INT_NEG_LMUL] THEN
  CONV_TAC (BINDER_CONV (LHS_CONV (REWR_CONV INT_ADD_COMM))) THEN
  SIMP_TAC (srw_ss()) [GSYM INT_EQ_SUB_LADD, int_sub] THEN
  Q_TAC SUFF_TAC
     `(c + 1) int_divides sumc (MAP (\x. modhat x (c + 1)) cs) vs + ~x` THEN1
     PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
  Q_TAC SUFF_TAC
     `c * (c + 1) int_divides
        c * (sumc  (MAP (\x. modhat x (c+ 1)) cs) vs + ~x)` THEN1
     PROVE_TAC [INT_DIVIDES_MUL_BOTH, INT_LT_REFL] THEN
  CONV_TAC (RAND_CONV (SIMP_CONV bool_ss [INT_LDISTRIB, GSYM INT_NEG_RMUL,
                                          sumc_MULT, MAP_MAP,
                                          combinTheory.o_DEF])) THEN
  `~(c * x) = sumc cs vs` by
      FULL_SIMP_TAC (srw_ss()) [GSYM INT_EQ_SUB_LADD] THEN
  ASM_SIMP_TAC (srw_ss()) [sumc_ADD, MAP2_MAP, modhat_def, int_sub] THEN
  CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [INT_LDISTRIB,
                                             GSYM INT_ADD_ASSOC])) THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [INT_ADD_COMM])) THEN
  SIMP_TAC (srw_ss()) [GSYM INT_ADD_ASSOC] THEN
  SIMP_TAC (srw_ss()) [BETA_RULE
                         (Q.INST [`h` |-> `\x. x + c * x`]
                              (INST_TYPE [alpha |-> ``:int``]
                                         (SPEC_ALL MAP_MAP2)))] THEN
  SIMP_TAC (srw_ss()) [GSYM sumc_ADD, INT_NEG_RMUL] THEN

  `!f c l. MAP (\x:int. c * f x) l = MAP (\x. c * x) (MAP f l)`
     by SIMP_TAC (srw_ss()) [MAP_MAP, combinTheory.o_DEF] THEN
  POP_ASSUM (fn th =>
                CONV_TAC (RAND_CONV (LAND_CONV
                                       (LAND_CONV (HO_REWR_CONV th))))) THEN
  ASM_SIMP_TAC (srw_ss()) [GSYM sumc_MULT] THEN
  `!x c. x + c * x = (c + 1) * x`
    by SIMP_TAC (srw_ss()) [INT_RDISTRIB, INT_ADD_COMM] THEN
  ASM_REWRITE_TAC [GSYM sumc_MULT] THEN
  Q_TAC SUFF_TAC `~(c + 1 = 0) /\ c int_divides sumc cs vs` THEN1
    PROVE_TAC [INT_DIVIDES_MUL_BOTH, INT_MUL_COMM] THEN
  REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC (srw_ss()) [GSYM INT_EQ_SUB_LADD],
    PROVE_TAC [INT_DIVIDES, INT_MUL_COMM, INT_DIVIDES_NEG, INT_NEG_LMUL]
  ]);


val _ = export_theory();

