open HolKernel Parse boolLib bossLib;
open integerTheory EVAL_ringTheory hurdUtils normalizerTheory;

val _ = new_theory "integerRing";
val _ = ParseExtras.temp_loose_equality()

val ARW_TAC = RW_TAC arith_ss;

val int_is_ring = store_thm
    ("int_is_ring",
     “is_ring (ring int_0 int_1 $+ $* $~)”,
ARW_TAC [ is_ring_def, ring_accessors, INT_0, INT_1,
          INT_ADD_RINV, INT_RDISTRIB,
          INT_ADD_ASSOC, INT_MUL_ASSOC, INT_ADD_LID, INT_MUL_LID] THEN
MAP_FIRST MATCH_ACCEPT_TAC [ INT_ADD_SYM, INT_MUL_SYM ]);

val int_ring_thms =
  EVAL_ringLib.store_ring { Name = "int", Theory = int_is_ring };

(* equations to put any expression build on + * ~ & int_0 int_1
   under the (unique) following forms:  &n  or ~&n *)
val int_calculate = store_thm
    ("int_calculate",
     “    ( &n +  &m = &(n+m))
         /\ (~&n +  &m = if n<=m then &(m-n) else ~&(n-m))
         /\ ( &n + ~&m = if m<=n then &(n-m) else ~&(m-n))
         /\ (~&n + ~&m = ~&(n+m))

         /\ ( &n *  &m =  &(n*m))
         /\ (~&n *  &m = ~&(n*m))
         /\ ( &n * ~&m = ~&(n*m))
         /\ (~&n * ~&m =  &(n*m))

         /\ (( &n =  &m) = (n=m))
         /\ (( &n = ~&m) = (n=0)/\(m=0))
         /\ ((~&n =  &m) = (n=0)/\(m=0))
         /\ ((~&n = ~&m) = (n=m))

         /\ (~~x = x : int)
         /\ (~0 = 0 : int)   ”,
REWRITE_TAC [INT_ADD_CALCULATE,INT_MUL_CALCULATE,INT_EQ_CALCULATE]);


(* Note: AND_CLAUSES is not lazy *)
local open numeralTheory
in
val int_rewrites = save_thm("int_rewrites", LIST_CONJ
  [ int_calculate, INT_0, INT_1,
    numeral_lt, numeral_lte, numeral_sub, iSUB_THM, AND_CLAUSES ]);
end;

Triviality INT_POLY_CONV_sth:
  (!x y z. x + (y + z) = (x + y) + z :int) /\
  (!x y. x + y = y + x :int) /\
  (!x. &0 + x = x :int) /\
  (!x y z. x * (y * z) = (x * y) * z :int) /\
  (!x y. x * y = y * x :int) /\
  (!x. &1 * x = x :int) /\
  (!(x :int). &0 * x = &0) /\
  (!x y z. x * (y + z) = x * y + x * z :int) /\
  (!(x :int). x ** 0 = &1) /\
  (!(x :int) n. x ** (SUC n) = x * (x ** n))
Proof
  REWRITE_TAC [INT_POW, INT_ADD_ASSOC, INT_MUL_ASSOC, INT_ADD_LID,
    INT_MUL_LZERO, INT_MUL_LID, INT_LDISTRIB] THEN
  REWRITE_TAC [Once INT_ADD_SYM, Once INT_MUL_SYM]
QED

Theorem INT_POLY_CONV_sth = MATCH_MP SEMIRING_PTHS INT_POLY_CONV_sth;

Theorem INT_POLY_CONV_rth:
  (!x. -x = -(&1) * x :int) /\
  (!x y. x - y = x + -(&1) * y :int)
Proof
  REWRITE_TAC [INT_MUL_LNEG, INT_MUL_LID, int_sub]
QED

Theorem INT_INTEGRAL:
  (!(x :int). &0 * x = &0) /\
  (!x y (z :int). (x + y = x + z) <=> (y = z)) /\
  (!w x y (z :int). (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))
Proof
  REWRITE_TAC[INT_MUL_LZERO, INT_EQ_LADD] THEN
  ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN
  REWRITE_TAC[GSYM INT_ENTIRE] THEN
  rpt GEN_TAC \\
  Suff ‘w * y + x * z - (w * z + x * y) = (w - x) * (y - z :int)’
  >- (Rewr' >> REWRITE_TAC []) \\
  REWRITE_TAC [INT_ADD2_SUB2] \\
  REWRITE_TAC [GSYM INT_SUB_LDISTRIB] \\
  ‘x * (z - y) = -x * (y - z :int)’
    by (REWRITE_TAC [INT_MUL_LNEG, INT_SUB_LDISTRIB, INT_NEG_SUB]) \\
  POP_ORW \\
  REWRITE_TAC [GSYM INT_RDISTRIB, GSYM int_sub]
QED

val _ = export_theory();
