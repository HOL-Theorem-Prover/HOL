(*
load "ringLib";
load "integerTheory";
load "bossLib";
*)
local
open HolKernel Parse basicHol90Lib bossLib  integerTheory ringTheory;
in
infix THEN THENL THENC o;
infix 8 by;


val ARW_TAC = RW_TAC arith_ss;

val int_is_ring = prove(--`is_ring (ring int_0 int_1 $+ $* $~)`--,
ARW_TAC [ is_ring_def, ring_accessors, INT_0, INT_1,
          INT_ADD_RINV, INT_RDISTRIB,
          INT_ADD_ASSOC, INT_MUL_ASSOC, INT_ADD_LID, INT_MUL_LID] THEN
MAP_FIRST MATCH_ACCEPT_TAC [ INT_ADD_SYM, INT_MUL_SYM ]);

val num_to_int = --`&`--;
val int_0 = --`int_0`--;
val int_1 = --`int_1`--;

fun is_closed_int t =
  mem t [int_0,int_1] orelse
    ((is_comb t) andalso (rator t)=num_to_int) andalso (is_numeral (rand t));


val INT_ADD_NEG2 = 
  GSYM(REWRITE_RULE[int_sub,INT_ADD_LID] (SPECL[int_0,int_0]INT_ADD2_SUB2));


val NAT_RDIFF = prove(--`!n m. &n + ~&m = if n<m then ~&(m-n) else &(n-m) `--,
REPEAT GEN_TAC THEN
ARW_TAC [GSYM int_sub,INT_EQ_SUB_RADD,INT_ADD,INT_INJ] THEN
ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
MATCH_MP_TAC EQ_SYM THEN
ARW_TAC [GSYM int_sub,INT_EQ_SUB_RADD,INT_ADD,INT_INJ]);

val NAT_LDIFF = ONCE_REWRITE_RULE[INT_ADD_SYM] NAT_RDIFF;


val INT_EQ_OPP = prove(--`!n m. (&n = ~&m) = (n+m = 0)`--,
ARW_TAC [GSYM INT_SUB_LZERO, INT_EQ_SUB_LADD, INT_ADD, INT_INJ]);


(* equations to put any expression build on + * ~ & int_0 int_1
   under the (unique) following forms:  &n  or ~(&n) *)
val intr_plus = prove(
--`    ( &n +  &m = &(n+m))
    /\ (~&n +  &m = if m<n then ~&(n-m) else &(m-n))
    /\ ( &n + ~&m = if n<m then ~&(m-n) else &(n-m))
    /\ (~&n + ~&m = ~&(n+m)) `--,
ARW_TAC [INT_ADD,NAT_RDIFF,NAT_LDIFF, GSYM INT_NEG_ADD])
;

val intr_mult = prove(
--`    ( &n *  &m =  &(n*m))
    /\ (~&n *  &m = ~&(n*m))
    /\ ( &n * ~&m = ~&(n*m))
    /\ (~&n * ~&m =  &(n*m)) `--,
ARW_TAC [INT_MUL,GSYM INT_NEG_LMUL, GSYM INT_NEG_RMUL,INT_NEGNEG])
;

val intr_opp = prove(
--` (~~n = n:int) /\ (~0 = 0) `--,
ARW_TAC [INT_NEGNEG, INT_NEG_0]);


val intr_eq = prove(
--`   (( &n =  &m) = (n=m)) 
   /\ (( &n = ~&m) = (n+m=0))
   /\ ((~&n =  &m) = (n+m=0))
   /\ ((~&n = ~&m) = (n=m)) `--,
ARW_TAC [INT_INJ,INT_NEG_EQ, INT_EQ_OPP, INT_NEGNEG]);


(* from num_ring... *)
local open numeralTheory
in
val REFL_EQ_0 = prove(--` ((ALT_ZERO = ALT_ZERO)=T) /\ ((0 = 0:num) = T) `--,
ARW_TAC []);

val numeral_rewrites =
  [ REFL_EQ_0, numeral_distrib, numeral_eq, numeral_suc, numeral_iisuc,
    numeral_add, numeral_mult, iDUB_removal ];

val int_rewrites =
    [ intr_plus, intr_mult, intr_opp, INT_0, INT_1,
      numeral_lt, numeral_sub, iSUB_THM, (* to simplify plus *)
      intr_eq ];
end;

val {EqConv=INT_RING_CONV_raw, NormConv=INT_NORM_CONV_raw,...} =
  ringLib.declare_ring { Name = "int",
                         Theory = int_is_ring,
			 Const = is_closed_int,
			 Rewrites = int_rewrites@numeral_rewrites }
;


(* dealing with subtraction: *)
val PRE_CONV = REWRITE_CONV[int_sub]

val POST_CONV =
  REWRITE_CONV[GSYM INT_NEG_MINUS1] THENC
  REWRITE_CONV[GSYM INT_NEG_LMUL, GSYM int_sub]
;

val INT_RING_CONV = PRE_CONV THENC INT_RING_CONV_raw THENC POST_CONV;
val INT_NORM_CONV = PRE_CONV THENC INT_NORM_CONV_raw THENC POST_CONV;

end;

(*
val ring_conv = INT_RING_CONV;
val norm_conv = INT_NORM_CONV;

norm_conv(--` ~( 3 * (9 - 7)) `--);
*)

(*
norm_conv(--`x+y+x:int`--);
norm_conv(--`(a+b)*(a+b):int`--);
norm_conv(--`(b+a)*(b+a):int`--);
norm_conv(--`(a+b)*(a+b)*(a+b):int`--);
ring_conv(--`(a+b)*(a+b) = (b+a)*(b+a):int`--);


INT_NORM_CONV_raw(--` (a-b)*(a+b):int `--);
INT_NORM_CONV    (--` (a-b)*(a+b):int `--);


*)
(*
val pb = --`

(p1*p1+q1*q1+r1*r1+s1*s1+t1*t1+u1*u1+v1*v1+w1*w1)
*(p2*p2+q2*q2+r2*r2+s2*s2+t2*t2+u2*u2+v2*v2+w2*w2)

=

(p1*p2-q1*q2-r1*r2-s1*s2-t1*t2-u1*u2-v1*v2-w1*w2)*
(p1*p2-q1*q2-r1*r2-s1*s2-t1*t2-u1*u2-v1*v2-w1*w2)
+
(p1*q2+q1*p2+r1*s2-s1*r2+t1*u2-u1*t2-v1*w2+w1*v2)*
(p1*q2+q1*p2+r1*s2-s1*r2+t1*u2-u1*t2-v1*w2+w1*v2)
+
(p1*r2-q1*s2+r1*p2+s1*q2+t1*v2+u1*w2-v1*t2-w1*u2)*
(p1*r2-q1*s2+r1*p2+s1*q2+t1*v2+u1*w2-v1*t2-w1*u2)
+
(p1*s2+q1*r2-r1*q2+s1*p2+t1*w2-u1*v2+v1*u2-w1*t2)*
(p1*s2+q1*r2-r1*q2+s1*p2+t1*w2-u1*v2+v1*u2-w1*t2)
+
(p1*t2-q1*u2-r1*v2-s1*w2+t1*p2+u1*q2+v1*r2+w1*s2)*
(p1*t2-q1*u2-r1*v2-s1*w2+t1*p2+u1*q2+v1*r2+w1*s2)
+
(p1*u2+q1*t2-r1*w2+s1*v2-t1*q2+u1*p2-v1*s2+w1*r2)*
(p1*u2+q1*t2-r1*w2+s1*v2-t1*q2+u1*p2-v1*s2+w1*r2)
+
(p1*v2+q1*w2+r1*t2-s1*u2-t1*r2+u1*s2+v1*p2-w1*q2)*
(p1*v2+q1*w2+r1*t2-s1*u2-t1*r2+u1*s2+v1*p2-w1*q2)
+
(p1*w2-q1*v2+r1*u2+s1*t2-t1*s2-u1*r2+v1*q2+w1*p2)*
(p1*w2-q1*v2+r1*u2+s1*t2-t1*s2-u1*r2+v1*q2+w1*p2)
:int
`--;

val t1 = lhs pb;


- time ring_conv pb;
(with ternary comparison:)
runtime: 41.550s,    gctime: 4.780s,     systime: 0.040s.

runtime: 56.330s,    gctime: 5.430s,     systime: 0.050s.
 (74s without functor application in ringLib)
runtime: 84.580s,    gctime: 5.700s,     systime: 0.580s.
runtime: 2710.160s,    gctime: 330.350s,     systime: 52.590s.

*)
