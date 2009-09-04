(*---------------------------------------------------------------------------
      Normalizers and equality provers for rings.
 ---------------------------------------------------------------------------*)

load "numRingLib"; open numRingLib;         (* Test on natural numbers *)

val ring_conv = NUM_RING_CONV o Parse.Term
val norm_conv = NUM_NORM_CONV o Parse.Term;

norm_conv ` 3*(9+7) : num `;
norm_conv `x+y+x : num`;
norm_conv `(a+b)*(a+b) : num`;
norm_conv `(b+a)*(b+a) : num`;
norm_conv `(a+b)*(a+b)*(a+b) : num`;
ring_conv `(a+b)*(a+b) = (b+a)*(b+a) : num`;


load "integerRingLib"; open integerRingLib; (* Test on integers *)

val ring_conv = INT_RING_CONV o Parse.Term;
val norm_conv = INT_NORM_CONV o Parse.Term;

norm_conv `~(3 * (9 - 7)) : int`;
norm_conv `x+y+x:int`;
norm_conv `(a+b)*(a+b) : int`;
norm_conv `(b+a)*(b+a) : int`;
norm_conv `(a+b)*(a+b)*(a+b) : int`;
ring_conv `(a+b)*(a+b) = (b+a)*(b+a) :int`;

ringLib.RING_NORM_CONV(--` (a-b)*(a+b) : int `--);
INT_NORM_CONV(--` (a-b)*(a+b) : int `--);

(*---------------------------------------------------------------------------
       bigger test: 8 squares
 ---------------------------------------------------------------------------*)

Count.apply ring_conv
   `(p1*p1+q1*q1+r1*r1+s1*s1+t1*t1+u1*u1+v1*v1+w1*w1)
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
    : int`;

Count.apply ring_conv
   `(p1*p1+q1*q1+r1*r1+s1*s1+t1*t1+u1*u1+v1*v1+w1*w1)
   *(p2*p2+q2*q2+r2*r2+s2*s2+t2*t2+u2*u2+v2*v2+w2*w2)

         =

    (((((((p1*p2-q1*q2)-r1*r2)-s1*s2)-t1*t2)-u1*u2)-v1*v2)-w1*w2)*
    (((((((p1*p2-q1*q2)-r1*r2)-s1*s2)-t1*t2)-u1*u2)-v1*v2)-w1*w2)
    +
    (((p1*q2+q1*p2+r1*s2-s1*r2+t1*u2)-u1*t2)-v1*w2+w1*v2)*
    (((p1*q2+q1*p2+r1*s2-s1*r2+t1*u2)-u1*t2)-v1*w2+w1*v2)
    +
    ((((p1*r2-q1*s2)+r1*p2+s1*q2+t1*v2+u1*w2)-v1*t2)-w1*u2)*
    ((((p1*r2-q1*s2)+r1*p2+s1*q2+t1*v2+u1*w2)-v1*t2)-w1*u2)
    +
    ((p1*s2+q1*r2-r1*q2+s1*p2+t1*w2-u1*v2+v1*u2-w1*t2)*
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
    : int`;


(*---------------------------------------------------------------------------
    Developer comments ...

    (with ternary comparison:)
    runtime: 41.240s,    gctime: 4.230s,     systime: 0.070s.

    (without)
    runtime: 56.330s,    gctime: 5.430s,     systime: 0.050s.
     (74s without functor application in ringLib)
    runtime: 84.580s,    gctime: 5.700s,     systime: 0.580s.
    runtime: 2710.160s,    gctime: 330.350s,     systime: 52.590s.
 ---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------
      Another example: sum of squares
 ---------------------------------------------------------------------------*)

open arithmeticTheory;

val sum_def =
 Define `(sum f 0 = 0n) /\ (sum f (SUC n) = sum f n + f (SUC n))`;

val lemma = Q.prove
(`!n:num. sum (\m. m * m) n * 6 = n * (n+1) * (2 * n + 1)`,
 Induct THEN RW_TAC arith_ss [sum_def,RIGHT_ADD_DISTRIB] THEN NUM_RING_TAC);

val sum_squares = Q.prove
(`!n:num. sum (\m. m * m) n  = (n*(n+1) * (2*n + 1)) DIV 6`,
 GEN_TAC THEN MATCH_MP_TAC (GSYM DIV_UNIQUE) THEN Q.EXISTS_TAC `0`
 THEN RW_TAC arith_ss [lemma]);
