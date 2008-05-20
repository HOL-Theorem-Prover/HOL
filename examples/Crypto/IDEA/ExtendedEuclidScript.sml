(* For interactive use
app load ["intLib"];
quietdec := true;
open pairTheory intLib integerTheory;
quietdec := false;
*)

open HolKernel Parse boolLib bossLib
     pairTheory intLib integerTheory;

val _ = new_theory "ExtendedEuclid";

val dec_def = 
 Define 
   `dec (r1:num, r2:num, u1:int, u2:int, v1:int, v2:int) = 
      if r1 < r2 
        then (r1, r2 - r1, u1, u2 - u1, v1, v2 - v1) 
        else (r1 - r2, r2, u1 - u2, u2, v1 - v2, v2)`;

val P_def = 
 Define 
   `P ((r1:num, r2:num, u1:int, u2:int, v1:int, v2:int), x:int, y:int) = 
       (int_of_num r1 = u1*x + v1*y) /\ (int_of_num r2 = u2*x + v2*y)`;

val decP_Lemma1 = Q.store_thm
("decP_Lemma1",
 `!n m. ~(n < m) ==> (& (n - m) = & n - & m)`,
 RW_TAC arith_ss [arithmeticTheory.NOT_LESS, INT_SUB]);

val decP_Lemma2 = Q.store_thm
("decP_Lemma2",
 `!r1:num r2:num u1:int u2:int v1:int v2:int x:int y:int. 
  ((& r1 = u1 * x + v1 * y) /\ 
   (& r2 = u2 * x + v2 * y) /\ ~(r1 < r2))
  ==>
   (& (r1 - r2) = (u1 - u2) * x + (v1 - v2) * y)`,
 RW_TAC arith_ss [INT_SUB_RDISTRIB, decP_Lemma1, INT_ADD2_SUB2]);

val decP_Lemma3 = Q.store_thm
("decP_Lemma3",
 `!n m. (m < n) ==> (& (n - m) = & n - & m)`,
 RW_TAC arith_ss [arithmeticTheory.LESS_IMP_LESS_OR_EQ, INT_SUB]);

val decP_Lemma4 = Q.store_thm
("decP_Lemma4",
 `!r1:num r2:num u1:int u2:int v1:int v2:int x:int y:int. 
  ((& r1 = u1 * x + v1 * y) /\ (& r2 = u2 * x + v2 * y) /\ (r1 < r2))==>(& (r2 - r1) = (u2 - u1) * x + (v2 - v1) * y)`,
 RW_TAC arith_ss [INT_SUB_RDISTRIB, decP_Lemma3, INT_ADD2_SUB2]);

val decP_Theorem = Q.store_thm
("decP_Theorem",
 `!r1 r2 u1 u2 v1 v2 x y. (P ((r1, r2, u1, u2, v1, v2), x, y)) 
    ==> (P (dec (r1, r2, u1, u2, v1, v2), x, y))`,
 RW_TAC arith_ss [dec_def, P_def, decP_Lemma2, decP_Lemma4]);

val (inv_def,inv_ind) = 
  Defn.tprove 
    (Hol_defn 
      "inv"
      `inv (r1, r2, u1, u2, v1, v2) =  
      if ((FST (r1, r2, u1, u2, v1, v2) = 1) \/ (FST (SND (r1, r2, u1, u2, v1, v2)) = 1) 
        \/ (FST (r1, r2, u1, u2, v1, v2) = 0) \/ (FST (SND (r1, r2, u1, u2, v1, v2)) = 0))   
        then (r1, r2, u1, u2, v1, v2)
        else inv (dec (r1, r2, u1, u2, v1, v2))`,    
   WF_REL_TAC `measure (\(a,b,c,d,e,f). a+b)` THEN RW_TAC arith_ss [dec_def]);

val _ = save_thm("inv_def", inv_def);
val _ = save_thm("inv_ind", inv_ind);

val invP_Lemma1 = Q.store_thm
("invP_Lemma1",
`!r1 r2 u1 u2 v1 v2 x y. (P ((r1, r2, u1, u2, v1, v2), x, y) 
  /\ ((FST (dec (r1,r2,u1,u2,v1,v2)) = 1) \/ (FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 1)
    \/ (FST (dec (r1,r2,u1,u2,v1,v2)) = 0) \/ (FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 0))) 
  ==> (inv (dec (r1,r2,u1,u2,v1,v2)) = dec (r1,r2,u1,u2,v1,v2))`, 
  RW_TAC arith_ss [dec_def] THEN RW_TAC arith_ss [inv_def]);

val invP_Lemma2 = Q.store_thm
("invP_Lemma2",
`!r1 r2 u1 u2 v1 v2 x y. (~((FST (dec (r1,r2,u1,u2,v1,v2)) = 1) \/ (FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 1)
    \/ (FST (dec (r1,r2,u1,u2,v1,v2)) = 0) \/ (FST (SND (dec (r1,r2,u1,u2,v1,v2))) = 0))) 
  ==> (inv (dec (r1,r2,u1,u2,v1,v2)) = inv (dec (dec (r1,r2,u1,u2,v1,v2))))`, 
  REWRITE_TAC [dec_def] THEN RW_TAC arith_ss [inv_def]);

val invP_Theorem = Q.store_thm
("invP_Theorem",
`!r1 r2 u1 u2 v1 v2 x y. (P ((r1, r2, u1, u2, v1, v2), x, y)) 
    ==> (P (inv (r1, r2, u1, u2, v1, v2), x, y))`,
  FULL_SIMP_TAC arith_ss [inv_def] THEN recInduct inv_ind THEN RW_TAC arith_ss [decP_Theorem]
  THENL [ASSUME_TAC invP_Lemma1 THEN RES_TAC THEN RW_TAC arith_ss [decP_Theorem],
         ASSUME_TAC invP_Lemma1 THEN RES_TAC THEN RW_TAC arith_ss [decP_Theorem],
         ASSUME_TAC invP_Lemma1 THEN RES_TAC THEN RW_TAC arith_ss [decP_Theorem],
         ASSUME_TAC invP_Lemma1 THEN RES_TAC THEN RW_TAC arith_ss [decP_Theorem],
         ASSUME_TAC decP_Theorem THEN RES_TAC THEN RES_TAC THEN 
         `inv (dec (r1,r2,u1,u2,v1,v2))=inv (dec (dec (r1,r2,u1,u2,v1,v2)))` by RES_TAC
         THENL [RW_TAC arith_ss [invP_Lemma2], RW_TAC arith_ss []]]);

(* A more general case, commented out to use a specific one.
val i16_Lemma1 = Q.store_thm
("i16_Lemma1",
`!x. P((x, 65537, 1, 0, 0, 1), (int_of_num x), (int_of_num 65537))`,
 RW_TAC arith_ss [P_def, INT_MUL_LZERO, INT_MUL_LID, INT_ADD]);
*)

val i16_Lemma1 = Q.store_thm
("i16_Lemma1",
`!r1. P((r1, 65537, 1, 0, 0, 1), (int_of_num r1), (int_of_num 65537))`,
 RW_TAC arith_ss [P_def, INT_MUL_LZERO, INT_MUL_LID, INT_ADD]);

val i16_Lemma2 = Q.store_thm
("i16_Lemma2",
`!x. P(inv(x, 65537, 1, 0, 0, 1), (int_of_num x), 65537)`,
 RW_TAC arith_ss [i16_Lemma1, invP_Theorem]);

val i16_Lemma3 = Q.store_thm
("i16_Lemma3",
`!a:int b:int c:int. ~(c = 0) ==> (((a + b * c) % c) = (a % c))`,
 FULL_SIMP_TAC arith_ss [int_mod] THEN ASSUME_TAC INT_MOD_COMMON_FACTOR THEN
 RW_TAC arith_ss [INT_ADD_DIV] THEN ASSUME_TAC INT_MOD_ID THEN
 RW_TAC arith_ss [INT_MUL_DIV, INT_DIV_ID, INT_MUL_RID, INT_RDISTRIB, INT_ADD2_SUB2] THEN
 `b * c - b * c = 0` by RES_TAC 
 THENL [`b * c = b * c` by DECIDE_TAC THEN RW_TAC arith_ss [INT_SUB_0], 
        RW_TAC arith_ss [INT_ADD_CALCULATE]]);

val i16_Lemma4 = Q.store_thm
("i16_Lemma4",
`!r1 r2 u1 u2 v1 v2 x y. (P ((r1, r2, u1, u2, v1, v2), & x, y) /\ ~(y = 0)) 
  ==> (((int_of_num (FST (r1, r2, u1, u2, v1, v2))) % y = (FST (SND (SND (r1, r2, u1, u2, v1, v2))) * & x) % y) /\
       ((int_of_num (FST (SND (r1, r2, u1, u2, v1, v2)))) % y = (FST (SND (SND (SND (r1, r2, u1, u2, v1, v2))))
       * & x) % y))`,
  FULL_SIMP_TAC arith_ss [] THEN RW_TAC arith_ss [P_def, i16_Lemma3]);

val i16_Lemma5 = Q.store_thm
("i16_Lemma5",
`!r1 r2 u1 u2 v1 v2.
      (FST (inv (r1,r2,u1,u2,v1,v2)) = 1) \/
      (FST (inv (r1,r2,u1,u2,v1,v2)) = 0) \/
      (FST (SND (inv (r1,r2,u1,u2,v1,v2))) = 1) \/
      (FST (SND (inv (r1,r2,u1,u2,v1,v2))) = 0)`,
recInduct inv_ind THEN RW_TAC arith_ss [] THEN RW_TAC arith_ss [inv_def]);

val ir1_def = Define `(ir1 x) = FST (inv (x, 65537, 1, 0, 0, 1))`;

val ir2_def = Define `(ir2 x) = FST (SND (inv (x, 65537, 1, 0, 0, 1)))`;

val i16_Lemma6 = Q.store_thm
("i16_Lemma6",
`!x. ((ir1 x) = 1) \/ ((ir1 x) = 0) \/ ((ir2 x) = 1) \/ ((ir2 x) = 0)`,
  RW_TAC arith_ss [ir1_def, ir2_def] THEN RW_TAC arith_ss [i16_Lemma5]);

val i16_Lemma7 = Q.store_thm
("i16_Lemma7",
`!r1 r2 u1 u2 v1 v2 x y. (P ((r1, r2, u1, u2, v1, v2), & x, y) /\ ~(y = 0)) 
  ==> (((int_of_num (FST (inv(r1, r2, u1, u2, v1, v2)))) % y = (FST (SND (SND (inv (r1, r2, u1, u2, v1, v2)))) * & x) % y) /\
       ((int_of_num (FST (SND (inv (r1, r2, u1, u2, v1, v2))))) % y = (FST (SND (SND (SND (inv (r1, r2, u1, u2, v1, v2)))))
       * & x) % y))`,
recInduct inv_ind THEN RW_TAC arith_ss [] THEN RW_TAC arith_ss [inv_def,i16_Lemma4] THEN
ASSUME_TAC decP_Theorem THEN RES_TAC THEN `~(r1 = 1) /\ ~(r2 = 1) /\ ~(r1 = 0) /\ ~(r2 = 0)` by DECIDE_TAC
THEN RW_TAC arith_ss []);

val iu1_def = Define `(iu1 x) = FST (SND (SND (inv (x, 65537, 1, 0, 0, 1))))`;

val iu2_def = Define `(iu2 x) = FST (SND (SND (SND (inv (x, 65537, 1, 0, 0, 1)))))`;

val i16_Lemma8 = Q.store_thm
("i16_Lemma8",
 `!x. ((int_of_num (ir1 x)) % 65537 = ((iu1 x) * (int_of_num x)) % 65537 ) /\
   ((int_of_num (ir2 x)) % 65537 = ((iu2 x) * (int_of_num x)) % 65537 )`,
FULL_SIMP_TAC arith_ss [ir1_def, ir2_def, iu1_def, iu2_def] THEN
STRIP_TAC THEN ASSUME_TAC i16_Lemma1 THEN
`~(65537i = 0)` by intLib.ARITH_TAC THEN RW_TAC arith_ss [i16_Lemma7]);

val i16_Lemma9 = Q.store_thm
("i16_Lemma9",
 `!x. (((iu1 x) * (int_of_num x)) % 65537 = 0) \/ (((iu1 x) * (int_of_num x)) % 65537 = 1) \/ 
   (((iu2 x) * (int_of_num x)) % 65537 = 0) \/ (((iu2 x) * (int_of_num x)) % 65537 = 1) `,
 `~(65537i = 0)` by intLib.ARITH_TAC THEN GEN_TAC THEN
 `(& (ir1 x) % 65537 = (iu1 x * & x) % 65537) /\
  (& (ir2 x) % 65537 = (iu2 x * & x) % 65537)` by RW_TAC arith_ss [i16_Lemma8] THEN
 `(ir1 x = 1) \/ (ir1 x = 0) \/ (ir2 x = 1) \/ (ir2 x = 0)` by RW_TAC arith_ss [i16_Lemma6] 
 THENL [`((ir1 x) MOD 65537 = 1)` by RW_TAC arith_ss [arithmeticTheory.LESS_MOD] THEN
        `& (ir1 x) % 65537 = & ((ir1 x) MOD 65537)` by METIS_TAC [INT_MOD],
        `((ir1 x) MOD 65537 = 0)` by RW_TAC arith_ss [arithmeticTheory.LESS_MOD] THEN
        `& (ir1 x) % 65537 = & ((ir1 x) MOD 65537)` by METIS_TAC [INT_MOD],
        `((ir2 x) MOD 65537 = 1)` by RW_TAC arith_ss [arithmeticTheory.LESS_MOD] THEN
        `& (ir2 x) % 65537 = & ((ir2 x) MOD 65537)` by METIS_TAC [INT_MOD],
        `((ir2 x) MOD 65537 = 0)` by RW_TAC arith_ss [arithmeticTheory.LESS_MOD] THEN
        `& (ir2 x) % 65537 = & ((ir2 x) MOD 65537)` by METIS_TAC [INT_MOD]
 ] THEN METIS_TAC []);

val i16_Lemma10 = Q.store_thm
("i16_Lemma10",
 `!x. (((int_of_num x) * (iu1 x)) % 65537 = 0) \/ (((int_of_num x) * (iu1 x)) % 65537 = 1) \/ 
   (((int_of_num x) * (iu2 x)) % 65537 = 0) \/ (((int_of_num x) * (iu2 x)) % 65537 = 1)`,
 GEN_TAC THEN `& x * iu1 x = iu1 x * & x` by RW_TAC arith_ss [INT_MUL_COMM] THEN
 `& x * iu2 x = iu2 x * & x` by RW_TAC arith_ss [INT_MUL_COMM] THEN METIS_TAC [i16_Lemma9]);

val () = export_theory();
