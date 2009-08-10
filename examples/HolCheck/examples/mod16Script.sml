open HolKernel Parse boolLib bossLib

val _ = new_theory "mod16"; (* FIXME: functorize this *)

open pairTheory
open metisLib

val xor_def = Define `xor x y = (x \/ y) /\ ~(x=y)`

val MOD16_ONE_def = Define `MOD16_ONE (v3:bool,v2:bool,v1:bool,v0:bool) = (F,F,F,T)`
val MOD16_IS_ONE_def = Define `MOD16_IS_ONE (v3:bool,v2:bool,v1:bool,v0:bool) = ~v3 /\ ~v2 /\ ~v1 /\ v0`

val MOD16_INC_def = Define `MOD16_INC (v3,v2,v1,v0) = (xor (v0 /\ v1 /\ v2) v3,xor (v0 /\ v1) v2,xor v0 v1,~v0)`

val MOD16_INC8_def = Define `MOD16_INC8 (v3,v2,v1,v0) = (F,xor (v0 /\ v1) v2,xor v0 v1,~v0)`

val MOD16_INC4_def = Define `MOD16_INC4 (v3,v2,v1,v0) = (F,F,xor v0 v1,~v0)`

val MOD16_HOLD_def = Define `MOD16_HOLD (v3,v2,v1,v0) = (v3,v2,v1,v0)`

val MOD16_ZERO_def = Define `MOD16_ZERO (v3:bool,v2:bool,v1:bool,v0:bool) = (F,F,F,F)`
val MOD16_IS_ZERO_def = Define `MOD16_IS_ZERO (v3:bool,v2:bool,v1:bool,v0:bool) = ~v3 /\ ~v2 /\ ~v1 /\ ~v0`

val MOD16_IS_16_def = Define `MOD16_IS_16 (v3:bool,v2:bool,v1:bool,v0:bool) = v3 /\ v2 /\ v1 /\ v0`

val MOD16_IS_4_def = Define `MOD16_IS_4 (v3:bool,v2:bool,v1:bool,v0:bool) = ~v3 /\ v2 /\ ~v1 /\ ~v0`

val MOD16_EQ_def = `MOD16_EQ (v3:bool,v2:bool,v1:bool,v0:bool) (w3:bool,w2:bool,w1:bool,w0:bool) =
(v3=w3) /\ (v2=w2) /\ (v1=w1) /\ (v0=w0)`;

val dest_mod16_tup = save_thm("dest_mod16_tup",prove(``!v3 v2 v1 v0 v3' v2' v1' v0'. ((v3',v2',v1',v0')=(v3,v2,v1,v0))
= (v3'=v3) /\  (v2'=v2) /\  (v1'=v1) /\  (v0'=v0)``,METIS_TAC [PAIR_EQ]))

val dest_mod16 = save_thm("dest_mod16",prove(``!P Q v3 v2 v1 v0 v3' v2' v1' v0'. (P (v3',v2',v1',v0')= Q (v3,v2,v1,v0))
=  (FST (P (v3',v2',v1',v0')) = FST (Q (v3,v2,v1,v0))) /\
   (FST (SND (P (v3',v2',v1',v0'))) = (FST (SND (Q (v3,v2,v1,v0))))) /\
   (FST (SND (SND (P (v3',v2',v1',v0')))) = (FST (SND (SND (Q (v3,v2,v1,v0)))))) /\
   (SND (SND (SND (P (v3',v2',v1',v0')))) = (SND (SND (SND (Q (v3,v2,v1,v0))))))``,
 METIS_TAC [PAIR_FST_SND_EQ]))

val dest_mod16r = save_thm("dest_mod16r",prove(``!Q v3 v2 v1 v0 v3' v2' v1' v0'. ((v3',v2',v1',v0')= Q (v3,v2,v1,v0))
=  (FST ((v3',v2',v1',v0')) = FST (Q (v3,v2,v1,v0))) /\
   (FST (SND ((v3',v2',v1',v0'))) = (FST (SND (Q (v3,v2,v1,v0))))) /\
   (FST (SND (SND ((v3',v2',v1',v0')))) = (FST (SND (SND (Q (v3,v2,v1,v0)))))) /\
   (SND (SND (SND ((v3',v2',v1',v0')))) = (SND (SND (SND (Q (v3,v2,v1,v0))))))``,
 METIS_TAC [PAIR_FST_SND_EQ]))

val dest_mod16r2 = save_thm("dest_mod16r2",prove(``!Q v3 v2 v1 v0 . ((v3,v2,v1,v0)= Q)
=  (FST ((v3,v2,v1,v0)) = FST Q) /\
   (FST (SND ((v3,v2,v1,v0))) = (FST (SND Q))) /\
   (FST (SND (SND ((v3,v2,v1,v0)))) = (FST (SND (SND Q)))) /\
   (SND (SND (SND ((v3,v2,v1,v0)))) = (SND (SND (SND Q))))``,
 METIS_TAC [PAIR_FST_SND_EQ]))

val FST_COND = save_thm("FST_COND",prove(``!c p1 p2. FST (if c then p1 else p2) = if c then FST p1 else FST p2``,METIS_TAC [FST]))
val SND_COND = save_thm("SND_COND",prove(``!c p1 p2. SND (if c then p1 else p2) = if c then SND p1 else SND p2``,METIS_TAC [SND]))

val MOD16_FORALL_EXPAND16 = save_thm("MOD16_FORALL_EXPAND16",prove(``!P. ((!n. n<16 ==> P n) = P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\ P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15)``,
GEN_TAC THEN EQ_TAC THENL [
SIMP_TAC arith_ss [],
REPEAT STRIP_TAC
THEN METIS_TAC [DECIDE ``n<8 ==> ((n=0) \/ (n=1) \/  (n=2) \/ (n=3) \/  (n=4) \/ (n=5) \/  (n=6) \/ (n=7))``,DECIDE ``n>=8 /\ n<16 ==> ((n=8) \/ (n=9) \/  (n=10) \/ (n=11) \/  (n=12) \/ (n=13) \/  (n=14) \/ (n=15))``,DECIDE ``n<16 ==> (n<8 \/ (n>=8 /\ n<16))``]
])); (*intLib.COOPER_CONV is much faster than DECIDE for this; but who wants to mess around with intLib*)

val MOD16_FORALL_EXPAND8 = save_thm("MOD16_FORALL_EXPAND8",prove(``!P. ((!n. n<8 ==> P n) = P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7)``,
GEN_TAC THEN EQ_TAC THENL [
SIMP_TAC arith_ss [],
REPEAT STRIP_TAC
THEN METIS_TAC [DECIDE ``n<8 ==> ((n=0) \/ (n=1) \/  (n=2) \/ (n=3) \/ (n=4) \/ (n=5) \/  (n=6) \/ (n=7))``]
]));

val MOD16_FORALL_EXPAND4 = save_thm("MOD16_FORALL_EXPAND4",prove(``!P. ((!n. n<4 ==> P n) = P 0 /\ P 1 /\ P 2 /\ P 3)``,
GEN_TAC THEN EQ_TAC THENL [
SIMP_TAC arith_ss [],
REPEAT STRIP_TAC
THEN METIS_TAC [DECIDE ``n<4 ==> ((n=0) \/ (n=1) \/  (n=2) \/ (n=3))``]
]));

val MOD16_PROJ_def = Define `MOD16_PROJ (b3,b2,b1,b0) i = if i = 0 then b0 else if i=1 then b1 else if i=2 then b2 else b3`

val N2B'_defn = Hol_defn "MOD16_N2B'"
`MOD16_N2B' n k (b3,b2,b1,b0) =
    if k=0 then
	if n=1 then b0 else ~b0
    else (if n >= 2**k then MOD16_PROJ (b3,b2,b1,b0) k else ~(MOD16_PROJ (b3,b2,b1,b0) k)) /\
	MOD16_N2B' (if n >= 2**k then n-(2**k) else n) (k-1) (b3,b2,b1,b0)`;

val (MOD16_N2B'_def,N2B'_ind) = Defn.tprove(N2B'_defn,WF_REL_TAC `measure (FST o SND)`);
val _ = save_thm("MOD16_N2B'_def",MOD16_N2B'_def)

val MOD16_N2B_def = Define `MOD16_N2B n (b3,b2,b1,b0) = MOD16_N2B' n 3 (b3,b2,b1,b0)`

val MOD16_N2B_15 = save_thm("MOD16_N2B_15",prove(``!b3 b2 b0 b1. MOD16_N2B 15 (b3,b2,b1,b0) = b3 /\ b2 /\ b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_14 = save_thm("MOD16_N2B_14",prove(``!b3 b2 b0 b1. MOD16_N2B 14 (b3,b2,b1,b0) = b3 /\ b2 /\ b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_13 = save_thm("MOD16_N2B_13",prove(``!b3 b2 b0 b1. MOD16_N2B 13 (b3,b2,b1,b0) = b3 /\ b2 /\ ~b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_12 = save_thm("MOD16_N2B_12",prove(``!b3 b2 b0 b1. MOD16_N2B 12 (b3,b2,b1,b0) = b3 /\ b2 /\ ~b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_11 = save_thm("MOD16_N2B_11",prove(``!b3 b2 b0 b1. MOD16_N2B 11 (b3,b2,b1,b0) = b3 /\ ~b2 /\ b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_10 = save_thm("MOD16_N2B_10",prove(``!b3 b2 b0 b1. MOD16_N2B 10 (b3,b2,b1,b0) = b3 /\ ~b2 /\ b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_9 = save_thm("MOD16_N2B_9",prove(``!b3 b2 b0 b1. MOD16_N2B 9 (b3,b2,b1,b0) = b3 /\ ~b2 /\ ~b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_8 = save_thm("MOD16_N2B_8",prove(``!b3 b2 b0 b1. MOD16_N2B 8 (b3,b2,b1,b0) = b3 /\ ~b2 /\ ~b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_7 = save_thm("MOD16_N2B_7",prove(``!b3 b2 b0 b1. MOD16_N2B 7 (b3,b2,b1,b0) = ~b3 /\ b2 /\ b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_6 = save_thm("MOD16_N2B_6",prove(``!b3 b2 b0 b1. MOD16_N2B 6 (b3,b2,b1,b0) = ~b3 /\ b2 /\ b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_5 = save_thm("MOD16_N2B_5",prove(``!b3 b2 b0 b1. MOD16_N2B 5 (b3,b2,b1,b0) = ~b3 /\ b2 /\ ~b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_4 = save_thm("MOD16_N2B_4",prove(``!b3 b2 b0 b1. MOD16_N2B 4 (b3,b2,b1,b0) = ~b3 /\ b2 /\ ~b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_3 = save_thm("MOD16_N2B_3",prove(``!b3 b2 b0 b1. MOD16_N2B 3 (b3,b2,b1,b0) = ~b3 /\ ~b2 /\ b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_2 = save_thm("MOD16_N2B_2",prove(``!b3 b2 b0 b1. MOD16_N2B 2 (b3,b2,b1,b0) = ~b3 /\ ~b2 /\ b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_1 = save_thm("MOD16_N2B_1",prove(``!b3 b2 b0 b1. MOD16_N2B 1 (b3,b2,b1,b0) = ~b3 /\ ~b2 /\ ~b1 /\ b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));
val MOD16_N2B_0 = save_thm("MOD16_N2B_0",prove(``!b3 b2 b0 b1. MOD16_N2B 0 (b3,b2,b1,b0) = ~b3 /\ ~b2 /\ ~b1 /\ ~b0``,
SIMP_TAC arith_ss [MOD16_N2B_def,MOD16_N2B'_def,MOD16_PROJ_def]));

val _ = export_theory();