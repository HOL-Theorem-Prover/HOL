(* ========================================================================= *)
(* File Name: smart_gridScript.sml                                           *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Dependability Analysis of Smart Grids                 *)
(*                 using Theorem Proving                                     *)
(*                                                                           *)
(*                HOL4-Kananaskis                                            *)
(*                                                                           *)
(*              Author :  Waqar Ahmad                                        *)
(*                                                                           *)
(*          School of Electrical Engineering and Computer Sciences (SEECS)   *)
(*          National University of Sciences and Technology (NUST), PAKISTAN  *)
(*                                                                           *)
(*                                                                           *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;

open limTheory arithmeticTheory realTheory prim_recTheory real_probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite extra_pred_setTools
     util_probTheory extrealTheory real_measureTheory real_lebesgueTheory real_sigmaTheory
     satTheory numTheory;

open RBDTheory FT_deepTheory VDCTheory ASN_gatewayTheory;

val _ = new_theory "smart_grid";

(*--------------------*)
val op by = BasicProvers.byA;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)

(*------------------------------------------------------*)
Definition in_events_def :
in_events p L = (!x. MEM x L ==>  x IN events p)
End
(*------------------------------------------------------*)
Definition not_null_def :
not_null L = (!x. MEM x L ==> ~NULL x)
End
(*------------------------------------------------------*)
Definition in_events_k_out_n_def :
in_events_k_out_n p X n = ((\x. PREIMAGE X {Normal(&x)}) IN ((count (SUC n)) -> events p))
End
(*------------------------------------------------------*)
Definition k_out_n_event_def :
k_out_n_event p X k n = PREIMAGE X (BIGUNION {{Normal (&x)} | k <= x /\ x < SUC n})
End
(*------------------------------------------------------*)
Definition binomial_distr_def :
binomial_distr p X n pr = (!x. distribution p X {Normal (&x)} =
        &binomial n x * pr pow x * (1 - pr) pow (n - x))
End

(*----------------casc_series_RBD_def------------------------*)
Definition casc_series_RBD_def :
casc_series_RBD p PIED ESW_list CIED t =
 rbd_struct p (series (rbd_list (rel_event_list p
                        ([PIED]++ESW_list++[CIED]) t)))
End

(*----------------rel_casc_seriesRBD------------------------*)
Theorem rel_casc_seriesRBD :
!p t PIED ESW_list CIED C_PIED C_ESW_list C_CIED.
              (0 <= t) /\
              prob_space p /\
              ~NULL ESW_list /\
              exp_dist_list p ([PIED]++ESW_list++[CIED])
                              ([C_PIED]++C_ESW_list++[C_CIED])  /\
              (LENGTH C_ESW_list = LENGTH ESW_list) /\
              mutual_indep p
                (rel_event_list p ([PIED]++ESW_list++[CIED]) t) /\
              (!x.
                   MEM x (rel_event_list p ([PIED]++ESW_list++[CIED]) t) ==>
                   x IN events p) ==>
               (prob p (casc_series_RBD p PIED ESW_list CIED t) =
                list_prod
                 (exp_func_list ([C_PIED]++C_ESW_list++[C_CIED]) t))
Proof
RW_TAC std_ss[casc_series_RBD_def]
>> DEP_REWRITE_TAC[series_struct_thm]
>> RW_TAC std_ss[]
>- (RW_TAC list_ss[rel_event_list_def])
>> MATCH_MP_TAC rel_prod_series_rbd_exp_dist
>> RW_TAC list_ss[]
QED

(*----------------redund_star_ring_RBD------------------------*)
Definition redund_star_ring_RBD_def :
redund_star_ring_RBD p PIED list_ESW_list CIED t =
 rbd_struct p
   ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
               ([[PIED]]++list_ESW_list++[[CIED]]))
End

(*---------------------------------------*)
Theorem len_EL_lem1 :
!h1 h2 c1 c2 L C n.
     (LENGTH L = LENGTH C) /\
     (n < LENGTH L + 2) /\
     (!n.
        (n < LENGTH L) /\ (n < LENGTH C) ==>
        (LENGTH (EL n L) = LENGTH (EL n C))) ==>
          (LENGTH (EL n ([h1]::(L ++ [[h2]]))) =
     LENGTH (EL n ([c1]::(C ++ [[c2]]))))
Proof
NTAC 4 (GEN_TAC)
>> Induct
>- (RW_TAC list_ss[]
   >> FULL_SIMP_TAC list_ss[LENGTH_NIL_SYM]
   >> Cases_on `n`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[]
   >> POP_ASSUM MP_TAC
   >> ONCE_ASM_REWRITE_TAC[TWO]
   >> FULL_SIMP_TAC arith_ss[]
   >> Cases_on `n'`
   >- (RW_TAC list_ss[])
   >> FULL_SIMP_TAC arith_ss[])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[]
>> Cases_on `n`
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[]
>> Cases_on `n'`
>- (RW_TAC list_ss[]
   >> (FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC))
   >> RW_TAC list_ss[])
>> RW_TAC list_ss[]
>> (FIRST_X_ASSUM (Q.SPECL_THEN [`C'`,`SUC n`] MP_TAC))
>> RW_TAC list_ss[]
>> (`(!n'. n' < LENGTH C' ==> (LENGTH (EL n' L) = LENGTH (EL n' C')))` by RW_TAC list_ss[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n'`] MP_TAC)
   >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
QED
(*----------------rel_redund_star_ringRBD------------------------*)
Theorem rel_redund_star_ringRBD :
!p (t:real)  PIED list_ESW_list CIED C_PIED C_list_ESW_list C_CIED.
        (!z. MEM z list_ESW_list  ==>  ~NULL z) /\
         (0 <=  (t:real)) /\ prob_space p /\
         (!x'.
            MEM x' (FLAT ((two_dim_rel_event_list p
                ([[PIED]]++list_ESW_list++[[CIED]])  t))) ==>
            (x' IN events p)) /\
         (mutual_indep p (FLAT (two_dim_rel_event_list p ([[PIED]]++list_ESW_list++[[CIED]]) t))) /\
         (LENGTH C_list_ESW_list = LENGTH list_ESW_list) /\
         (!n.
              (n < LENGTH list_ESW_list) /\ (n < LENGTH C_list_ESW_list) ==>
              (LENGTH (EL n list_ESW_list) = LENGTH (EL n C_list_ESW_list))) /\
         two_dim_exp_dist_list p ([[PIED]]++list_ESW_list++[[CIED]])
                                 ([[C_PIED]]++C_list_ESW_list++[[C_CIED]]) ==>
           (prob p (redund_star_ring_RBD p PIED list_ESW_list CIED t) =
           (list_prod of
                 (\a. 1 - list_prod (one_minus_list (exp_func_list a t))))
                      ([[C_PIED]]++C_list_ESW_list++[[C_CIED]]))
Proof
RW_TAC std_ss[redund_star_ring_RBD_def]
>> DEP_REWRITE_TAC[rbd_virtual_cloud_server_alt_form]
>> RW_TAC std_ss[]
>> MATCH_MP_TAC rel_series_parallel_RBD_exp_dist_fail_rate
>> RW_TAC list_ss[]
>- (RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC list_ss[]
>> MATCH_MP_TAC len_EL_lem1
>> RW_TAC std_ss[]
QED

(*--------G1_FT------------------------------*)

Definition G1_FT_def :
G1_FT p t SW1 L1_220 L2_220 L3_220 L4_220 =
AND (gate_list (fail_event_list p [SW1;L1_220;L2_220;L3_220;L4_220] t))
End


(*--------G2_FT------------------------------*)

Definition G2_FT_def :
G2_FT p t SW1 L1_220 L2_220 L3_220 L4_220 =
AND (gate_list (fail_event_list p [SW1;L1_220;L2_220;L3_220;L4_220] t))
End


(*--------G3_FT------------------------------*)

Definition G3_FT_def :
G3_FT p t SW2 T1_220 T2_220 BUS_220 SS_220 =
AND (gate_list (fail_event_list p [SW2;T1_220;T2_220;BUS_220;SS_220] t))
End


(*--------G4_FT------------------------------*)

Definition G4_FT_def :
G4_FT p t SW2 T1_220 T2_220 BUS_220 SS_220 =
AND (gate_list (fail_event_list p [SW2;T1_220;T2_220;BUS_220;SS_220] t))
End

(*-----------SABP_FT----------------------*)
Definition SABP_FT_def :
SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 =
FTree p (AND [OR [G1_FT p t SW1 L1_220 L2_220 L3_220 L4_220;
                 G2_FT p t SW1 L1_220 L2_220 L3_220 L4_220];
              OR [G3_FT p t SW2 T1_220 T2_220 BUS_220 SS_220;
                 G4_FT p t SW2 T1_220 T2_220 BUS_220 SS_220]])
End

(*---------------------------------*)
Theorem SABP_FT_alt_form :
!A B C D. (A UNION B) INTER (C UNION D) = (A INTER C) UNION (A INTER D) UNION (B INTER C) UNION (B INTER D)
Proof
RW_TAC std_ss[]
>> SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
>> METIS_TAC[]
QED

(*---------------------------------*)
Theorem SABP_FT_alt_form1 :
!p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220.
prob_space p ==>
(SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 =
rbd_struct p ((parallel of (\a. series (rbd_list a)))
              (list_fail_event_list p
                [[SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220];
                 [SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220];
                 [SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220];
                 [SW1;L1_220;L2_220;L3_220;L4_220;SW2;T1_220;T2_220;BUS_220;SS_220]] t)))
Proof
RW_TAC std_ss[of_DEF,o_THM]
>> RW_TAC list_ss[SABP_FT_def,FTree_def]
>> PSET_TAC[]
>> RW_TAC list_ss[list_fail_event_list_def,fail_event_list_def,rbd_list_def,rbd_struct_def,G1_FT_def,G2_FT_def,G3_FT_def,G4_FT_def,FTree_def,gate_list_def]
>> SRW_TAC[][DISJOINT_DEF,DIFF_DEF,INTER_DEF,EXTENSION,GSPECIFICATION]
>> METIS_TAC[]
QED

(*---------------------------------*)
Theorem fail_prob_SABP_FT_lem1 :
!p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 C_SW1 C_SW2 C_L1_220 C_L2_220 C_L3_220 C_L4_220 C_T1_220 C_T2_220 C_BUS_220 C_SS_220.
0 <= t /\ prob_space p /\
     list_exp p
       [C_SW1; C_SW2; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_T1_220;
         C_T2_220; C_BUS_220; C_SS_220]
        [SW1; SW2; L1_220; L2_220; L3_220; L4_220; T1_220; T2_220;
         BUS_220; SS_220] ==>
     (list_prod
        (one_minus_list
           (list_prod_rel p
              (list_fail_event_list p
                 [[SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220];
            [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220];
            [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220];
            [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
             BUS_220; SS_220]] t))) =
      list_prod
        (one_minus_exp_prod t
           [[C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220];
      [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220];
      [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220];
      [C_SW1; C_L1_220; C_L2_220; C_L3_220; C_L4_220; C_SW2; C_T1_220;
       C_T2_220; C_BUS_220; C_SS_220]]))
Proof
RW_TAC list_ss[list_exp_def,exp_distribution_def,distribution_def,CDF_def,list_fail_event_list_def,fail_event_list_def,fail_event_def,list_prod_rel_def,list_prod_def,list_prob_def]
>> RW_TAC list_ss[one_minus_list_def,list_prod_def,one_minus_exp_prod_def,exp_func_list_def,list_sum_def,exp_func_def]
>> RW_TAC std_ss[REAL_MUL_ASSOC]
>> RW_TAC real_ss[]
QED
(*---------------------------------*)
Theorem fail_prob_SABP_FT :
!p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220 C_SW1 C_SW2 C_L1_220 C_L2_220 C_L3_220 C_L4_220 C_T1_220 C_T2_220 C_BUS_220 C_SS_220.
(0 <= t) /\ prob_space p  /\
 (!x'.
    MEM x'
      (fail_event_list p
        [SW1;SW2;L1_220;L2_220;L3_220;L4_220;T1_220;T2_220;BUS_220;SS_220] t) ==>
    x' IN events p) /\
 mutual_indep p (FLAT
     (list_fail_event_list p
        [[SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220];
         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220];
         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220];
         [SW1; L1_220; L2_220; L3_220; L4_220; SW2; T1_220; T2_220;
          BUS_220; SS_220]] t)) /\
 (list_exp p
    ([C_SW1;C_SW2;C_L1_220;C_L2_220;C_L3_220;C_L4_220;
      C_T1_220;C_T2_220;C_BUS_220;C_SS_220])
    ([SW1;SW2;L1_220;L2_220;L3_220;L4_220;T1_220;T2_220;
      BUS_220;SS_220])) ==>
(prob p
   (SABP_FT p t SW1 SW2 L1_220 L2_220 L3_220 L4_220 T1_220 T2_220 BUS_220 SS_220) =
1 - list_prod
  (one_minus_exp_prod t
     ([[C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;
        C_T1_220;C_T2_220;C_BUS_220;C_SS_220];
       [C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;
        C_T1_220;C_T2_220;C_BUS_220;C_SS_220];
       [C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;
        C_T1_220;C_T2_220;C_BUS_220;C_SS_220];
       [C_SW1;C_L1_220;C_L2_220;C_L3_220;C_L4_220;C_SW2;
        C_T1_220;C_T2_220;C_BUS_220;C_SS_220]])))
Proof
RW_TAC std_ss[]
>> RW_TAC std_ss[SABP_FT_alt_form1]
>> DEP_REWRITE_TAC[rel_parallel_series_rbd]
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[list_fail_event_list_def,fail_event_list_def])
>- (FULL_SIMP_TAC list_ss[list_fail_event_list_def,fail_event_list_def])
>> DEP_REWRITE_TAC[fail_prob_SABP_FT_lem1]
>> FULL_SIMP_TAC list_ss[]
QED

(*------------------------------------------*)
Theorem k_out_n_alt :
!p X k n.
       prob_space p /\
       (\x. PREIMAGE X {Normal(&x)}) IN ((count (SUC n)) -> events p) ==>
       (K_out_N_struct p X k n =
       (BIGUNION ((IMAGE (PREIMAGE (X:'a ->extreal))
                {{(Normal (&x))}| k <= x /\ x < SUC n}))))
Proof
RW_TAC std_ss[K_out_N_struct_def,IN_IMAGE,IN_FUNSET,IN_COUNT]
>> RW_TAC std_ss[BIGUNION,EXTENSION,GSPECIFICATION]
>> EQ_TAC
>- (RW_TAC std_ss[]
   >> Q.EXISTS_TAC `s`
   >> FULL_SIMP_TAC std_ss[IN_IMAGE,EXTENSION,GSPECIFICATION]
   >> Q.EXISTS_TAC `{Normal (&x')}`
   >> `PREIMAGE X {Normal (&x')} INTER p_space p = PREIMAGE X {Normal (&x')} `  by ONCE_REWRITE_TAC[INTER_COMM]
   >- (MATCH_MP_TAC INTER_PSPACE
      >> RW_TAC std_ss[]
      >> FIRST_X_ASSUM (MP_TAC o Q.SPECL [ `x':num`])
      >> RW_TAC std_ss[])
   >> POP_ORW
   >> RW_TAC std_ss[]
   >> Q.EXISTS_TAC `x'`
   >> RW_TAC std_ss[])
>> RW_TAC std_ss[]
>> Q.EXISTS_TAC `s`
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[IN_IMAGE,EXTENSION,GSPECIFICATION]
>> Q.EXISTS_TAC `x''`
>> `PREIMAGE X {Normal (&x'')} INTER p_space p = PREIMAGE X {Normal (&x'')} `  by ONCE_REWRITE_TAC[INTER_COMM]
   >- (MATCH_MP_TAC INTER_PSPACE
      >> RW_TAC std_ss[]
      >> FIRST_X_ASSUM (MP_TAC o Q.SPECL [ `x'':num`])
      >> RW_TAC std_ss[])
   >> POP_ORW
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC std_ss[IN_PREIMAGE]
QED

(*----------------------------------------------*)

Theorem k_out_n_RBD_v2 :
!p n k X pr.
       prob_space p /\ (k < (SUC n)) /\
       (\x. PREIMAGE X {Normal(&x)}) IN
       ((count (SUC n)) -> events p) /\
       (!x. (distribution p X {Normal (&x)} =
       ((& binomial n x)* (pr pow x) * ((1- pr) pow (n - x))))) ==>
         (prob p (K_out_N_struct p X k n) =
            sum (k, (SUC n)-k)
                (\x. (& binomial n x) * (pr pow x) * ((1 - pr) pow (n - x) )))
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[k_out_n_RBD_v1]
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[IN_IMAGE,IN_FUNSET,IN_COUNT]
>> RW_TAC std_ss[]
>> REPEAT (FIRST_X_ASSUM (MP_TAC o Q.SPECL [ `x:num`]))
>> RW_TAC std_ss[]
>> `PREIMAGE X {Normal (&x)} INTER p_space p =
    PREIMAGE X {Normal (&x)} `  by ONCE_REWRITE_TAC[INTER_COMM]
   >- (MATCH_MP_TAC INTER_PSPACE
      >> RW_TAC std_ss[])
>> POP_ORW
>> RW_TAC std_ss[]
QED
(*-------------------bigunion_in_events---------------------------*)
Theorem bigunion_in_events :
!p n k X. prob_space p /\
    (\x. PREIMAGE X {Normal(&x)}) IN ((count (SUC n)) -> events p) ==>
 (BIGUNION
  (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
     {x | k <= x /\ x < SUC n}) IN events p)
Proof
RW_TAC std_ss []
>> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
    >> RW_TAC std_ss []
    >> FULL_SIMP_TAC std_ss[IN_IMAGE,EXTENSION,GSPECIFICATION]
    >> FIRST_X_ASSUM (MP_TAC o Q.SPECL [ `x':num`])
    >> RW_TAC std_ss[]
    >> ONCE_REWRITE_TAC[INTER_COMM]
    >> DEP_REWRITE_TAC[INTER_PSPACE]
    >> RW_TAC std_ss[])
>> MATCH_MP_TAC image_countable
>> MATCH_MP_TAC finite_countable
>> RW_TAC std_ss[k_out_n_lemma2]
>> MATCH_MP_TAC FINITE_INTER
>> DISJ2_TAC
>> RW_TAC std_ss [GSYM count_def]
>> RW_TAC std_ss [FINITE_COUNT]
QED
(*----------------------------------------------*)
Theorem series_rbd_indep_k_out_n_rbd :
!p L n k X pr.
       prob_space p /\
       ~NULL L /\
       (!x'. MEM x' L ==> x' IN events p) /\
       mutual_indep p (L++ [PREIMAGE X (BIGUNION {{Normal (&x)} | k <= x /\ x < SUC n})]) /\
       (k < (SUC n)) /\
       (\x. PREIMAGE X {Normal(&x)}) IN ((count (SUC n)) -> events p) /\
       (!x. (distribution p X {Normal (&x)} =
       ((& binomial n x)* (pr pow x) * ((1 - pr) pow (n - x)))))
 ==>
       (prob p (rbd_struct p (series (rbd_list L)) INTER
               K_out_N_struct p X k n) =
        list_prod (list_prob p L) *
        sum (k, (SUC n)-k)
            (\x. (& binomial n x) * (pr pow x) * ((1 - pr) pow (n - x) )))
Proof
RW_TAC std_ss[K_out_N_struct_def]
>> `(rbd_struct p (series (rbd_list L)) INTER
   BIGUNION
     (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        {x | k <= x /\ x < SUC n})) = (rbd_struct p (series (rbd_list (L++[BIGUNION
     (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        {x | k <= x /\ x < SUC n})]))))` by DEP_REWRITE_TAC[GSYM series_rbd_append]
>- (RW_TAC list_ss[]
   >- (METIS_TAC[])
   >- (DEP_REWRITE_TAC[bigunion_in_events]
      >> RW_TAC std_ss[])
      >> RW_TAC std_ss[rbd_struct_def,rbd_list_def]
      >> `(BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
      {x | k <= x /\ x < SUC n}) INTER p_space p) = BIGUNION (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
      {x | k <= x /\ x < SUC n})` by ONCE_REWRITE_TAC[INTER_COMM]
      >- (DEP_REWRITE_TAC[INTER_PSPACE]
         >> RW_TAC std_ss[]
         >- (DEP_REWRITE_TAC[bigunion_in_events]
             >> RW_TAC std_ss[])
         >> RW_TAC std_ss[INTER_COMM])
      >> POP_ORW
      >> RW_TAC std_ss[])
>> POP_ORW
>> DEP_REWRITE_TAC[series_rbd_append2]
>> RW_TAC list_ss[]
>- (METIS_TAC[])
>- (DEP_REWRITE_TAC[bigunion_in_events]
   >> RW_TAC std_ss[])
>- (DEP_REWRITE_TAC[GSYM K_out_N_struct_def, k_out_n_alt]
   >> RW_TAC std_ss[GSYM PREIMAGE_BIGUNION])
>> RW_TAC std_ss[rbd_struct_def,rbd_list_def]
>> DEP_REWRITE_TAC[series_struct_thm]
>> RW_TAC list_ss[]
>- (MATCH_MP_TAC mutual_indep_front_append
   >> Q.EXISTS_TAC `[PREIMAGE X (BIGUNION {{Normal (&x)} | k <= x /\ x < SUC n})]`
   >> MATCH_MP_TAC mutual_indep_append_sym
   >> RW_TAC std_ss[])
>> ONCE_REWRITE_TAC[INTER_COMM]
>> DEP_REWRITE_TAC[INTER_PSPACE]
>> RW_TAC std_ss[bigunion_in_events]
>> DEP_REWRITE_TAC [GSYM K_out_N_struct_def,k_out_n_RBD_v2]
>> RW_TAC std_ss[]
QED

(*----------------------------------------------*)
(* Definition binomial_events_conds_def :
(binomial_events_conds p [] k n pr = T) /\
(binomial_events_conds p (h::t) k n pr = binomial_event_conds p h k n pr /\
                                        binomial_events_conds p t k n pr)
End
*)
(*----------------------------------------------*)
Definition binomial_event_def :
binomial_event (X:'a->extreal) a = PREIMAGE X {Normal (&a)}
End

(*----------------------------------------------*)
Definition binomial_event_list_def :
binomial_event_list L m = MAP (\a. binomial_event a m) L
End
(*----------------------------------------------*)
Definition binomial_conds_def :
binomial_conds p X X1 k n L t  =
 ((k < (SUC n)) /\
 (!x.
        x < SUC n ==>
        in_events p (binomial_event_list L x)) /\
(!x.
        distribution p X {Normal (&x)} =
        &binomial n x * Reliability p X1 t pow x *
        (1 - Reliability p X1 t) pow (n - x)))
End
(*----------------------------------------------*)
Definition K_out_N_struct_list_def :
K_out_N_struct_list p L k n = MAP (\a. K_out_N_struct p a k n) L
End

(*----------------------------------------------*)
Definition rbd_conds_def :
rbd_conds p L =
( prob_space p /\
 in_events p L /\
  mutual_indep p L )
End

(*----------------------------------------------*)
(*Theorem parallel_rbd_indep_k_out_n_rbd :
!p L n k X1 X2  pr.
       prob_space p /\
       (!z. MEM z L ==> ~NULL z) /\
       (!x'. MEM x' (FLAT L) ==> x' IN events p) /\
       mutual_indep p (FLAT (L++ [[PREIMAGE X1 (BIGUNION {{Normal (&x)} | k <= x /\ x < SUC n}); PREIMAGE X2 (BIGUNION {{Normal (&x)} | k <= x /\ x < SUC n})]])) /\
       (k < (SUC n)) /\
       (\x. PREIMAGE X1 {Normal(&x)}) IN ((count (SUC n)) -> events p) /\
       (!x. (distribution p X1 {Normal (&x)} =
       ((& binomial n x)* (pr pow x) * ((1 - pr) pow (n - x)))))
 ==>
     (prob p
        (rbd_struct p (parallel (rbd_list L1)) INTER
         rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) =
      (list_prod of
       (\a. 1 - list_prod (one_minus_list (list_prob p a)))) ([K_out_N_struct p X1 k n;K_out_N_struct p X2 k n]::L))
Proof
RW_TAC list_ss[of_DEF,o_THM,rbd_struct_def,rbd_list_def] *)
(*----------------------------------------------*)

(*----------------------------------------------*)
Theorem parallel_rbd_indep_k_out_n_rbd :
!p L1 L n k  pr.
       prob_space p /\
       mutual_indep p ((FLAT (K_out_N_struct_list p L1 k n::L))) /\
       in_events p (FLAT L) /\
       (!k. (k < SUC n) ==> in_events p (binomial_event_list L1 k)) /\
       not_null L /\ ~NULL ((K_out_N_struct_list p L1 k n))
  ==>
        (prob p
        (rbd_struct p (parallel (rbd_list (K_out_N_struct_list p L1 k n))) INTER
         rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) =
     (1 - list_prod (one_minus_list (list_prob p (K_out_N_struct_list p L1 k n)))) *
      (list_prod of
       (\a. 1 - list_prod (one_minus_list (list_prob p a)))) L)
Proof
 RW_TAC std_ss[rbd_conds_def,not_null_def]
>> DEP_REWRITE_TAC[parallel_rbd_indep_series_parallel_rbd]
>> RW_TAC list_ss[]
>- (RW_TAC std_ss[])
>- (RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[in_events_def]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_list_def,MEM_MAP]
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_def]
   >> DEP_REWRITE_TAC[bigunion_in_events]
   >> RW_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   >> FULL_SIMP_TAC std_ss[binomial_event_def]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `x:num`)
   >> RW_TAC std_ss[]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `binomial_event a x`)
   >> RW_TAC std_ss[]
   >> `MEM (binomial_event a x) (binomial_event_list L1 x)` by ALL_TAC
   >- (RW_TAC std_ss[binomial_event_list_def,MEM_MAP]
       >> Q.EXISTS_TAC `a`
       >> RW_TAC list_ss[])
   >> FULL_SIMP_TAC list_ss[binomial_event_list_def,MEM_MAP]
   >> FULL_SIMP_TAC std_ss[binomial_event_def])
>- (FULL_SIMP_TAC std_ss[in_events_def])
>> DEP_REWRITE_TAC[parallel_struct_thm]
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[in_events_def]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_list_def,MEM_MAP]
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_def]
   >> DEP_REWRITE_TAC[bigunion_in_events]
   >> RW_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   >> FULL_SIMP_TAC std_ss[binomial_event_def]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `x:num`)
   >> RW_TAC std_ss[]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `binomial_event a x`)
   >> RW_TAC std_ss[]
   >> `MEM (binomial_event a x) (binomial_event_list L1 x)` by ALL_TAC
   >- (RW_TAC std_ss[binomial_event_list_def,MEM_MAP]
       >> Q.EXISTS_TAC `a`
       >> RW_TAC list_ss[])
   >> FULL_SIMP_TAC list_ss[binomial_event_list_def,MEM_MAP]
   >> FULL_SIMP_TAC std_ss[binomial_event_def])
>- (FULL_SIMP_TAC list_ss[]
   >> MATCH_MP_TAC mutual_indep_front_append
   >> Q.EXISTS_TAC `FLAT L`
   >> MATCH_MP_TAC mutual_indep_append_sym
   >> RW_TAC std_ss[])
>> `(rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = (rbd_struct p ((series of (\a. parallel (rbd_list a))) L))` by RW_TAC std_ss[of_DEF,o_THM]
>> POP_ORW
>> DEP_REWRITE_TAC[series_parallel_struct_thm_v2]
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[in_events_def])
>> FULL_SIMP_TAC list_ss[]
>> MATCH_MP_TAC mutual_indep_front_append
>> Q.EXISTS_TAC `K_out_N_struct_list p L1 k n`
>> RW_TAC std_ss[]
QED
(*----------------------------------------------*)
Theorem parallel_rbd_indep_k_out_n_rbd_v1 :
!p L1 L n k  pr.
       prob_space p /\
       mutual_indep p ((FLAT (K_out_N_struct_list p L1 k n::L))) /\
       in_events p (FLAT L) /\
       (!k. (k < SUC n) ==> in_events p (binomial_event_list L1 k)) /\
       not_null L /\ ~NULL ((K_out_N_struct_list p L1 k n))
  ==>
        (prob p
        (rbd_struct p (parallel (rbd_list (K_out_N_struct_list p L1 k n))) INTER
         rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) =
     (1 - list_prod (one_minus_list (list_prob p (K_out_N_struct_list p L1 k n)))) *
      prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L)))
Proof
 RW_TAC std_ss[rbd_conds_def,not_null_def]
>> DEP_REWRITE_TAC[parallel_rbd_indep_series_parallel_rbd]
>> RW_TAC list_ss[]
>- (RW_TAC std_ss[])
>- (RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[in_events_def]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_list_def,MEM_MAP]
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_def]
   >> DEP_REWRITE_TAC[bigunion_in_events]
   >> RW_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   >> FULL_SIMP_TAC std_ss[binomial_event_def]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `x:num`)
   >> RW_TAC std_ss[]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `binomial_event a x`)
   >> RW_TAC std_ss[]
   >> `MEM (binomial_event a x) (binomial_event_list L1 x)` by ALL_TAC
   >- (RW_TAC std_ss[binomial_event_list_def,MEM_MAP]
       >> Q.EXISTS_TAC `a`
       >> RW_TAC list_ss[])
   >> FULL_SIMP_TAC list_ss[binomial_event_list_def,MEM_MAP]
   >> FULL_SIMP_TAC std_ss[binomial_event_def])
>- (FULL_SIMP_TAC std_ss[in_events_def])
>> DEP_REWRITE_TAC[parallel_struct_thm]
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[in_events_def]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_list_def,MEM_MAP]
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC list_ss[K_out_N_struct_def]
   >> DEP_REWRITE_TAC[bigunion_in_events]
   >> RW_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   >> FULL_SIMP_TAC std_ss[binomial_event_def]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `x:num`)
   >> RW_TAC std_ss[]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC
         `binomial_event a x`)
   >> RW_TAC std_ss[]
   >> `MEM (binomial_event a x) (binomial_event_list L1 x)` by ALL_TAC
   >- (RW_TAC std_ss[binomial_event_list_def,MEM_MAP]
       >> Q.EXISTS_TAC `a`
       >> RW_TAC list_ss[])
   >> FULL_SIMP_TAC list_ss[binomial_event_list_def,MEM_MAP]
   >> FULL_SIMP_TAC std_ss[binomial_event_def])
>- (FULL_SIMP_TAC list_ss[]
   >> MATCH_MP_TAC mutual_indep_front_append
   >> Q.EXISTS_TAC `FLAT L`
   >> MATCH_MP_TAC mutual_indep_append_sym
   >> RW_TAC std_ss[])
>> `(rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L))) = (rbd_struct p ((series of (\a. parallel (rbd_list a))) L))` by RW_TAC std_ss[of_DEF,o_THM]
>> POP_ORW
>> RW_TAC std_ss[]
QED
(*----------------------------------------------*)
Theorem series_parallel_rbd_indep_k_out_n_rbd_exp_dist :
!p PIED ESW1 ESW2 ESW3 ESW4 ESWs CIED  C_PIED C_ESW1 C_ESW2 C_ESW3 C_ESW4 C_ESWs C_CIED   pr t.
       0 <= t /\
       prob_space p /\
       mutual_indep p
         ((FLAT
             (K_out_N_struct_list p [ESWs;ESWs] 3 4::
                (two_dim_rel_event_list p
                   [[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED]] t)))) /\
       in_events p
          (FLAT
            (two_dim_rel_event_list p
               [[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED]] t)) /\
       (!x.
          (x < SUC 4) ==>
          in_events p (binomial_event_list [ESWs;ESWs] x)) /\
       (!x.
          (distribution p ESWs {Normal (&x)} =
          ((& binomial 4 x)* (pr pow x) * ((1 - pr) pow (4 - x))))) /\
       (two_dim_exp_dist_list p
        [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]
        [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]]) ==>
       (prob p
          (rbd_struct p
            (parallel
               (rbd_list (K_out_N_struct_list p [ESWs;ESWs] 3 4))) INTER
           rbd_struct p
            (series
               (MAP (\a. parallel (rbd_list a))
                  (two_dim_rel_event_list p
                     [[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED]] t)))) =
        (1 -
         (1 -
          sum (3,SUC 4 - 3)
            (\x.
                &binomial 4 x * pr pow x * (1 - pr) pow (4 - x))) *
         (1 - sum (3,SUC 4 - 3)
            (\x. &binomial 4 x * pr pow x * (1 - pr) pow (4 - x))))  *
      (list_prod of
       (\a. 1 - list_prod (one_minus_list (exp_func_list a t))))
            [[C_PIED];[C_ESW1;C_ESW2];[C_ESW3;C_ESW4];[C_CIED]])
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[parallel_rbd_indep_k_out_n_rbd_v1]
>> RW_TAC std_ss[]
>- (DEP_REWRITE_TAC[not_null_def,mem_flat_fun_eq_mem_flat_null_list3]
   >> RW_TAC list_ss[]
   >- (RW_TAC list_ss[])
   >- (RW_TAC list_ss[])
   >- (RW_TAC list_ss[])
   >> (RW_TAC list_ss[]))
>- (RW_TAC list_ss[K_out_N_struct_list_def])
>> MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                                                 `t:real`,
                                                `[[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED:'a->extreal]]`,
                                                `[[C_PIED:real];[C_ESW1;C_ESW2];[C_ESW3;C_ESW4];[C_CIED]]`]
                                                        rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC std_ss[]
>> `(!z.
         MEM z [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] ==> ~NULL z) /\
      0 <= t /\
      (!x'.
         MEM x'
           (FLAT
              (two_dim_rel_event_list p
                 [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) ==>
         x' IN events p) /\
      mutual_indep p
        (FLAT
           (two_dim_rel_event_list p
              [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) /\
      (LENGTH [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]] =
       LENGTH [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]) /\
      (!n.
         n < LENGTH [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] /\
         n <
         LENGTH
           [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]] ==>
         (LENGTH (EL n [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]) =
          LENGTH
            (EL n
               [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4];
                [C_CIED]])))` by RW_TAC list_ss[]
>- (RW_TAC list_ss[])
>- (RW_TAC list_ss[])
>- (RW_TAC list_ss[])
>- (RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[in_events_def])
>- (FULL_SIMP_TAC list_ss[]
   >> MATCH_MP_TAC mutual_indep_front_append
   >> Q.EXISTS_TAC `K_out_N_struct_list p [ESWs; ESWs] 3 4`
   >> RW_TAC std_ss[])
>- (Cases_on `n`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[]
   >> Cases_on `n'`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[]
   >> Cases_on `n`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[]
   >> Cases_on `n'`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> NTAC 6 POP_ORW
>> RW_TAC std_ss[REAL_EQ_RMUL]
>> DISJ2_TAC
>> RW_TAC list_ss[K_out_N_struct_list_def,list_prod_def,list_prob_def,one_minus_list_def]
>> RW_TAC real_ss[]
>> DEP_REWRITE_TAC[k_out_n_RBD_v2]
>> RW_TAC std_ss[]
>- (RW_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
   >> FULL_SIMP_TAC list_ss[binomial_event_list_def,in_events_def,binomial_event_def])
QED

(*---------------------------------------------*)
(*----------------------------------------------*)
Theorem series_parallel_rbd_indep_k_out_n_rbd_exp_dist_eval :
!p PIED ESW1 ESW2 ESW3 ESW4 ESWs CIED X_bino C_PIED C_ESW1 C_ESW2 C_ESW3 C_ESW4 C_ESWs C_CIED t.
       0 <= t /\
       prob_space p /\
       mutual_indep p
         ((FLAT
            (K_out_N_struct_list p [X_bino;X_bino] 3 4::
                (two_dim_rel_event_list p
                  [[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED]] t)))) /\
       in_events p
         (FLAT
           (two_dim_rel_event_list p
              [[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED]] t)) /\
       (!x.
          (x < SUC 4) ==>
          in_events p (binomial_event_list [X_bino;X_bino] x)) /\
       (!x.
          (distribution p X_bino {Normal (&x)} =
          ((&binomial 4 x)* ((Reliability p ESWs t) pow x) *
          ((1 - (Reliability p ESWs t) ) pow (4 - x))))) /\
       exp_dist p ESWs C_ESWs /\
       (two_dim_exp_dist_list p [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]
         [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]]) ==>
       (prob p
        (rbd_struct p
           (parallel
             (rbd_list (K_out_N_struct_list p [X_bino;X_bino] 3 4))) INTER
         rbd_struct p
           (series
             (MAP (\a. parallel (rbd_list a))
                (two_dim_rel_event_list p
                   [[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED]] t)))) =
         (1 -
          (1 -
           sum (3,SUC 4 - 3)
            (\x.
                &binomial 4 x * exp (-C_ESWs * t) pow x *
                (1 - exp (-C_ESWs * t)) pow (4 - x))) *
          (1 -
           sum (3,SUC 4 - 3)
            (\x.
                &binomial 4 x * exp (-C_ESWs * t) pow x *
                (1 - exp (-C_ESWs * t)) pow (4 - x)))) *
         (list_prod of
          (\a. 1 - list_prod (one_minus_list (exp_func_list a t))))
            [[C_PIED];[C_ESW1;C_ESW2];[C_ESW3;C_ESW4];[C_CIED]])
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[parallel_rbd_indep_k_out_n_rbd_v1]
>> RW_TAC std_ss[]
>- (DEP_REWRITE_TAC[not_null_def,mem_flat_fun_eq_mem_flat_null_list3]
   >> RW_TAC list_ss[]
   >- (RW_TAC list_ss[])
   >- (RW_TAC list_ss[])
   >- (RW_TAC list_ss[])
   >> (RW_TAC list_ss[]))
>- (RW_TAC list_ss[K_out_N_struct_list_def])
>> MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                                                 `t:real`,
                                                 `[[PIED];[ESW1;ESW2];[ESW3;ESW4];[CIED:'a->extreal]]`,
                                                `[[C_PIED:real];[C_ESW1;C_ESW2];[C_ESW3;C_ESW4];[C_CIED]]`] rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC std_ss[]
>> `(!z.
         MEM z [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] ==> ~NULL z) /\
      0 <= t /\
      (!x'.
         MEM x'
           (FLAT
              (two_dim_rel_event_list p
                 [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) ==>
         x' IN events p) /\
      mutual_indep p
        (FLAT
           (two_dim_rel_event_list p
              [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] t)) /\
      (LENGTH [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]] =
       LENGTH [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]) /\
      (!n.
         n < LENGTH [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]] /\
         n <
         LENGTH
           [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4]; [C_CIED]] ==>
         (LENGTH (EL n [[PIED]; [ESW1; ESW2]; [ESW3; ESW4]; [CIED]]) =
          LENGTH
            (EL n
               [[C_PIED]; [C_ESW1; C_ESW2]; [C_ESW3; C_ESW4];
                [C_CIED]])))` by RW_TAC list_ss[]
>- (RW_TAC list_ss[])
>- (RW_TAC list_ss[])
>- (RW_TAC list_ss[])
>- (RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[in_events_def])
>- (FULL_SIMP_TAC list_ss[]
   >> MATCH_MP_TAC mutual_indep_front_append
   >> Q.EXISTS_TAC `K_out_N_struct_list p [X_bino; X_bino] 3 4`
   >> RW_TAC std_ss[])
>- (Cases_on `n`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[]
   >> Cases_on `n'`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[]
   >> Cases_on `n`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[]
   >> Cases_on `n'`
   >- (RW_TAC list_ss[])
   >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> NTAC 6 POP_ORW
>> RW_TAC std_ss[REAL_EQ_RMUL]
>> DISJ2_TAC
>> RW_TAC list_ss[K_out_N_struct_list_def,list_prod_def,list_prob_def,one_minus_list_def]
>> RW_TAC real_ss[]
>> MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                                                 `4:num`, `3:num`,
                                                `X_bino:'a->extreal`,`(Reliability p ESWs t)`] k_out_n_RBD_v2)
>> RW_TAC std_ss[]
>> `(\x. PREIMAGE X_bino {Normal (&x)}) IN (count 5 -> events p)` by RW_TAC std_ss[SUBSET_DEF,IN_FUNSET,IN_COUNT,IN_IMAGE]
>- (FULL_SIMP_TAC list_ss[binomial_event_list_def,in_events_def,binomial_event_def])
>> FULL_SIMP_TAC std_ss[]
>> `Reliability p ESWs t = exp (-C_ESWs * t)` by RW_TAC std_ss[Reliability_def]
>- (FULL_SIMP_TAC real_ss[exp_distribution_def])
>> POP_ORW
>> rw [REAL_NEG_LMUL]
QED

(*----------------------------------------------*)
val _ = export_theory();
