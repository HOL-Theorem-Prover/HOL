(* ========================================================================= *)
(* File Name: frogp.sml                                                      *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Reliability Analysis of Oil and Gas Pipelines         *)
(*               using Theorem Proving                                       *)
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


(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory",
          "real_probabilityTheory", "numTheory", "extra_pred_setTools",
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "real_measureTheory",
          "real_lebesgueTheory","real_sigmaTheory","dep_rewrite","RBDTheory",
          "FT_deepTheory","VDCTheory","ASN_gatewayTheory"];*)
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory
     prim_recTheory real_probabilityTheory seqTheory pred_setTheory res_quanTheory
     sortingTheory res_quanTools listTheory transcTheory rich_listTheory pairTheory
     combinTheory realLib  optionTheory util_probTheory extrealTheory real_measureTheory
     real_lebesgueTheory real_sigmaTheory satTheory numTheory dep_rewrite
     extra_pred_setTools RBDTheory VDCTheory FT_deepTheory ASN_gatewayTheory;

fun K_TAC _ = ALL_TAC;

open HolKernel boolLib bossLib Parse;
val _ = new_theory "frogp";

(*--------------------*)
val op by = BasicProvers.byA;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)


(*---------------------------------------------------*)
(*-----Case Study: Oil and Gas Pipeline-------------*)
(*--------------------------------------------------*)
(* ------------------------------------------------------------------------- *)

Definition pipeline_def :
pipeline p L  = prob p (rbd_struct p (series (rbd_list L)))
End

(* ------------------------------------------------------------------------- *)
(*-------------------------------------------------*)
(*---------Operation State z1----------------------*)
(*-------------------------------------------------*)
Definition rel_pipeline_z1_def :
(rel_pipeline_z1 p X (2:num) (3:num) = prob p
 (BIGUNION
    (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
       ({x|(2:num) <= x /\ x < (SUC 3)}))))
End
(* ------------------------------------------------------------------------- *)
Theorem series_exp_list_sum :
!p t L C. (0 <=  t) /\  prob_space p /\
                exp_dist_list p L C /\ (LENGTH C = LENGTH L ) /\
                (!z. MEM z (rel_event_list p L t) ==> z IN events p) ==>
                 (list_prod (list_prob p (rel_event_list p L t)) =
                  exp_func t (list_sum C))
Proof
GEN_TAC >> GEN_TAC
>> Induct
>- (RW_TAC list_ss[list_prob_def,list_sum_def,rel_event_list_def,exp_func_def,list_prod_def,LENGTH_NIL]
   >> RW_TAC real_ss[EXP_0])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[list_prob_def,list_sum_def,rel_event_list_def,exp_func_def,list_prod_def,exp_dist_list_def,VDCTheory.exp_dist_def,CDF_def,distribution_def]
>> RW_TAC std_ss[GSYM rel_event_def]
>> DEP_REWRITE_TAC[GSYM compl_fail_event_eq_rel_event]
>> DEP_REWRITE_TAC[PROB_COMPL]
>> DEP_REWRITE_TAC[GSYM comp_rel_event_eq_fail_event]
>> DEP_REWRITE_TAC[EVENTS_COMPL]
>> RW_TAC std_ss[rel_event_def]
>> RW_TAC std_ss[compl_rel_event_eq_fail_event]
>> RW_TAC real_ss[GSYM fail_event_def,rel_event_def,GSYM  rel_event_list_def,compl_fail_event_eq_rel_event]
>> FULL_SIMP_TAC std_ss[GSYM rel_event_list_def]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`C':real list`] MP_TAC)
>> RW_TAC std_ss[]
>> RW_TAC real_ss[exp_func_def]
>> RW_TAC real_ss[REAL_RDISTRIB,REAL_NEG_ADD,EXP_ADD]
QED

(*-----------------------------------------------*)
Theorem rel_pipeline_series :
!p L t C. 0 <= t /\ prob_space p /\ exp_dist_list p L C /\
     (LENGTH C = LENGTH L) /\
     ~NULL (rel_event_list p L t) /\
     mutual_indep p (rel_event_list p L t) /\
     (!x. MEM x (rel_event_list p L t) ==> x IN events p) ==>
                (pipeline p (rel_event_list p L t) = exp (-(list_sum C) * t))
Proof
RW_TAC std_ss[pipeline_def]
>> DEP_REWRITE_TAC[series_struct_thm]
>> RW_TAC std_ss[GSYM REAL_NEG_LMUL,GSYM exp_func_def]
>> MATCH_MP_TAC series_exp_list_sum
>> RW_TAC std_ss[]
QED

(*---------------------------------------------------*)
(*---------------rel_pipeline_z1_THM------------------*)
(*---------------------------------------------------*)
Theorem rel_pipeline_z1_thm :
!p p' X C L t.
   prob_space p  /\
   prob_space p'  /\
   (!x. MEM x (rel_event_list p' L t) ==> x IN events p') /\
   (\x. PREIMAGE X {Normal(&x)} INTER p_space p) IN
         ((count (SUC 3)) -> events p) /\
   (!x.
     (distribution p X {Normal (&x)} =
     ((& binomial (3) x) * ((pipeline p' (rel_event_list p' L t)) pow x) *
       ((1- (pipeline p' (rel_event_list p' L t))) pow ((3)-x))))) /\
  (~NULL (rel_event_list p' L t)) /\
  (0 <=  t) /\
  (exp_dist_list p' L C) /\
  (LENGTH C = LENGTH L) /\
  mutual_indep p' (rel_event_list p' L t) ==>
    (rel_pipeline_z1 p X (2:num) (3:num) =
     3 * exp (2 * -(list_sum C * t)) * (1 − exp (-(list_sum C * t))) +
       exp (3 * -(list_sum C * t)))
Proof
REPEAT GEN_TAC THEN
REPEAT STRIP_TAC THEN REWRITE_TAC[rel_pipeline_z1_def] THEN
(`prob p
  (BIGUNION
     (IMAGE (\x. PREIMAGE X {Normal (&x)} INTER p_space p)
        {x | 2 <= x /\ x < SUC 3})) =
        sum (2,SUC 3 − 2)
        (\x. &binomial 3 x * (pipeline p' (rel_event_list p' L t)) pow x *
                (1 − (pipeline p' (rel_event_list p' L t))) pow (3 − x)) ` by (REWRITE_TAC[GSYM K_out_N_struct_def]
THEN MATCH_MP_TAC k_out_n_RBD_v1)) THEN1
(RW_TAC std_ss[] THEN ONCE_ASM_REWRITE_TAC[]) THEN POP_ORW THEN
RW_TAC real_ss[] THEN ONCE_REWRITE_TAC[TWO] THEN
RW_TAC std_ss[sum] THEN ONCE_REWRITE_TAC[ONE] THEN RW_TAC std_ss[sum] THEN
(`(3 = SUC 2)` by RW_TAC arith_ss[]) THEN ONCE_ASM_REWRITE_TAC[] THEN
POP_ASSUM(K ALL_TAC) THEN
ONCE_REWRITE_TAC[TWO] THEN
RW_TAC std_ss[binomial_def,BINOMIAL_DEF4] THEN
ONCE_REWRITE_TAC[TWO,ONE] THEN
(`(3 = SUC 2)` by RW_TAC arith_ss[]) THEN ONCE_ASM_REWRITE_TAC[] THEN
POP_ASSUM(K ALL_TAC) THEN
RW_TAC std_ss[binomial_def,BINOMIAL_DEF4] THEN
ONCE_REWRITE_TAC[TWO,ONE] THEN
RW_TAC std_ss[binomial_def] THEN
(`pipeline p' (rel_event_list p' L t) = exp (-list_sum C * t)` by MATCH_MP_TAC rel_pipeline_series) THEN
RW_TAC real_ss[] THEN POP_ORW THEN
RW_TAC std_ss[POW_2] THEN RW_TAC real_ss[GSYM EXP_ADD] THEN
RW_TAC real_ss[POW_1] THEN (`(3 = SUC 2)` by RW_TAC arith_ss[]) THEN
ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN
RW_TAC real_ss[pow] THEN RW_TAC std_ss[POW_2] THEN
RW_TAC real_ss[GSYM EXP_ADD] THEN RW_TAC std_ss[REAL_DOUBLE] THEN
(`!a:real. ((a + 2*a) = 3*a)` by REAL_ARITH_TAC) THEN
ASM_REWRITE_TAC[] THEN RW_TAC real_ss[]
QED


(*-------------------------------------------------*)
(*---------Operation State z2----------------------*)
(*-------------------------------------------------*)

Definition rel_pipeline_z2_def :
(rel_pipeline_z2 p L t = prob p
        (rbd_struct p
           ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
                          L)))
End

Definition len_mem_list_le_def :
(len_mem_list_le (3:num) L = (!x. MEM x L ==> (LENGTH x <= 3)))
End


(*---------------------------------------------------*)
(*---------------rel_pipeline_z2_THM------------------*)
(*---------------------------------------------------*)
Theorem rel_pipeline_z2_thm :
!L (C:real list list)  p (t:real).
 (!z. MEM z L  ==>  ~NULL z)
   /\ (0 <=  (t:real)) /\ prob_space p /\
   (!x'. MEM x' (FLAT ((two_dim_rel_event_list p L t))) ==> (x' IN events p))
    /\ ( mutual_indep p (FLAT (two_dim_rel_event_list p L t)))
 /\ (LENGTH C = LENGTH L) /\ (!n. LENGTH (EL n L) = LENGTH (EL n C)) /\
  two_dim_exp_dist_list p L C /\
len_mem_list_le (3:num) L ==>
  (rel_pipeline_z2 p L t =
      (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C)
Proof
RW_TAC std_ss[rel_pipeline_z2_def] THEN
DEP_REWRITE_TAC[rbd_virtual_cloud_server_alt_form] THEN
RW_TAC std_ss[] THEN
MATCH_MP_TAC rel_series_parallel_RBD_exp_dist_fail_rate THEN RW_TAC std_ss[]
QED

(*------------------------------------------------------*)
(*------------------------------------------------------*)
Theorem rel_pipeline_z3_lemma4 :
!L1 L2 p.
     (!z. MEM z (L1++L2) ==> ~NULL z) /\ prob_space p /\
     (!x'. MEM x' (FLAT (L1++L2)) ==> x' IN events p) /\
     mutual_indep p (FLAT (L1++L2)) ==>
     (prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L1) INTER
              rbd_struct p ((series of (\a. parallel (rbd_list a))) L2)) =
      prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L1)) *
      prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L2)))
Proof
RW_TAC std_ss[]
>> MP_TAC(ISPECL [``p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)``, ``L1:'a event list list`` ,``[[L2:'a event list list]]``] series_parallel_rbd_indep_series_parallel_of_series_parallel)
>> RW_TAC list_ss[of_DEF,o_DEF,rbd_struct_def,rbd_list_def,UNION_EMPTY]
>> FULL_SIMP_TAC std_ss[GSYM FLAT_APPEND]
>> RW_TAC std_ss[of_DEF,o_THM]
>> (`((rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L2)) INTER
           p_space p) = (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L2)))) ` by ONCE_REWRITE_TAC[INTER_COMM])
>- (MATCH_MP_TAC INTER_PSPACE
   >> DEP_REWRITE_TAC[in_events_series_parallel]
   >> RW_TAC list_ss[])
>> FULL_SIMP_TAC list_ss[]
QED


(*---------------------------------------------------*)
(*---------------------------------------------------*)
(*---------------rel_pipeline_z3_THM------------------*)
(*---------------------------------------------------*)
Theorem rel_pipeline_z3_THM :
!L1 L2 (C1:real list list) C2  p (t:real).
 (!z. MEM z (L1++L2)  ==>  ~NULL z)
   /\ (0 <=  (t:real)) /\ prob_space p  /\
   (!x'. MEM x' (FLAT ((two_dim_rel_event_list p (L1++L2)  t))) ==> (x' IN events p))
    /\ ( mutual_indep p (FLAT ( two_dim_rel_event_list p (L1++L2 ) t)))
 /\ (LENGTH C1 = LENGTH L1) /\
(LENGTH C2 = LENGTH L2) /\
 (!n. LENGTH (EL n L1) = LENGTH (EL n C1)) /\
(!n. LENGTH (EL n L2) = LENGTH (EL n C2)) /\
  two_dim_exp_dist_list p L1 C1 /\
two_dim_exp_dist_list p L2 C2 /\
len_mem_list_le (2:num) L1 /\
len_mem_list_le (2:num) L2 ==>
  (prob p (rbd_struct p
        ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
           L1) INTER rbd_struct p
        ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
           L2)) =
      (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C1 * (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C2)
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[rbd_virtual_cloud_server_alt_form]
>> RW_TAC std_ss[]
>> DEP_REWRITE_TAC[rel_pipeline_z3_lemma4]
>> RW_TAC list_ss[two_dim_rel_event_list_def]
>- (POP_ASSUM MP_TAC
   >> MATCH_MP_TAC mem_flat_map_not_null3
   >> RW_TAC list_ss[])
>- (POP_ASSUM MP_TAC
   >> MATCH_MP_TAC mem_flat_map_not_null3
   >> RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def])
>> MP_TAC(Q.ISPECL[`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                   `t:real`,`L1:('a->extreal)list list`,`C1:real list list`] rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC list_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
>> (`mutual_indep p (FLAT (MAP (\a. rel_event_list p a t) L1))` by MATCH_MP_TAC mutual_indep_front_append)
>- (EXISTS_TAC (``(FLAT (MAP (\a. rel_event_list p a t) L2))``)
   >> MATCH_MP_TAC mutual_indep_append_sym
   >> RW_TAC std_ss[])
>> FULL_SIMP_TAC list_ss[]
>> RW_TAC std_ss[]
>> POP_ORW
>> POP_ORW
>> MP_TAC(Q.ISPECL[`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                   `t:real`,`L2:('a->extreal)list list`,`C2:real list list`] rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC list_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
>> (`mutual_indep p (FLAT (MAP (\a. rel_event_list p a t) L2))` by MATCH_MP_TAC mutual_indep_front_append)
>- (EXISTS_TAC (``(FLAT (MAP (\a. rel_event_list p a t) L1))``)
   >> RW_TAC std_ss[])
>> FULL_SIMP_TAC list_ss[]
>> RW_TAC std_ss[]
QED

  (*---------------------------------------------------*)
 (*-------------------------------------------------*)
(*---------Operation State z4----------------------*)
(*-------------------------------------------------*)
Definition rel_pipeline_z4_def :

    rel_pipeline_z4 p L1 L2 L3 t = (prob p
        (rbd_struct p ((series of (\a. parallel (rbd_list a))) L1) INTER
              rbd_struct p ((series of (\a. parallel (rbd_list a))) L2) INTER
              rbd_struct p ((series of (\a. parallel (rbd_list a))) L3)))
End

(*-------------------------------------------------*)


Theorem rel_pipeline_z4_lemma2 :
!L1 L2 L3 p.
     (!z. MEM z (L1++L2++L3) ==> ~NULL z) /\ prob_space p /\
     (!x'. MEM x' (FLAT (L1++L2++L3)) ==> x' IN events p) /\ mutual_indep p (FLAT (L1++L2++L3)) ==>
     (prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L1) INTER
              rbd_struct p ((series of (\a. parallel (rbd_list a))) L2) INTER
              rbd_struct p ((series of (\a. parallel (rbd_list a))) L3)) =
      prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L1)) *
      prob p (rbd_struct p ((series of (\a. parallel (rbd_list a))) L2) INTER
              rbd_struct p ((series of (\a. parallel (rbd_list a))) L3)))
Proof
RW_TAC std_ss[]
>> MP_TAC(ISPECL [``p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)``, ``L1:'a event list list`` ,``[[L2:'a event list list];[L3]]``] series_parallel_rbd_indep_series_parallel_of_series_parallel)
>> RW_TAC real_ss[of_DEF,o_DEF,rbd_struct_def,rbd_list_def]
>> FULL_SIMP_TAC list_ss[rbd_struct_def,rbd_list_def,o_THM,UNION_EMPTY]
>> (`((rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L3)) INTER
           p_space p) = (rbd_struct p (series (MAP (\a. parallel (rbd_list a)) L3)))) ` by ONCE_REWRITE_TAC[INTER_COMM])
>- (MATCH_MP_TAC INTER_PSPACE
   >> DEP_REWRITE_TAC[in_events_series_parallel]
   >> RW_TAC list_ss[])
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[of_DEF,o_THM,INTER_ASSOC]
>> RW_TAC std_ss[INTER_ASSOC]
>> METIS_TAC[]
QED


(*---------------------------------------------------*)
(*---------------------------------------------------*)
(*---------------rel_pipeline_z4_THM------------------*)
(*---------------------------------------------------*)
Theorem rel_pipeline_z4_THM :
!L1 L2 L3 C1 C2 C3 p t.
     (!z. MEM z (L1 ++ L2 ++ L3) ==> ¬NULL z) /\ 0 <= t /\ prob_space p /\
     (!x'.
        MEM x' (FLAT (two_dim_rel_event_list p (L1 ++ L2 ++ L3) t)) ==>
        x' IN events p) /\
     mutual_indep p (FLAT (two_dim_rel_event_list p (L1 ++ L2 ++ L3) t)) /\
     (LENGTH C1 = LENGTH L1) /\ (LENGTH C2 = LENGTH L2) /\
     (LENGTH C3 = LENGTH L3) /\
     (!n. LENGTH (EL n L1) = LENGTH (EL n C1)) /\
     (!n. LENGTH (EL n L2) = LENGTH (EL n C2)) /\
     (!n. LENGTH (EL n L3) = LENGTH (EL n C3)) /\
     two_dim_exp_dist_list p L1 C1 /\ two_dim_exp_dist_list p L2 C2 /\
     two_dim_exp_dist_list p L3 C3 /\
     len_mem_list_le 2 L1 /\ len_mem_list_le 2 L2 /\
     len_mem_list_le 2 L3 ==>
     (prob p
        (rbd_struct p
           ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
              L1) INTER
         rbd_struct p
           ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
              L2) INTER
          rbd_struct p
           ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
              L3)) =
      (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C1 *
      (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C2*
      (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C3)
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[rbd_virtual_cloud_server_alt_form]
>> RW_TAC std_ss[]
>> DEP_REWRITE_TAC[rel_pipeline_z4_lemma2]
>> RW_TAC list_ss[two_dim_rel_event_list_def]
>- (FULL_SIMP_TAC list_ss[] >> METIS_TAC[mem_flat_map_not_null3])
>- (FULL_SIMP_TAC list_ss[] >> METIS_TAC[mem_flat_map_not_null3])
>- (FULL_SIMP_TAC list_ss[] >> METIS_TAC[mem_flat_map_not_null3])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def])
>> RW_TAC std_ss[GSYM two_dim_rel_event_list_def]
>> DEP_REWRITE_TAC[rel_pipeline_z3_lemma4]
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
>> RW_TAC list_ss[]
>- (FULL_SIMP_TAC list_ss[] >> METIS_TAC[mem_flat_map_not_null3])
>- (FULL_SIMP_TAC list_ss[] >> METIS_TAC[mem_flat_map_not_null3])
>- (FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[]
   >> MATCH_MP_TAC mutual_indep_front_append
   >> EXISTS_TAC(``FLAT (MAP (\a. rel_event_list p a t) L1)``)
   >> RW_TAC list_ss[])
>> MP_TAC(Q.ISPECL[`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                   `t:real`,`L1:('a->extreal)list list`,`C1:real list list`] rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC list_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
>> (`mutual_indep p (FLAT (MAP (\a. rel_event_list p a t) L1))` by
   MATCH_MP_TAC mutual_indep_front_append)
>- (EXISTS_TAC(``FLAT (MAP (\a. rel_event_list p a t) L2) ++
         FLAT (MAP (\a. rel_event_list p a t) L3)``)
    >> MATCH_MP_TAC mutual_indep_append_sym
    >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> MP_TAC(Q.ISPECL[`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                   `t:real`,`L2:('a->extreal)list list`,`C2:real list list`] rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC list_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
>> (`mutual_indep p (FLAT (MAP (\a. rel_event_list p a t) L2))` by
   MATCH_MP_TAC mutual_indep_front_append)
>- (EXISTS_TAC(``FLAT (MAP (\a. rel_event_list p a t) L3)``)
    >> MATCH_MP_TAC mutual_indep_append_sym
    >> MATCH_MP_TAC mutual_indep_front_append
    >> EXISTS_TAC(``FLAT (MAP (\a. rel_event_list p a t) L1)``)
    >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> MP_TAC(Q.ISPECL[`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`,
                   `t:real`,`L3:('a->extreal)list list`,`C3:real list list`] rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC list_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
>> (`mutual_indep p (FLAT (MAP (\a. rel_event_list p a t) L3))` by
   MATCH_MP_TAC mutual_indep_front_append)
>- (EXISTS_TAC(``FLAT (MAP (\a. rel_event_list p a t) L1) ++
                  FLAT (MAP (\a. rel_event_list p a t) L2)``)
    >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> REAL_ARITH_TAC
QED

val _ = export_theory();
