(* ========================================================================= *)
(* File Name: WSNScript.sml                                                  *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Reliability Analysis of Data Transport Protocol       *)
(*                 using Theorem Proving                                     *)
(*                                                                           *)
(*                HOL4-Kananaskis 12                                         *)
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
     rich_listTheory pairTheory combinTheory realLib  optionTheory util_probTheory extrealTheory real_measureTheory
     real_lebesgueTheory real_sigmaTheory satTheory numTheory dep_rewrite extra_pred_setTools;

open RBDTheory FT_deepTheory VDCTheory smart_gridTheory ASN_gatewayTheory;

fun K_TAC _ = ALL_TAC;

val _ = new_theory "WSN";

(*--------------------*)
val op by = BasicProvers.byA;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)

(*--------------------------------------*)
Theorem E2W_WSN :
!p t X_fil X_aggr X_rout C_fil C_aggr C_rout.
              (0 <= t) /\
              prob_space p /\
              exp_dist_list p ([X_fil;X_aggr;X_rout])
                              ([C_fil;C_aggr;C_rout])  /\
              mutual_indep p
                (rel_event_list p ([X_fil;X_aggr;X_rout]) t) /\
              (!x.
                   MEM x (rel_event_list p ([X_fil;X_aggr;X_rout]) t) ==>
                   x IN events p) ==>
               (prob p (rbd_struct p
                    (series (rbd_list (rel_event_list p [X_fil;X_aggr;X_rout] t)))) =
                exp (-list_sum[C_fil;C_aggr;C_rout] * t))
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[series_struct_thm]
>> RW_TAC list_ss[]
>- (RW_TAC list_ss[rel_event_list_def])
>> MP_TAC (ISPECL [``p:'a event # 'a event event # ('a event -> real)``, ``t:real``,``[X_fil; X_aggr; X_rout]:('a->extreal) list``,``[C_fil; C_aggr; C_rout]:real list`` ]rel_prod_series_rbd_exp_dist)
>> RW_TAC list_ss[]
>> RW_TAC list_ss[exp_func_list_def,list_sum_def,list_prod_def]
>> RW_TAC real_ss[GSYM transcTheory.EXP_ADD]
>> AP_TERM_TAC
>> REAL_ARITH_TAC
QED

(*------------------------------------*)
Theorem one_minus_exp_equi :
!t c. (one_minus_list (exp_func_list c t)) =
          (one_minus_exp t c)
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[exp_func_list_def,one_minus_exp_def,one_minus_list_def])
>> RW_TAC list_ss[exp_func_list_def,one_minus_exp_def,one_minus_list_def]
>- (RW_TAC real_ss[REAL_MUL_COMM])
>> FULL_SIMP_TAC list_ss[exp_func_list_def,one_minus_exp_def]
QED
(*-------------------------------------*)

Theorem ESRT_WSN :
!p t X_routing_list C_routing_list.
              (0 <= t) /\
              prob_space p /\
              ~NULL (rel_event_list p X_routing_list t) /\
              exp_dist_list p (X_routing_list)
                              (C_routing_list)  /\
              (LENGTH X_routing_list = LENGTH C_routing_list) /\
              mutual_indep p
                (rel_event_list p (X_routing_list) t) /\
              (!x.
                   MEM x (rel_event_list p (X_routing_list) t) ==>
                   x IN events p) ==>
               (prob p (rbd_struct p
                    (parallel (rbd_list (rel_event_list p X_routing_list t)))) =
                1 - list_prod (one_minus_exp t C_routing_list))
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[parallel_struct_thm]
>> RW_TAC list_ss[]
>> RW_TAC std_ss[GSYM one_minus_exp_equi]
>> MATCH_MP_TAC rel_series_parallel_RBD_exp_dist_fail_rate_lemma1
>> RW_TAC list_ss[]
QED

(*-------------------------------------*)
Theorem parallel_series_struct_rbd_v2 :
!p L.  (!z. MEM z L ==> ~NULL z) /\ prob_space p /\
     (!x'. MEM x' (FLAT L) ==> x' IN events p) /\ mutual_indep p (FLAT L) ==>
     (prob p
        (rbd_struct p ((parallel of (λa. series (rbd_list a))) L)) =
         1 - (list_prod o (one_minus_list) of
              (\a. list_prod (list_prob p a))) L)
Proof
RW_TAC std_ss[]
>> (`1 - list_prod
          ((one_minus_list of
            (λa. list_prod (list_prob p a))) L) =
     1 − list_prod
         (one_minus_list (list_prod_rel p L)) `
by RW_TAC std_ss[of_DEF,o_DEF,list_prod_rel_def])
>> RW_TAC std_ss [rel_parallel_series_rbd]
QED


(*---------------------------------------*)

Theorem parallel_series_exp_fail_rate :
!p t L C.
     (!z. MEM z L ==> ~NULL z) /\ 0 <= t /\ prob_space p /\
     (!x'.
        MEM x' (FLAT (two_dim_rel_event_list p L t)) ==> x' IN events p) /\
     (LENGTH C = LENGTH L) /\
     (!n.
        n < LENGTH L /\ n < LENGTH C ==>
        (LENGTH (EL n L) = LENGTH (EL n C))) /\
     two_dim_exp_dist_list p L C ==>
     (1 - (list_prod o (one_minus_list) of
        (\a. list_prod (list_prob p a)))
             (two_dim_rel_event_list p L t) =
     1 - (list_prod o (one_minus_list) of
        (\a. list_prod (exp_func_list a t))) C)
Proof
GEN_TAC >> GEN_TAC
>> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,
                   list_prod_def,list_prob_def,LENGTH_NIL])
>> GEN_TAC >> Induct
   >- (RW_TAC list_ss[])
>> GEN_TAC >> RW_TAC std_ss[]
>> RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,
                  list_prod_def,list_prob_def,one_minus_list_def,exp_func_list_def]
>> (`list_prod (list_prob p (rel_event_list p h t)) =
     list_prod (exp_func_list h' t)`
   by MATCH_MP_TAC rel_prod_series_rbd_exp_dist)
   >- (FULL_SIMP_TAC list_ss[two_dim_exp_dist_list_def,two_dim_rel_event_list_def]
   >> (FIRST_X_ASSUM (Q.SPECL_THEN [`0:num`] MP_TAC)
   >> RW_TAC list_ss[]))
>> POP_ORW
>> FULL_SIMP_TAC std_ss[exp_func_list_def]
>> RW_TAC real_ss[real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
>> RW_TAC real_ss[REAL_EQ_MUL_LCANCEL]
>> DISJ2_TAC
>> FULL_SIMP_TAC real_ss[real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
>> RW_TAC std_ss[GSYM two_dim_rel_event_list_def]
>> FULL_SIMP_TAC std_ss[of_DEF,o_DEF]
>> (FIRST_X_ASSUM (Q.SPECL_THEN [`C':real list list`] MP_TAC))
>> DEP_ASM_REWRITE_TAC[]
>> RW_TAC std_ss[]
>> DEP_ASM_REWRITE_TAC[]
>> FULL_SIMP_TAC list_ss[two_dim_exp_dist_list_def,two_dim_rel_event_list_def]
>> RW_TAC std_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
>> RW_TAC list_ss[]
QED

(*------------------------------------------------*)
Theorem rel_parallel_series_exp_fail_rate :
!p t L C.
     (!z. MEM z L ==> ~NULL z) /\ 0 <= t /\ prob_space p /\
     (!x'.
        MEM x' (FLAT (two_dim_rel_event_list p L t)) ==> x' IN events p) /\
     mutual_indep p (FLAT (two_dim_rel_event_list p L t)) /\
     (LENGTH C = LENGTH L) /\
     (!n.
        n < LENGTH L /\ n < LENGTH C ==>
        (LENGTH (EL n L) = LENGTH (EL n C))) /\
     two_dim_exp_dist_list p L C ==>
(prob p
        (rbd_struct p ((parallel of (λa. series (rbd_list a)))
                    (two_dim_rel_event_list p L t))) =
      1 - (list_prod o (one_minus_list) of
        (\a. list_prod (exp_func_list a t))) C)
Proof

REPEAT GEN_TAC >> REPEAT STRIP_TAC
>> DEP_REWRITE_TAC[parallel_series_struct_rbd_v2]
>> DEP_REWRITE_TAC[parallel_series_exp_fail_rate]
>> RW_TAC std_ss[]
>> POP_ASSUM MP_TAC
>> REWRITE_TAC[two_dim_rel_event_list_def]
>> MATCH_MP_TAC mem_flat_map_not_null3
>> RW_TAC std_ss[]
QED

(*------------------------------------------------*)
Definition RMST_fail_rate_list_def :
(RMST_fail_rate_list a b 0 = []) /\
 (RMST_fail_rate_list a b (SUC n) = [a;b]::(RMST_fail_rate_list a b n))
End

(*------------------------------------------------*)
Theorem RMST_WSN :
!p (t:real)  X_rout X_MLD C_rout C_MLD n.
        (!z. MEM z (RMST_fail_rate_list X_rout X_MLD n)  ==>  ~NULL z) /\
         (0 <=  (t:real)) /\ prob_space p /\
         (!x'.
            MEM x' (FLAT ((two_dim_rel_event_list p
                (RMST_fail_rate_list X_rout X_MLD n)  t))) ==>
            (x' IN events p)) /\
         (mutual_indep p
           (FLAT (two_dim_rel_event_list p
                 (RMST_fail_rate_list X_rout X_MLD n)  t))) /\
         (LENGTH (RMST_fail_rate_list C_rout C_MLD n)  =
          LENGTH (RMST_fail_rate_list X_rout X_MLD n)) /\
         (!n'.
            (n' < LENGTH (RMST_fail_rate_list X_rout X_MLD n)) /\
            (n' < LENGTH (RMST_fail_rate_list C_rout C_MLD n) ) ==>
         (LENGTH (EL n' (RMST_fail_rate_list X_rout X_MLD n)) =
          LENGTH (EL n' (RMST_fail_rate_list C_rout C_MLD n)))) /\
         two_dim_exp_dist_list p ((RMST_fail_rate_list X_rout X_MLD n))
                                 ((RMST_fail_rate_list C_rout C_MLD n)) ==>
(prob p
       (rbd_struct p ((parallel of (λa. series (rbd_list a)))
                    (two_dim_rel_event_list p (RMST_fail_rate_list X_rout X_MLD n) t))) =
      1 - (list_prod o (one_minus_list) of
        (\a. list_prod (exp_func_list a t)))
             (RMST_fail_rate_list C_rout C_MLD n))
Proof
REPEAT GEN_TAC >> REPEAT STRIP_TAC
>> MATCH_MP_TAC rel_parallel_series_exp_fail_rate
>> RW_TAC list_ss[]
QED



val _ = export_theory();
