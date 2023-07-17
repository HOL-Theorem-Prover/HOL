(* ========================================================================= *)
(* File Name: VDCScript.sml                                                  *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Reliability Analysis of Virtual Data Center in HOL    *)
(*                                                                           *)
(*                                                                           *)
(*                HOL4-Kananaskis                                            *)
(*                                                                           *)
(*              Author :  Waqar Ahmed                                        *)
(*                                                                           *)
(*          School of Electrical Engineering and Computer Sciences (SEECS)   *)
(*          National University of Sciences and Technology (NUST), PAKISTAN  *)
(*                                                                           *)
(*                                                                           *)
(* ========================================================================= *)


open HolKernel Parse boolLib bossLib;

open limTheory arithmeticTheory realTheory iterateTheory
    prim_recTheory real_probabilityTheory seqTheory pred_setTheory
    res_quanTheory sortingTheory res_quanTools listTheory
    transcTheory rich_listTheory pairTheory combinTheory realLib
    optionTheory dep_rewrite util_probTheory extrealTheory real_measureTheory
    real_lebesgueTheory real_sigmaTheory satTheory numTheory RBDTheory extra_pred_setTools;

val _ = new_theory "VDC";

(*--------------------*)
val op by = BasicProvers.byA;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)

(* -------------------------------------------------------------------------- *)
(*     Reliability Events Modeling form Random Variable                       *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

Definition fail_event_def :
fail_event p X t = PREIMAGE X {y | y <= Normal t} INTER p_space p
End

Definition rel_event_def :
rel_event p X t = PREIMAGE X {y| Normal t < y} INTER p_space p
End


Definition rel_event_list_def :
rel_event_list p L t =
  MAP (\a. PREIMAGE a {y| Normal t < y} INTER p_space p) L
End

Definition two_dim_rel_event_list_def :
two_dim_rel_event_list p L t =
 MAP (\a.  rel_event_list p a t) L
End

Definition three_dim_rel_event_list_def :
three_dim_rel_event_list p L t =
 MAP (\a. two_dim_rel_event_list p a t) L
End

Definition four_dim_rel_event_list_def :
four_dim_rel_event_list p L t =
 MAP (\a. three_dim_rel_event_list p a t) L
End



(* -------------------------------------------------------------------------- *)
(*  Formalization of Cloud Server Random variable and failure rate lists      *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

Definition log_base_def :
log_base  (b:real) (x:real) = ln x / ln b
End

Definition gen_list_def :
(gen_list L 0 = []) /\
 (gen_list L (SUC n) = SNOC L (gen_list L n))
End

Definition cloud_server_fail_rate_list_def :
cloud_server_fail_rate_list (L: (real) list list) m n =
 gen_list (gen_list L m) n
End

Definition cloud_server_rv_list_def :
cloud_server_rv_list L m n = gen_list (gen_list L m) n
End

Definition CDF_def :
CDF p X (t:real) = distribution p X {y | y <=  Normal t}
End

Definition Reliability_def :
Reliability p X t = 1 - CDF p X t
End

Definition rel_virt_cloud_server_def :
rel_virt_cloud_server p L t =
 prob p
   (rbd_struct p
      ((series of (\a. parallel (rbd_list (rel_event_list p a t)))) L))
End


(* -------------------------------------------------------------------------- *)
(*   Formalization of Exponential Function and Distribution                  *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

Definition exp_func_list_def :
exp_func_list C t = MAP (\a:real. exp (- (a*t))) C
End

Definition exp_dist_def :
exp_dist p X l =
!t:real. CDF p X (t) = (if (0 <=  t) then 1 - exp(-l * t) else 0)
End

Definition exp_dist_list_def :
(exp_dist_list p [] L =  T) /\
((exp_dist_list p (h::t) L) =
((exp_dist p h (HD L)) /\ exp_dist_list p t (TL L)))
End

Definition two_dim_exp_dist_list_def :
(two_dim_exp_dist_list p [] L = T) /\
 (two_dim_exp_dist_list p (h::t) L =
 ((exp_dist_list p h (HD L)) /\ two_dim_exp_dist_list p t (TL L)))
End

Definition three_dim_exp_dist_list_def :
(three_dim_exp_dist_list p [] L = T) /\
(three_dim_exp_dist_list p (h::t) L =
((two_dim_exp_dist_list p h (HD L)) /\ three_dim_exp_dist_list p t (TL L)))
End

Definition four_dim_exp_dist_list_def :
(four_dim_exp_dist_list p [] L = T) /\
 (four_dim_exp_dist_list p (h::t) L =
 ((three_dim_exp_dist_list p h (HD L)) /\ four_dim_exp_dist_list p t (TL L)))
End

Definition gen_rv_list_def :
gen_rv_list (X:'a->extreal) n = gen_list X n
End



(* ========================================================================== *)
(*    Essential Lemmas for Virtual Data Center Formalization                  *)
(*                                                                            *)
(*                                                                            *)
(* ========================================================================== *)

Theorem not_null_map :
!f l.  ~NULL l ==> ~NULL (MAP f l)
Proof
RW_TAC std_ss[]
>> Induct_on `l`
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[]
QED

(*-----------------------------*)
Theorem extreal_not_le :
!x y. ~(x < y) = ~(~(y <=  x))
Proof
RW_TAC std_ss []
>> PROVE_TAC[extreal_lt_def]
QED
(*---------------*)
Theorem compl_rel_event_eq_fail_event :
!p t s.
     prob_space p ==>
     (p_space p DIFF PREIMAGE s {y | Normal t < y} INTER p_space p =
      PREIMAGE s {y | y <= Normal t} INTER p_space p)
Proof
SRW_TAC[][PREIMAGE_def,DIFF_DEF,EXTENSION,GSPECIFICATION,REAL_NOT_LT]
>> SET_TAC[extreal_not_le]
QED

(*---------------*)
Theorem gen_list_suc :
!L (n:num). (gen_list L (SUC n) = L::gen_list L n)
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[gen_list_def,SNOC])
>> RW_TAC list_ss[gen_list_def,SNOC]
>> SRW_TAC [] [gen_list_def, SNOC]
>> FULL_SIMP_TAC list_ss[gen_list_def, SNOC_APPEND]
QED
(*---------------*)
Theorem compl_fail_event_eq_rel_event :
!X t p. p_space p DIFF fail_event p X t = rel_event p X t
Proof
  RW_TAC std_ss[fail_event_def,rel_event_def]
  >> SRW_TAC[][IN_DIFF,PREIMAGE_def,EXTENSION,GSPECIFICATION]
  >> RW_TAC std_ss[GSYM extreal_lt_def]
  >> METIS_TAC[]
QED
(*---------------*)
Theorem comp_rel_event_eq_fail_event :
!X t p. p_space p DIFF rel_event p X t = fail_event p X t
Proof
RW_TAC std_ss[fail_event_def,rel_event_def]
>> SRW_TAC[][IN_DIFF,PREIMAGE_def,EXTENSION,GSPECIFICATION]
>> RW_TAC std_ss[extreal_lt_def]
>> METIS_TAC[]
QED
(*---------------*)

Theorem rel_series_parallel_RBD_exp_dist_fail_rate_lemma1 :
!p t l c.
       (0 <= t) /\
       prob_space p /\
       (LENGTH l = LENGTH c) /\
       (!x'. MEM x' (((rel_event_list p (l ) t))) ==> (x' IN events p)) /\
       exp_dist_list p l c ==>
       ((1 −
         list_prod (one_minus_list (list_prob p (rel_event_list p l t)))) =
        (1 − list_prod (one_minus_list (exp_func_list c t))))
Proof
GEN_TAC
>> GEN_TAC
>> Induct
   >- (RW_TAC list_ss[LENGTH,LENGTH_NIL_SYM,rel_event_list_def,list_prob_def,exp_func_list_def,one_minus_list_def,list_prod_def])
   >> Induct_on `c`
   >- (RW_TAC list_ss[LENGTH,LENGTH_EQ_NUM_compute,rel_event_list_def,list_prob_def,exp_func_list_def,one_minus_list_def,list_prod_def])
   >> RW_TAC list_ss[rel_event_list_def,list_prob_def,exp_func_list_def,one_minus_list_def,list_prod_def]
   >> FULL_SIMP_TAC std_ss[exp_dist_list_def,HD,exp_dist_def]
   >> DEP_REWRITE_TAC[GSYM PROB_COMPL]
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC list_ss[]
   >> DEP_REWRITE_TAC[compl_rel_event_eq_fail_event]
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC std_ss[CDF_def,distribution_def]
   >> FIRST_X_ASSUM (Q.SPECL_THEN [`c`] MP_TAC)
   >> RW_TAC std_ss[]
   >> FULL_SIMP_TAC list_ss[rel_event_list_def]
   >> FULL_SIMP_TAC std_ss[]
   >> (`(!x'.
         MEM x'
           (MAP (\a. PREIMAGE a {y | Normal t < y} ∩ p_space p) l) ==>
         x' IN events p)` by RW_TAC std_ss[])
   >> FULL_SIMP_TAC std_ss[real_sub,REAL_EQ_LADD,REAL_EQ_NEG]
   >> RW_TAC real_ss[exp_func_list_def]
QED

(*---------------*)
Theorem rel_series_parallel_RBD_exp_dist_fail_rate :
!p (t:real) L (C:real list list).
        (!z. MEM z L  ==>  ~NULL z) /\
         (0 <=  (t:real)) /\ prob_space p /\
         (!x'.
            MEM x' (FLAT ((two_dim_rel_event_list p L t))) ==>
            (x' IN events p)) /\
         (mutual_indep p (FLAT (two_dim_rel_event_list p L t))) /\
         (LENGTH C = LENGTH L) /\
         (!n.
              (n < LENGTH L) /\ (n < LENGTH C) ==>
              (LENGTH (EL n L) = LENGTH (EL n C))) /\
         two_dim_exp_dist_list p L C ==>
           (prob p
                (rbd_struct p ((series of (\a. parallel (rbd_list a)))
                            (two_dim_rel_event_list p L t))) =
           (list_prod of
                 (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH,LENGTH_EQ_NUM_compute,two_dim_rel_event_list_def,of_DEF,o_DEF,rbd_list_def,rbd_struct_def,list_prod_def,PROB_UNIV])
>> Induct_on `C`
>- (RW_TAC list_ss[LENGTH,exp_func_list_def,one_minus_list_def,list_prod_def])
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[]
>> DEP_REWRITE_TAC[series_parallel_struct_thm]
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
   >- (RW_TAC std_ss[rel_event_list_def]
      >> DEP_REWRITE_TAC[not_null_map]
      >> FULL_SIMP_TAC list_ss[])
   >> FULL_SIMP_TAC list_ss[MEM_MAP]
   >> RW_TAC std_ss[rel_event_list_def]
   >> DEP_REWRITE_TAC[not_null_map]
   >> FULL_SIMP_TAC list_ss[])
>> RW_TAC list_ss[two_dim_rel_event_list_def,list_prod_one_minus_rel_def, of_DEF,o_DEF,rbd_list_def,rbd_struct_def,exp_func_list_def,one_minus_list_def,list_prod_def]
>> MP_TAC(Q.ISPECL [`p:('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real)`, `t:real`,`h':('a->extreal) list`,`h:real list`]
       rel_series_parallel_RBD_exp_dist_fail_rate_lemma1)
>> RW_TAC std_ss[]
>> (`(LENGTH h' = LENGTH h) /\
       (!x'. MEM x' (rel_event_list p h' t) ==> x' IN events p) /\
       exp_dist_list p h' h` by RW_TAC std_ss[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
   >>  RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[ two_dim_exp_dist_list_def])
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC std_ss[GSYM list_prod_one_minus_rel_def,GSYM two_dim_rel_event_list_def]
>> DEP_REWRITE_TAC[GSYM series_parallel_struct_thm]
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC std_ss[two_dim_rel_event_list_def,MEM_MAP]
    >> DEP_REWRITE_TAC[rel_event_list_def,not_null_map]
    >> FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
   >> DEP_REWRITE_TAC[mutual_indep_front_append]
   >> EXISTS_TAC(``rel_event_list p h' t ``)
   >> RW_TAC std_ss[])
>> FIRST_X_ASSUM (Q.SPECL_THEN [`C':real list list`] MP_TAC)
>> RW_TAC std_ss[]
>> (`(!z. MEM z L ==> ~NULL z) /\
       (!x'.
          MEM x' (FLAT (two_dim_rel_event_list p L t)) ==>
          x' IN events p) /\
       mutual_indep p (FLAT (two_dim_rel_event_list p L t)) /\
       (LENGTH C' = LENGTH L) /\
       (!n.
          n < LENGTH L /\ n < LENGTH C' ==>
          (LENGTH (EL n L) = LENGTH (EL n C'))) /\
       two_dim_exp_dist_list p L C'` by RW_TAC std_ss[])
>- (FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
    >> DEP_REWRITE_TAC[mutual_indep_front_append]
    >> EXISTS_TAC(``rel_event_list p h' t ``)
    >> RW_TAC std_ss[])
>- (FULL_SIMP_TAC list_ss[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
    >>  RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[two_dim_exp_dist_list_def])
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC list_ss[exp_func_list_def]
>> RW_TAC real_ss[of_DEF,o_DEF]
QED
(*-----------------------------*)
Theorem rbd_virtual_cloud_server_alt_form :
!p t L. prob_space p ==>
  ((rbd_struct p
     ((series of (\a. parallel (rbd_list (rel_event_list p a t)))) L)) =
  (rbd_struct p ((series of (\a. parallel (rbd_list a))) (two_dim_rel_event_list p L t))))
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,rbd_list_def,rbd_struct_def])
>> RW_TAC std_ss[]
>> RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,rbd_list_def,rbd_struct_def]
>> FULL_SIMP_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,rbd_list_def,rbd_struct_def]
QED


(******************************************************************************)
(*                                                                            *)
(*       Reliability of Virtualization Configuration in a Cloud Server        *)
(*                                                                            *)
(******************************************************************************)

(*----------------------------*)
Theorem rel_virtual_cloud_server :
!L_VM L_VMM L_HW C_VM C_VMM C_HW p t.  (~NULL (L_VM))/\
(0 <=  t) /\ prob_space p /\
(!x'. MEM x' ((rel_event_list p (L_VMM::L_HW::L_VM) t)) ==> (x' IN events p)) /\
(mutual_indep p ((rel_event_list p (L_VMM::L_HW::L_VM) t))) /\
(LENGTH (C_VM) = LENGTH (L_VM)) /\
(exp_dist_list p ((L_VMM::L_HW::L_VM) ) ((C_VMM::C_HW::C_VM))) ==>
(prob p
        (rbd_struct p
           ((series of (\a. parallel (rbd_list (rel_event_list p a t))))
              (([L_VMM::L_HW::L_VM])))) =
      (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) (([C_VMM::C_HW::C_VM])))
Proof
RW_TAC list_ss[]
>> DEP_REWRITE_TAC[rbd_virtual_cloud_server_alt_form]
>> RW_TAC std_ss[]
>> (`prob p
  (rbd_struct p
     ((series of (\a. parallel (rbd_list a)))
        (two_dim_rel_event_list p [L_VMM::L_HW::L_VM] t))) = (list_prod of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) [C_VMM::C_HW::C_VM] ` by MATCH_MP_TAC rel_series_parallel_RBD_exp_dist_fail_rate)
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def,rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def,rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC[ONE]
   >> REWRITE_TAC[LT_SUC]
   >> RW_TAC arith_ss[]
   >> RW_TAC list_ss[])
>> RW_TAC list_ss[two_dim_exp_dist_list_def]
QED

(*---------------------------*)
Theorem seq_rel_prod_tend_0 :
!(n:num) p X t . (0 <=  (t:real)) /\ possibly p ((rel_event p X t)) /\   prob_space p ==> ((\n.
   list_prod
     (one_minus_list
        (list_prob p (rel_event_list p (gen_rv_list X n) t)))) --> 0)
Proof
RW_TAC std_ss[]
>> (`(!n:num. (
   list_prod
     (one_minus_list
        (list_prob p (rel_event_list p (gen_rv_list X n) t)))) = (1 - Reliability p X t) pow n)` by ALL_TAC)
   >- (Induct
      >- (RW_TAC list_ss[gen_rv_list_def,gen_list_def,rel_event_list_def,list_prob_def,one_minus_list_def,list_prod_def]
         >> RW_TAC real_ss[pow])
      >> RW_TAC list_ss[gen_rv_list_def,gen_list_suc]
      >> RW_TAC list_ss[rel_event_list_def,list_prob_def,one_minus_list_def,list_prod_def]
      >> RW_TAC real_ss[Reliability_def,distribution_def,CDF_def]
      >> (`(1 - prob p (PREIMAGE X {y | Normal t < y} INTER p_space p)) =
            prob p (p_space p  DIFF (PREIMAGE X {y | Normal t < y} INTER p_space p))` by DEP_REWRITE_TAC[GSYM PROB_COMPL])
      >- (RW_TAC std_ss[]
         >> FULL_SIMP_TAC std_ss[possibly_def]
         >> FULL_SIMP_TAC list_ss[rel_event_def])
      >> FULL_SIMP_TAC list_ss[rel_event_list_def,rel_event_def,gen_rv_list_def]
      >> RW_TAC real_ss[]
      >> RW_TAC std_ss[GSYM rel_event_def,GSYM fail_event_def]
      >> RW_TAC std_ss[comp_rel_event_eq_fail_event]
      >> RW_TAC real_ss[pow]
      >> RW_TAC std_ss[Reliability_def,CDF_def,distribution_def]
      >> RW_TAC std_ss[GSYM rel_event_def,GSYM fail_event_def]
      >> RW_TAC real_ss[])
  >> POP_ORW
  >> DEP_REWRITE_TAC[SEQ_POWER]
  >> RW_TAC real_ss[Reliability_def,distribution_def,CDF_def]
  >> RW_TAC std_ss[GSYM fail_event_def,GSYM comp_rel_event_eq_fail_event]
  >> DEP_REWRITE_TAC[PROB_COMPL]
  >> FULL_SIMP_TAC std_ss[possibly_def]
  >> DEP_REWRITE_TAC[ABS_1_MINUS_PROB]
  >> RW_TAC std_ss[]
QED
(*--------rel_prod_tend_0----*)
Theorem rel_prod_tend_0 :
!(n:num) p X t. (0 <=  (t:real)) /\
      possibly p ((rel_event p X t)) /\
      prob_space p ==>
      (lim (\ (n:num). ( list_prod (one_minus_list (list_prob p (rel_event_list p (gen_rv_list (X:('a -> extreal)) n) t))))) =  (0:real))
Proof
RW_TAC std_ss[]
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\n.
       list_prod
         (one_minus_list
            (list_prob p (rel_event_list p (gen_rv_list X n) t))))``)
>> RW_TAC std_ss[]
>- (RW_TAC std_ss[GSYM SEQ_LIM,convergent]
   >> EXISTS_TAC (`` (0:real)``)
   >> DEP_REWRITE_TAC[seq_rel_prod_tend_0]
   >> RW_TAC std_ss[])
>> DEP_REWRITE_TAC[seq_rel_prod_tend_0]
>> RW_TAC std_ss[]
QED

(*------------------------*)
Theorem bound_mult_ratr :
! (a:real) (b:real) c :real. (0 < c) ==> ((a * (b / c) = (a * b ) / c))
Proof
RW_TAC std_ss[]
>> (`~(c = (0:real))` by DEP_REWRITE_TAC[REAL_POS_NZ])
>- (RW_TAC std_ss[])
>> DEP_ASM_REWRITE_TAC[mult_ratr]
QED
(*-------------------------*)
Theorem bound_log_inequal :
! (a:real) (b:real) (c:real) (e:real)  n.
    (0 <= e) /\ (e < 1) /\ (a < b) /\ (0 < n) /\  (0 <  b) /\
    (a =  e * b * (1 - (1 - c) pow n)) /\  (0 < c /\ c <  1) ==>
    (&n > (log_base 10 (1 - a / b) / log_base 10 (1 - c)))
Proof
REPEAT GEN_TAC
>> DISCH_TAC
>> ONCE_REWRITE_TAC [real_gt]
>> (`((log_base 10 (1 - a / b) / log_base 10 (1 - c)) < &n) =
    ((&n * log_base 10 (1 - (c:real))) < log_base 10 (1 - a / b))  ` by ALL_TAC)
>- (DEP_REWRITE_TAC[REAL_LT_RDIV_EQ_NEG]
   >> RW_TAC std_ss[log_base_def]
   >> (`(ln (1 - c) / ln 10 < 0) = (ln(1 - c) < 0 * ln 10)` by DEP_REWRITE_TAC[REAL_LT_LDIV_EQ])
   >- (RW_TAC std_ss[GSYM LN_1]
      >> DEP_REWRITE_TAC[LN_MONO_LT]
      >> RW_TAC real_ss[])
   >> POP_ORW
   >> RW_TAC real_ss[]
   >> RW_TAC std_ss[GSYM LN_1]
   >> DEP_REWRITE_TAC[LN_MONO_LT]
   >> RW_TAC real_ss[]
   >- (RW_TAC real_ss[real_sub,REAL_LT_ADDNEG])
   >> RW_TAC real_ss[REAL_LT_SUB_RADD,REAL_LT_ADDR])
>> POP_ORW
>> RW_TAC std_ss[log_base_def]
>> DEP_REWRITE_TAC[bound_mult_ratr]
>> RW_TAC std_ss[]
>- (RW_TAC std_ss[GSYM LN_1]
   >> DEP_REWRITE_TAC[LN_MONO_LT]
   >> RW_TAC real_ss[])
>> DEP_REWRITE_TAC[REAL_LT_RDIV]
>> RW_TAC std_ss[GSYM LN_1]
>- (DEP_REWRITE_TAC[LN_MONO_LT]
   >> RW_TAC real_ss[])
>> (`&n * ln (1 - c) = ln ((1- c) pow n)` by MATCH_MP_TAC EQ_SYM)
>- (DEP_REWRITE_TAC[LN_POW]
   >> RW_TAC real_ss[real_sub,REAL_LT_ADDNEG])
>> POP_ORW
>> DEP_REWRITE_TAC[LN_MONO_LT]
>> RW_TAC real_ss[]
>- (DEP_REWRITE_TAC[REAL_POW_LT]
   >> RW_TAC real_ss[real_sub,REAL_LT_ADDNEG])
>- (RW_TAC real_ss[real_sub,REAL_LT_ADDNEG]
   >> DEP_REWRITE_TAC[REAL_LT_1]
   >> RW_TAC real_ss[]
   >- (DEP_REWRITE_TAC[REAL_LE_LT_MUL]
      >> RW_TAC real_ss[]
      >> RW_TAC real_ss[REAL_LT_ADDNEG]
      >> ONCE_REWRITE_TAC[GSYM POW_ONE]
      >> Cases_on `n`
      >- (RW_TAC real_ss[])
      >> DEP_REWRITE_TAC[POW_LT]
      >> RW_TAC real_ss[]
      >- (RW_TAC real_ss[GSYM real_sub,REAL_SUB_LE]
        >> DEP_REWRITE_TAC[REAL_LT_IMP_LE]
        >> RW_TAC real_ss[POW_ONE])
      >> RW_TAC real_ss[GSYM real_sub,POW_ONE]
      >> (`((1 - c) < 1) = ((1 - (c:real)) < (1 - (0:real)))` by RW_TAC real_ss[])
      >> POP_ORW
      >> ONCE_REWRITE_TAC[real_sub]
      >> RW_TAC real_ss[REAL_LT_LADD]
      >> ONCE_REWRITE_TAC[GSYM REAL_NEG_0]
      >> RW_TAC real_ss[REAL_LT_NEG])
   >> RW_TAC real_ss[GSYM real_sub])
>> RW_TAC real_ss[real_sub]
>> RW_TAC real_ss[GSYM REAL_LT_SUB_RADD]
>> ONCE_REWRITE_TAC[REAL_ADD_COMM]
>> RW_TAC real_ss[GSYM REAL_LT_SUB_LADD]
>> DEP_REWRITE_TAC[REAL_LT_LDIV_EQ]
>> RW_TAC real_ss[]
>> RW_TAC std_ss[GSYM  real_sub]
>> (`(1 − (1 − c) pow n) * (b:real) = 1 * (1 − (1 − c) pow n) * (b:real)` by RW_TAC real_ss[])
>> POP_ORW
>> ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC]
>> (`((b:real) * (1 − (1 − c) pow n)) = ((1 − (1 − c) pow n) * (b:real))` by RW_TAC std_ss[REAL_MUL_COMM])
>> POP_ORW
>> MATCH_MP_TAC REAL_LT_RMUL_IMP
>> RW_TAC real_ss[]
>> DEP_REWRITE_TAC[REAL_LT_RMUL_0]
>> RW_TAC real_ss[]
>> RW_TAC real_ss[real_sub,REAL_LT_ADDNEG]
>> ONCE_REWRITE_TAC[GSYM POW_ONE]
>> Cases_on `n`
>- (RW_TAC real_ss[])
>> DEP_REWRITE_TAC[POW_LT]
>> RW_TAC real_ss[]
>- (RW_TAC real_ss[GSYM real_sub,REAL_SUB_LE]
   >> DEP_REWRITE_TAC[REAL_LT_IMP_LE]
   >> RW_TAC real_ss[POW_ONE])
>> RW_TAC real_ss[POW_ONE]
>> (`(1 + -c < 1) = (((1:real) + -c) < (1 + (-0:real)))` by RW_TAC real_ss[])
>> POP_ORW
>> DEP_REWRITE_TAC[REAL_LT_LADD]
>> ONCE_REWRITE_TAC[GSYM REAL_NEG_0]
>> RW_TAC real_ss[REAL_LT_NEG]
QED
(*-------------------------*)
Theorem nlen_gen_list_eq_n1 :
 !L n . LENGTH (gen_list L n) = n
Proof
RW_TAC std_ss[]
>> Induct_on `n`
>- (RW_TAC list_ss[gen_list_def])
>> RW_TAC list_ss[gen_list_def]
QED

(*-------------------------*)
Theorem nlen_gen_list_eq_n :
!L n t p . LENGTH (rel_event_list p (gen_rv_list L n) t) = n
Proof
RW_TAC std_ss[]
>> Induct_on `n`
>- (RW_TAC list_ss[gen_rv_list_def,rel_event_list_def,gen_list_def])
>> RW_TAC list_ss[gen_rv_list_def,rel_event_list_def,gen_list_def,nlen_gen_list_eq_n1]
QED

(*-------------------------*)
Theorem compl_rel_pow_n :
!X p t n.
      prob_space p /\
      (rel_event p X t IN events p) ==>
      (list_prod
        (one_minus_list
           (list_prob p (rel_event_list p (gen_rv_list X n) t)))  =
      (1 - Reliability p X t) pow n)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[gen_rv_list_def,gen_list_def,rel_event_list_def,list_prod_def,list_prob_def,one_minus_list_def,pow])
>> RW_TAC list_ss[gen_rv_list_def,rel_event_list_def,of_DEF,list_prod_def,list_prob_def,one_minus_list_def,pow,gen_list_suc]
>> FULL_SIMP_TAC list_ss[gen_rv_list_def,rel_event_list_def]
>> RW_TAC real_ss[Reliability_def,CDF_def,distribution_def]
>> RW_TAC std_ss[GSYM rel_event_def,GSYM fail_event_def]
>> DEP_REWRITE_TAC[GSYM PROB_COMPL]
>> RW_TAC real_ss[]
>> RW_TAC std_ss[comp_rel_event_eq_fail_event]
QED

(*-------------------------*)
Theorem virt_config_bounds :
!X_VM X_VMM X_HW p n t.
      prob_space p /\
      (0 <=  t) /\
      (~NULL (rel_event_list p (gen_rv_list X_VM n) t)) /\
      (rel_event p X_VMM t IN events p)  /\
      (rel_event p X_VM t IN events p) /\
      (rel_event p X_HW t IN events p) /\
      (!x'.
         MEM x' (rel_event_list p (gen_rv_list X_VM n) t) ==>
         x' IN events p) /\
      (rel_virt_cloud_server p ([X_VMM]::[X_HW] ::[gen_rv_list X_VM n]) t <
        Reliability p X_VMM t) /\
      (Reliability p X_HW t < 1) /\
      (0 < Reliability p X_VMM t) /\
      (0 < Reliability p X_VM t /\ Reliability p X_VM t < 1) /\
      mutual_indep p
        (rel_event_list p (X_VMM::X_HW::gen_rv_list X_VM n) t) ==>
      (&n >
      log_base (10)
        (1 -
         ((rel_virt_cloud_server p ([X_VMM]::[X_HW] ::[gen_rv_list X_VM n]) t) /
         Reliability p X_VMM t)) /
      log_base (10) (1 - Reliability p X_VM t))
Proof
RW_TAC std_ss[]
>> MATCH_MP_TAC bound_log_inequal
>> EXISTS_TAC(``Reliability p X_HW t``)
>> RW_TAC real_ss[]
>- (RW_TAC real_ss[Reliability_def,CDF_def,distribution_def]
   >> RW_TAC std_ss[REAL_SUB_LE]
   >> DEP_REWRITE_TAC[PROB_LE_1 ]
   >> RW_TAC std_ss[GSYM fail_event_def]
   >> RW_TAC std_ss[GSYM comp_rel_event_eq_fail_event]
   >> DEP_REWRITE_TAC[EVENTS_COMPL]
   >> RW_TAC std_ss[])
>- ((`n = LENGTH (rel_event_list p (gen_rv_list X_VM n) t)` by MATCH_MP_TAC EQ_SYM)
   >- (RW_TAC std_ss[ nlen_gen_list_eq_n])
   >> POP_ORW
   >> FULL_SIMP_TAC std_ss[GSYM LENGTH_NOT_NULL]
   >> FULL_SIMP_TAC list_ss[gen_rv_list_def,rel_event_list_def,gen_list_def] )
>> RW_TAC std_ss[rel_virt_cloud_server_def]
>> DEP_REWRITE_TAC[rbd_virtual_cloud_server_alt_form]
>> RW_TAC real_ss[]
>> DEP_REWRITE_TAC[series_parallel_struct_thm_v2]
>> RW_TAC real_ss[]
>- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
   >- (FULL_SIMP_TAC list_ss[rel_event_list_def])
   >> FULL_SIMP_TAC list_ss[rel_event_list_def])
   >- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
      >- (FULL_SIMP_TAC list_ss[rel_event_list_def]
         >> RW_TAC std_ss[GSYM rel_event_def])
      >> FULL_SIMP_TAC list_ss[rel_event_list_def]
      >> RW_TAC std_ss[GSYM rel_event_def])
   >- (FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def,rel_event_list_def])
>> RW_TAC list_ss[two_dim_rel_event_list_def,rel_event_list_def,of_DEF,o_DEF,list_prod_def,list_prob_def,one_minus_list_def]
>> RW_TAC real_ss[Reliability_def,CDF_def,distribution_def]
>> RW_TAC std_ss[GSYM rel_event_def,GSYM rel_event_list_def]
>> DEP_REWRITE_TAC[compl_rel_pow_n]
>> RW_TAC real_ss[]
>> RW_TAC real_ss[Reliability_def,CDF_def,distribution_def]
>> RW_TAC std_ss[GSYM rel_event_def,GSYM fail_event_def]
>> DEP_REWRITE_TAC[GSYM PROB_COMPL]
>> RW_TAC std_ss[]
>- (RW_TAC std_ss[GSYM comp_rel_event_eq_fail_event]
   >> DEP_REWRITE_TAC[EVENTS_COMPL]
   >> RW_TAC std_ss[])
>- (RW_TAC std_ss[GSYM comp_rel_event_eq_fail_event]
   >> DEP_REWRITE_TAC[EVENTS_COMPL]
   >> RW_TAC std_ss[])
>> RW_TAC std_ss[compl_fail_event_eq_rel_event]
>> REAL_ARITH_TAC
QED

(*-------------------------*)
Theorem mem_flat_map_not_null2 :
!f L.
     (!y. ~NULL (f y)) /\ (!z. MEM z L ==> ~NULL z) ==>
     (!z. MEM z (MAP f L) ==> ~NULL z)
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[]
QED
(*----------------------*)
Theorem mem_flat_map_not_null3 :
!p t L.  (!z. MEM z ((L)) ==> ~NULL z) ==> (!z. MEM z (((MAP (\a. rel_event_list p a t) L))) ==> ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[rel_event_list_def]
>> RW_TAC std_ss[not_null_map]
QED
(*-----------------------*)
Theorem mem_flat_map_not_null1 :
!p t L.
     (!z. MEM z (FLAT L) ==> ~NULL z) ==>
     (!z.
        MEM z (FLAT (MAP (\a. two_dim_rel_event_list p a t) L)) ==>
        ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def]
>> DEP_REWRITE_TAC[mem_flat_map_not_null3]
>> EXISTS_TAC(``p:'a event # 'a event event # ('a event -> real)``)
>> EXISTS_TAC(``t:real``)
>> EXISTS_TAC(``h:('a->extreal) list list``)
>> FULL_SIMP_TAC list_ss[]
QED

(*----------------------------*)
Theorem mem_flat_map_not_null :
!p t L.
      (!z. MEM z (FLAT (FLAT L)) ==> ~NULL z) ==>
      (!z.
         MEM z (FLAT (FLAT (MAP (\a. three_dim_rel_event_list p a t) L))) ==>
         ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[three_dim_rel_event_list_def])
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def]
>> DEP_REWRITE_TAC[mem_flat_map_not_null1]
>> EXISTS_TAC(``p:'a event # 'a event event # ('a event -> real)``)
>> EXISTS_TAC(``t:real``)
>> EXISTS_TAC(``h:('a->extreal) list list list``)
>> FULL_SIMP_TAC list_ss[]
QED
(*-------------------------------*)
Theorem parallel_series_parallel_rbd_alt_form :
!p t L.
      prob_space p ==>
      (rbd_struct p
         ((parallel of series of (\a. parallel (rbd_list a)))
            (three_dim_rel_event_list p L t)) =
       rbd_struct p
         ((parallel of series of
            (\a. parallel (rbd_list (rel_event_list p a t)))) L))
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[three_dim_rel_event_list_def,rel_event_list_def,of_DEF,o_DEF])
>> RW_TAC list_ss[three_dim_rel_event_list_def,rel_event_list_def,of_DEF,o_DEF,rbd_list_def,rbd_struct_def]
>> FULL_SIMP_TAC std_ss[three_dim_rel_event_list_def,two_dim_rel_event_list_def,of_DEF,o_DEF]
>> MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `t:real`, `h:('a->extreal) list list`] (GSYM rbd_virtual_cloud_server_alt_form))
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC std_ss[of_DEF,o_DEF]
>> ONCE_ASM_REWRITE_TAC[]
>> RW_TAC list_ss[rel_event_list_def,rel_event_def]
>> RW_TAC std_ss[GSYM rel_event_list_def,GSYM two_dim_rel_event_list_def]
QED

(*-------------------------------*)
Theorem nested_series_parallel_rbd_alt_form :
!p t L.
     prob_space p ==>
     (rbd_struct p
           ((series of parallel of series of
             (\a. parallel (rbd_list a))) (four_dim_rel_event_list p L t)) =
      rbd_struct p
           ((series of parallel of series of
             (\a. parallel (rbd_list (rel_event_list p a t)))) L))
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[four_dim_rel_event_list_def,rel_event_list_def,of_DEF,o_DEF])
>> RW_TAC list_ss[four_dim_rel_event_list_def,rel_event_list_def,of_DEF,o_DEF,rbd_list_def,rbd_struct_def]
>> RW_TAC std_ss[GSYM four_dim_rel_event_list_def,GSYM rel_event_list_def]
>> FULL_SIMP_TAC std_ss[of_DEF,o_DEF]
>> MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `t:real`, `h:('a->extreal) list list list`] (parallel_series_parallel_rbd_alt_form))
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC std_ss[of_DEF,o_DEF]
>> ONCE_ASM_REWRITE_TAC[]
>> RW_TAC list_ss[rel_event_list_def,rel_event_def]
>> RW_TAC std_ss[GSYM rel_event_list_def,GSYM two_dim_rel_event_list_def]
>> FULL_SIMP_TAC std_ss[of_DEF,o_DEF]
QED

(*-------------------------------*)
Theorem mem_flat_fun_eq_mem_flat_null_list1 :
!p t L. ~NULL L ==> ~NULL (rel_event_list p L t)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[rel_event_list_def])
>> RW_TAC list_ss[rel_event_list_def]
QED
(*-------------------------------*)
Theorem mem_flat_fun_eq_mem_flat_null_list2 :
!p t L. (!z. MEM z (FLAT (L)) ==> ~NULL z) ==>
  (!z. MEM z
        (FLAT
           (MAP
              (\a.
                 MAP
                   (\a.
                      MAP
                        (\a. PREIMAGE a {y | Normal t < y} ∩ p_space p)
                        a) a) L)) ==> ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
>> RW_TAC list_ss[four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
>- (FULL_SIMP_TAC list_ss[MEM_MAP]
   >> RW_TAC std_ss[GSYM rel_event_list_def]
   >> DEP_REWRITE_TAC[ mem_flat_fun_eq_mem_flat_null_list1]
   >> FULL_SIMP_TAC list_ss[])
>> METIS_TAC[]
QED
(*-------------------------------*)
Theorem mem_flat_fun_eq_mem_flat_null_list3 :
!p t L.
       (!z. MEM z L ==> ~NULL z) ==>
       !z. MEM z (two_dim_rel_event_list p L t) ==> ~NULL z
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[two_dim_rel_event_list_def,rel_event_list_def])
>> RW_TAC list_ss[two_dim_rel_event_list_def,rel_event_list_def]
>- (RW_TAC std_ss[GSYM rel_event_list_def]
   >> MATCH_MP_TAC mem_flat_fun_eq_mem_flat_null_list1
   >> METIS_TAC[])
>> FULL_SIMP_TAC list_ss[two_dim_rel_event_list_def,rel_event_list_def]
QED
(*-------------------------------*)
Theorem mem_flat_fun_eq_mem_flat_null_list :
!p t L.
     (!z. MEM z (FLAT (FLAT L)) ==> ~NULL z) ==>
     (!z.
       MEM z (FLAT (FLAT (four_dim_rel_event_list p L t))) ==>
       ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
>> RW_TAC list_ss[four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
>- (POP_ASSUM MP_TAC
   >> MATCH_MP_TAC mem_flat_fun_eq_mem_flat_null_list2
   >> METIS_TAC[])
>> FULL_SIMP_TAC list_ss[four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
QED

(*---------------------------*)
Theorem parallel_series_parallel_prod_rel_exp_dist :
!p t L C.
     (0 <= t) /\ prob_space p /\ (LENGTH C = LENGTH L) /\
     mutual_indep p (FLAT (FLAT (three_dim_rel_event_list p L t))) /\
     (!x'.
        MEM x' (FLAT (FLAT (three_dim_rel_event_list p L t))) ==>
        x' IN events p) /\ (!z. MEM z (FLAT (L)) ==> ~NULL z) /\
     three_dim_exp_dist_list p L C /\
     (!n' n.
        (n' < LENGTH L) /\ (n' < LENGTH C) /\ (n < LENGTH (EL n' L)) /\
        (n < LENGTH (EL n' C)) ==>
        (LENGTH (EL n (EL n' L)) = LENGTH (EL n (EL n' C))))  /\
     (!n.
        (n < LENGTH L) /\ (n < LENGTH C) ==>
        (LENGTH (EL n L) = LENGTH (EL n C)))  ==>
     ((1 −
       list_prod
         (one_minus_list
           (MAP
              ((\a. list_prod a) of
               (\a. 1 − list_prod (one_minus_list (list_prob p a))))
              (three_dim_rel_event_list p L t)))) =
      (1 −
       list_prod
        (one_minus_list
          (MAP
            ((\a. list_prod a) of
             (\a. 1 − list_prod (one_minus_list (exp_func_list a t))))
            C))))
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,exp_func_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def,list_prod_def,list_prob_def,one_minus_list_def,LENGTH_NIL])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,exp_func_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def,list_prod_def,list_prob_def,one_minus_list_def])
>> RW_TAC std_ss[]
>> RW_TAC list_ss[of_DEF,exp_func_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def,list_prod_def,list_prob_def,one_minus_list_def]
>> RW_TAC std_ss[GSYM rel_event_list_def,GSYM two_dim_rel_event_list_def,GSYM one_minus_list_def]
>> (`(1 −
 list_prod
   (MAP (\a. 1 − list_prod (one_minus_list (list_prob p a)))
      (two_dim_rel_event_list p h t))) = 1 - (list_prod of
       (\a. 1 − list_prod (one_minus_list (list_prob p a)))) (two_dim_rel_event_list p h t)` by RW_TAC list_ss[of_DEF,o_DEF])
>> POP_ORW
>> DEP_REWRITE_TAC[GSYM series_parallel_struct_thm_v2]
>> RW_TAC std_ss[]
>- (POP_ASSUM MP_TAC
   >> MATCH_MP_TAC mem_flat_fun_eq_mem_flat_null_list3
   >> FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def]
   >> DEP_REWRITE_TAC[mutual_indep_front_append]
   >> EXISTS_TAC(``FLAT (FLAT (MAP (\a. two_dim_rel_event_list p a t) L))``)
   >> MATCH_MP_TAC mutual_indep_append_sym
   >> RW_TAC std_ss[])
>> MP_TAC(Q.ISPECL [`p:('a event # 'a event event # ('a event -> real))`, `t:real`, `h:('a->extreal) list list`,`h':real list list`] (rel_series_parallel_RBD_exp_dist_fail_rate))
>> RW_TAC list_ss[]
>> (`(!x'.
          MEM x' (FLAT (two_dim_rel_event_list p h t)) ==>
          x' IN events p) /\
       mutual_indep p (FLAT (two_dim_rel_event_list p h t)) /\
       (LENGTH h' = LENGTH h) /\
       (!n.
          n < LENGTH h /\ n < LENGTH h' ==>
          (LENGTH (EL n h) = LENGTH (EL n h'))) /\
       two_dim_exp_dist_list p h h'` by RW_TAC std_ss[])
>- (FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def]
   >> DEP_REWRITE_TAC[mutual_indep_front_append]
   >> EXISTS_TAC(``FLAT (FLAT (MAP (\a. two_dim_rel_event_list p a t) L))``)
   >> MATCH_MP_TAC mutual_indep_append_sym
   >> RW_TAC std_ss[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`0:num`] MP_TAC)
   >> RW_TAC list_ss[])
>- (RW_TAC list_ss[]
   >> FIRST_X_ASSUM (Q.SPECL_THEN [`0:num`,`n:num`] MP_TAC)
   >> RW_TAC list_ss[])
>- ( FULL_SIMP_TAC list_ss[three_dim_exp_dist_list_def])
>> FULL_SIMP_TAC std_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`C':real list list list`] MP_TAC)
>> RW_TAC std_ss[]
>> (`(LENGTH C' = LENGTH L) /\
       mutual_indep p (FLAT (FLAT (three_dim_rel_event_list p L t))) /\
       (!x'.
          MEM x' (FLAT (FLAT (three_dim_rel_event_list p L t))) ==>
          x' IN events p) /\ (!z. MEM z (FLAT L) ==> ~NULL z) /\
       three_dim_exp_dist_list p L C' /\
       (!n' n.
          n' < LENGTH L /\ n' < LENGTH C' /\ n < LENGTH (EL n' L) /\
          n < LENGTH (EL n' C') ==>
          (LENGTH (EL n (EL n' L)) = LENGTH (EL n (EL n' C')))) /\
       (!n.
          n < LENGTH L /\ n < LENGTH C' ==>
          (LENGTH (EL n L) = LENGTH (EL n C')))` by RW_TAC std_ss[])
>- (FULL_SIMP_TAC list_ss[])
>- (DEP_REWRITE_TAC[mutual_indep_front_append]
   >> EXISTS_TAC(``(FLAT (two_dim_rel_event_list p h t))``)
   >> FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def])
>- ( FULL_SIMP_TAC list_ss[three_dim_exp_dist_list_def])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n'`,`n:num`] MP_TAC)
   >> RW_TAC list_ss[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
   >> RW_TAC std_ss[]
   >> FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
   >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[real_sub,REAL_EQ_LADD]
>> FULL_SIMP_TAC std_ss[REAL_EQ_NEG,GSYM real_sub]
>> FULL_SIMP_TAC std_ss[GSYM three_dim_rel_event_list_def,GSYM of_DEF]
>> RW_TAC list_ss[exp_func_list_def,of_DEF,o_DEF]
QED
(*---------------------------*)
Theorem nested_series_parallel_exp_dist :
!p t L C.
     (0 <= t) /\ prob_space p /\ (!z. MEM z (FLAT (FLAT L)) ==> ~NULL z) /\
     (!x'.
        MEM x' (FLAT (FLAT (FLAT (four_dim_rel_event_list p L t)))) ==>
        x' IN events p) /\ (LENGTH C = LENGTH L) /\
     (!n.
       (n < LENGTH L) /\ (n < LENGTH C) ==>
       (LENGTH (EL n L) = LENGTH (EL n C))) /\
     (!n' n.
        (n' < LENGTH L) /\ (n' < LENGTH C) /\ (n < LENGTH (EL n' L)) /\
        (n < LENGTH (EL n' C)) ==>
        (LENGTH (EL n (EL n' L)) = LENGTH (EL n (EL n' C)))) /\
     (!n'' n' n.
        (n'' < LENGTH L) /\ (n'' < LENGTH C)/\ (n' < LENGTH (EL n'' L)) /\
        (n' < LENGTH (EL n'' C)) /\ (n < LENGTH (EL n'( EL n'' L))) /\
        (n < LENGTH (EL n'( EL n'' C))) ==>
        (LENGTH (EL n (EL n' (EL n'' L))) = LENGTH (EL n (EL n' (EL n'' C))))) /\
     four_dim_exp_dist_list p L C /\
     mutual_indep p (FLAT (FLAT (FLAT (four_dim_rel_event_list p L t)))) ==>
     (prob p
        (rbd_struct p
           ((series of parallel of series of
             (\a. parallel (rbd_list (rel_event_list p a t)))) L)) =
      (list_prod of (\a. 1 − list_prod (one_minus_list a)) of
       (\a. list_prod a) of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) C)
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,rel_event_list_def,rbd_list_def,rbd_struct_def]
   >> FULL_SIMP_TAC std_ss[LENGTH_NIL]
   >> RW_TAC list_ss[exp_func_list_def,one_minus_list_def,list_prod_def]
   >> RW_TAC std_ss[PROB_UNIV])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,rel_event_list_def,rbd_list_def,rbd_struct_def])
>> RW_TAC std_ss[]
>> DEP_REWRITE_TAC[GSYM nested_series_parallel_rbd_alt_form]
>> RW_TAC std_ss[]
>> DEP_REWRITE_TAC[rel_nested_series_parallel_rbd]
>> RW_TAC std_ss[]
>- (POP_ASSUM MP_TAC
   >> MATCH_MP_TAC mem_flat_fun_eq_mem_flat_null_list
   >> RW_TAC std_ss[])
>> RW_TAC list_ss[four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def,of_DEF,one_minus_list_def,list_prod_def]
>> RW_TAC std_ss[GSYM of_DEF,GSYM two_dim_rel_event_list_def,GSYM rel_event_list_def,GSYM three_dim_rel_event_list_def ]
>> (`(1 −
 list_prod
   (one_minus_list
      (MAP
         ((\a. list_prod a) of
          (\a. 1 − list_prod (one_minus_list (list_prob p a))))
         (three_dim_rel_event_list p h t)))) = (1 −
 list_prod
   (one_minus_list
      (MAP
         ((\a. list_prod a) of
          (\a. 1 − list_prod (one_minus_list (exp_func_list a t))))
         h')))` by MATCH_MP_TAC parallel_series_parallel_prod_rel_exp_dist)
>- (RW_TAC std_ss[]
   >- (NTAC 4 (POP_ASSUM MP_TAC)
       >> POP_ASSUM (MP_TAC o Q.SPEC `0:num`)
       >> RW_TAC list_ss[])
   >- (FULL_SIMP_TAC list_ss[four_dim_rel_event_list_def]
      >> DEP_REWRITE_TAC[mutual_indep_front_append]
      >> EXISTS_TAC(``FLAT (FLAT (FLAT (MAP (\a. three_dim_rel_event_list p a t) L)))``)
      >> MATCH_MP_TAC mutual_indep_append_sym
      >> RW_TAC std_ss[])
  >- (FULL_SIMP_TAC list_ss[four_dim_rel_event_list_def])
  >- (FULL_SIMP_TAC list_ss[])
  >- (FULL_SIMP_TAC list_ss[four_dim_exp_dist_list_def])
  >- ( FIRST_X_ASSUM (Q.SPECL_THEN [`0:num`,`n':num`,`n:num`] MP_TAC)
     >> RW_TAC list_ss[])
  >> NTAC 5 (POP_ASSUM MP_TAC)
  >> POP_ASSUM (MP_TAC o Q.SPEC `0:num`)
  >> RW_TAC list_ss[])
>> POP_ORW
>> (`list_prod
  (MAP
     ((\a. 1 − list_prod (one_minus_list a)) of (\a. list_prod a) of
      (\a. 1 − list_prod (one_minus_list (list_prob p a))))
     (MAP (\a. three_dim_rel_event_list p a t) L)) = (list_prod of (\a. 1 − list_prod (one_minus_list a)) of
       (\a. list_prod a) of
       (\a. 1 − list_prod (one_minus_list (list_prob p a))))(MAP (\a. three_dim_rel_event_list p a t) L) ` by RW_TAC list_ss[of_DEF,o_DEF])
>> POP_ORW
>> DEP_REWRITE_TAC[GSYM rel_nested_series_parallel_rbd]
>> RW_TAC std_ss[]
>- (POP_ASSUM MP_TAC
   >> RW_TAC std_ss[GSYM four_dim_rel_event_list_def]
   >> POP_ASSUM MP_TAC
   >> MATCH_MP_TAC mem_flat_fun_eq_mem_flat_null_list
   >> FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[four_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[four_dim_rel_event_list_def]
   >> DEP_REWRITE_TAC[mutual_indep_front_append]
   >> EXISTS_TAC(``FLAT (FLAT (three_dim_rel_event_list p h t))``)
   >> RW_TAC std_ss[])
>> RW_TAC std_ss[GSYM four_dim_rel_event_list_def]
>> DEP_REWRITE_TAC[nested_series_parallel_rbd_alt_form]
>> RW_TAC std_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`C':real list list list list`] MP_TAC)
>> RW_TAC std_ss[]
>> (`(!z. MEM z (FLAT (FLAT L)) ==> ~NULL z) /\
       (!x'.
          MEM x' (FLAT (FLAT (FLAT (four_dim_rel_event_list p L t)))) ==>
          x' IN events p) /\ (LENGTH C' = LENGTH L) /\
       (!n.
          n < LENGTH L /\ n < LENGTH C' ==>
          (LENGTH (EL n L) = LENGTH (EL n C'))) /\
       (!n' n.
          n' < LENGTH L /\ n' < LENGTH C' /\ n < LENGTH (EL n' L) /\
          n < LENGTH (EL n' C') ==>
          (LENGTH (EL n (EL n' L)) = LENGTH (EL n (EL n' C')))) /\
       (!n'' n' n.
          n'' < LENGTH L /\ n'' < LENGTH C' /\ n' < LENGTH (EL n'' L) /\
          n' < LENGTH (EL n'' C') /\ n < LENGTH (EL n' (EL n'' L)) /\
          n < LENGTH (EL n' (EL n'' C')) ==>
          (LENGTH (EL n (EL n' (EL n'' L))) =
           LENGTH (EL n (EL n' (EL n'' C'))))) /\
       four_dim_exp_dist_list p L C' /\
       mutual_indep p
         (FLAT (FLAT (FLAT (four_dim_rel_event_list p L t))))` by RW_TAC std_ss[])
>- (FULL_SIMP_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[four_dim_rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[])
>- (NTAC 7 (POP_ASSUM MP_TAC)
   >> POP_ASSUM (MP_TAC o Q.SPEC `SUC n`)
   >> RW_TAC list_ss[])
>- (NTAC 8 (POP_ASSUM MP_TAC)
   >> POP_ASSUM (MP_TAC o Q.SPEC `SUC n'`)
   >> RW_TAC list_ss[])
>- (NTAC 9 (POP_ASSUM MP_TAC)
   >> POP_ASSUM (MP_TAC o Q.SPEC `SUC n''`)
   >> RW_TAC list_ss[])
>- (FULL_SIMP_TAC list_ss[four_dim_exp_dist_list_def])
>- (FULL_SIMP_TAC list_ss[four_dim_rel_event_list_def]
    >> DEP_REWRITE_TAC[mutual_indep_front_append]
   >> EXISTS_TAC(``FLAT (FLAT (three_dim_rel_event_list p h t))``)
   >> RW_TAC std_ss[])
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC list_ss[of_DEF,o_DEF,exp_func_list_def]
QED

(*---------------------*)
Theorem cloud_server_rv_list_not_null1 :
 !p t a b c  n m. ( !z.
        MEM z (FLAT (gen_list [c] m)) \/
        MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ==>
        ~NULL z) ==> (!z.
        MEM z (FLAT (three_dim_rel_event_list p (gen_list [a::b::c] m) t)) ==> ~NULL z)
Proof

GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,gen_list_def]
   >> Induct_on `m`
   >- (RW_TAC list_ss[gen_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
   >> RW_TAC list_ss[gen_list_suc]
   >> FULL_SIMP_TAC list_ss[]
   >> FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
>> RW_TAC list_ss[gen_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
>>  FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`] MP_TAC)
>> RW_TAC list_ss[]
>> (`(!z.
         MEM z (FLAT (gen_list [c] m)) \/
         MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ==>
         ~NULL z)` by RW_TAC std_ss[])
>- ( FULL_SIMP_TAC list_ss[cloud_server_rv_list_def,gen_list_def])
>- (FULL_SIMP_TAC list_ss[cloud_server_rv_list_def,gen_list_suc])
>> FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
>> METIS_TAC[]
QED
(*---------------------*)
Theorem cloud_server_rv_list_not_null2 :
!a b c n m.
  (!z.
        MEM z (FLAT (gen_list [c] m)) \/
        MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ==>
        ~NULL z) ==>
  (!z.
        MEM z (FLAT ((gen_list [a::b::c] m))) ==> ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,gen_list_def]
   >> Induct_on `m`
   >- (RW_TAC list_ss[gen_list_def])
   >> RW_TAC list_ss[gen_list_suc]
   >> FULL_SIMP_TAC list_ss[])
>> RW_TAC list_ss[gen_list_def]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`] MP_TAC)
>> RW_TAC list_ss[]
>> (`(!z.
         MEM z (FLAT (gen_list [c] m)) \/
         MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ==>
         ~NULL z)` by RW_TAC std_ss[])
>- ( FULL_SIMP_TAC list_ss[cloud_server_rv_list_def,gen_list_def])
>- (FULL_SIMP_TAC list_ss[cloud_server_rv_list_def,gen_list_suc])
>> METIS_TAC[]
QED
(*----------------------*)
Theorem cloud_server_rv_list_not_null3 :
!a b c n m.
  (!z.
        MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ==> ~NULL z) ==>
  (!z.
        MEM z
         (FLAT
            (FLAT
               ((cloud_server_rv_list [a::b::c] m n)))) ==> ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,gen_list_def])
>> RW_TAC list_ss[cloud_server_rv_list_def,gen_list_suc]
>- (POP_ASSUM MP_TAC
   >> MATCH_MP_TAC cloud_server_rv_list_not_null2
   >> EXISTS_TAC(``n:num``)
   >> METIS_TAC[cloud_server_rv_list_def])
>> FULL_SIMP_TAC std_ss[GSYM cloud_server_rv_list_def]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`] MP_TAC)
>> RW_TAC list_ss[]
QED
(*---------------------*)
Theorem cloud_server_rv_list_not_null :
!p t a b c n m.
  (!z.
        MEM z (FLAT (FLAT (cloud_server_rv_list [c] m n))) ==> ~NULL z) ==>
  (!z.
        MEM z
         (FLAT
            (FLAT
               (four_dim_rel_event_list p
                  (cloud_server_rv_list [a::b::c] m n) t))) ==> ~NULL z)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,gen_list_def,four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
>> RW_TAC list_ss[cloud_server_rv_list_def,gen_list_suc,four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
>- (FULL_SIMP_TAC std_ss[GSYM cloud_server_rv_list_def]
   >> FULL_SIMP_TAC std_ss[GSYM rel_event_list_def,GSYM two_dim_rel_event_list_def,GSYM three_dim_rel_event_list_def]
   >> POP_ASSUM MP_TAC
   >> MATCH_MP_TAC cloud_server_rv_list_not_null1
   >> EXISTS_TAC(``n:num``)
   >> METIS_TAC[])
>> FULL_SIMP_TAC std_ss[GSYM cloud_server_rv_list_def]
>> FULL_SIMP_TAC std_ss[GSYM rel_event_list_def,GSYM two_dim_rel_event_list_def,GSYM three_dim_rel_event_list_def,GSYM four_dim_rel_event_list_def]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`] MP_TAC)
>> RW_TAC list_ss[]
QED

(*---------------------*)
Theorem in_events_cloud_server_rv_list1 :
!p t a b c n m. rel_event p a t IN events p /\
                    rel_event p b t IN events p /\
     (!x'.
        MEM x'
          (FLAT
             (FLAT (three_dim_rel_event_list p (gen_list [c] m) t))) \/
        MEM x'
          (FLAT
             (FLAT
                (FLAT
                   (MAP (\a. three_dim_rel_event_list p a t)
                      (cloud_server_rv_list [c] m n))))) ==>
        x' IN events p) ==>
     (!x'. MEM x'
            (FLAT
              (FLAT (three_dim_rel_event_list p (gen_list [a::b::c] m) t))) ==>
           x' IN events p)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,gen_list_def]
   >> Induct_on `m`
   >- (RW_TAC list_ss[gen_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
   >> RW_TAC list_ss[gen_list_suc]
   >> FULL_SIMP_TAC list_ss[]
   >> FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
   >> FULL_SIMP_TAC list_ss[rel_event_def]
   >> FULL_SIMP_TAC list_ss[rel_event_def]
   >> METIS_TAC[])
>> RW_TAC list_ss[gen_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`] MP_TAC)
>> RW_TAC list_ss[]
>> FULL_SIMP_TAC std_ss[]
>> (`(!x'.
         MEM x'
           (FLAT
              (FLAT (three_dim_rel_event_list p (gen_list [c] m) t))) \/
         MEM x'
           (FLAT
              (FLAT
                 (FLAT
                    (MAP (\a. three_dim_rel_event_list p a t)
                       (cloud_server_rv_list [c] m n))))) ==>
         x' IN events p)` by RW_TAC std_ss[])
>- (FULL_SIMP_TAC list_ss[three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
>- (FULL_SIMP_TAC list_ss[cloud_server_rv_list_def,gen_list_suc,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
>> FULL_SIMP_TAC std_ss[GSYM four_dim_rel_event_list_def,GSYM three_dim_rel_event_list_def,GSYM two_dim_rel_event_list_def,GSYM rel_event_list_def]
>> METIS_TAC[]
QED

(*----------------------*)
Theorem in_events_cloud_server_rv_list :
!p t a b c n m. rel_event p a t IN events p /\ rel_event p b t IN events p /\
  (!x'.
         MEM x'
           (FLAT
              (FLAT
                 (FLAT
                    (four_dim_rel_event_list p
                       (cloud_server_rv_list [c] m n) t)))) ==>
         x' IN events p) ==>
   (!x'. MEM x'
         (FLAT
            (FLAT
               (FLAT
                  (four_dim_rel_event_list p
                     (cloud_server_rv_list [a::b::c] m n)
                     t)))) ==> x' IN events p)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,gen_list_def,four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def])
>> RW_TAC list_ss[cloud_server_rv_list_def,gen_list_suc,four_dim_rel_event_list_def,three_dim_rel_event_list_def,two_dim_rel_event_list_def,rel_event_list_def]
>- (FULL_SIMP_TAC std_ss[GSYM cloud_server_rv_list_def]
   >> FULL_SIMP_TAC std_ss[GSYM rel_event_list_def,GSYM two_dim_rel_event_list_def,GSYM three_dim_rel_event_list_def]
   >> POP_ASSUM MP_TAC
   >> MATCH_MP_TAC in_events_cloud_server_rv_list1
   >> EXISTS_TAC(``n:num``)
   >> METIS_TAC[])
>> FULL_SIMP_TAC std_ss[GSYM cloud_server_rv_list_def]
>> FULL_SIMP_TAC std_ss[GSYM rel_event_list_def,GSYM two_dim_rel_event_list_def,GSYM three_dim_rel_event_list_def,GSYM four_dim_rel_event_list_def]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`] MP_TAC)
>> RW_TAC list_ss[]
QED

(*---------------------*)
Theorem rel_prod_series_rbd_exp_dist :
!p t L C.
      (0 <= t) /\ prob_space p /\ exp_dist_list p L C /\
      (LENGTH C = LENGTH L) /\
      (!x. MEM x (rel_event_list p L t) ==> x IN events p) ==>
      (list_prod (list_prob p (rel_event_list p L t)) =
       list_prod (exp_func_list C t))
Proof
GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL]
   >> RW_TAC list_ss[rel_event_list_def,exp_func_list_def,list_prob_def,list_prod_def])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[rel_event_list_def,exp_func_list_def,list_prob_def,list_prod_def]
>> FULL_SIMP_TAC list_ss[exp_dist_list_def,exp_dist_def]
>> RW_TAC std_ss[GSYM rel_event_def,GSYM compl_fail_event_eq_rel_event]
>> DEP_REWRITE_TAC[PROB_COMPL]
>> RW_TAC std_ss[]
>- (DEP_REWRITE_TAC[GSYM comp_rel_event_eq_fail_event]
   >> MATCH_MP_TAC EVENTS_COMPL
   >> RW_TAC list_ss[rel_event_def])
>> FULL_SIMP_TAC std_ss[CDF_def,distribution_def,fail_event_def]
>> RW_TAC real_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`C':real list`] MP_TAC)
>> RW_TAC list_ss[rel_event_list_def]
>> DEP_REWRITE_TAC[GSYM fail_event_def,compl_fail_event_eq_rel_event,rel_event_def]
>> RW_TAC std_ss[exp_func_list_def]
QED
(*---------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list :
!a b c d e f n m.
     LENGTH (cloud_server_fail_rate_list [a::b::c] m n) =
     LENGTH (cloud_server_rv_list [d::e::f] m n)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_def])
>> RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_def]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`] MP_TAC)
>> RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_def]
QED
(*---------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list1 :
!a b c d e f m.
     (LENGTH (([a::b::c])) = LENGTH (([d::e::f]))) ==>
     (LENGTH (gen_list ([a::b::c]) m) = LENGTH (gen_list ([d::e::f]) m))
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[gen_list_def])
>> RW_TAC list_ss[gen_list_def]
QED
(*---------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list2 :
!a b c d e f n m n'.
     (LENGTH [a::b::c] = LENGTH [d::e::f]) /\
     (n' < LENGTH (cloud_server_rv_list ([a::b::c]) m n)) /\
     (n' < LENGTH(cloud_server_fail_rate_list ([d::e::f]) m n)) /\
     ~NULL c /\ ~NULL f ==>
     (LENGTH (EL n' (cloud_server_rv_list ([a::b::c]) m n)) =
      LENGTH (EL n' (cloud_server_fail_rate_list ([d::e::f]) m n)))
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_def])
>> RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_suc]
>> Induct_on `n'`
>- (RW_TAC list_ss[gen_list_def]
   >> Cases_on `m`
   >- (RW_TAC list_ss[gen_list_def])
   >> RW_TAC list_ss[gen_list_def]
   >> MATCH_MP_TAC len_cloud_server_fail_rate_eq_rv_list1
   >> RW_TAC list_ss[LENGTH])
>> RW_TAC list_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`,`n'`] MP_TAC)
>> RW_TAC list_ss[LENGTH]
>> FULL_SIMP_TAC std_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def]
QED


(*---------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list3 :
!a b c d e f m n.
      (LENGTH c = LENGTH f) /\
      ~NULL f /\ ~NULL c /\
      (n < LENGTH (gen_list [a::b::c] m)) /\
      (n < LENGTH (gen_list [d::e::f] m)) ==>
      (LENGTH (EL n (gen_list [a::b::c] m)) =
       LENGTH (EL n (gen_list [d::e::f] m)))
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[gen_list_def])
>> RW_TAC list_ss[gen_list_suc]
>> Induct_on `n`
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[]
QED
(*---------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list4 :
!a b c d e f l m n n'.  (LENGTH c =  LENGTH f) /\ (n' < LENGTH (cloud_server_rv_list [a::b::c] m l))
       /\  (n' <
            LENGTH (cloud_server_fail_rate_list [d::e::f] m l))
       /\  (n <
            LENGTH
              (EL n' (cloud_server_rv_list [a::b::c] m l)))
       /\  (n <
            LENGTH
              (EL n'
                 (cloud_server_fail_rate_list [d::e::f] m l))) /\ ~NULL f /\ ~NULL c /\ ~NULL ((cloud_server_fail_rate_list [f] m l)) /\ ~NULL((cloud_server_rv_list [c] m l) ) ==>(LENGTH
       (EL n (EL n' (cloud_server_rv_list [a::b::c] m l))) =
     LENGTH
       (EL n
          (EL n' (cloud_server_fail_rate_list [d::e::f] m l)))
)
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_def])
>> RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_suc]
>> Induct_on `n'`
>- (RW_TAC list_ss[]
   >> MATCH_MP_TAC len_cloud_server_fail_rate_eq_rv_list3
   >> RW_TAC list_ss[])
>> RW_TAC list_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`,`n:num`,`n'`] MP_TAC)
>> FULL_SIMP_TAC list_ss[cloud_server_fail_rate_list_def,cloud_server_rv_list_def]
>> Cases_on `l`
>- (RW_TAC list_ss[gen_list_def]
   >> FULL_SIMP_TAC list_ss[gen_list_def])
>> RW_TAC list_ss[gen_list_suc]
QED
(*-------------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list5 :
!a b c d e f n.
     (LENGTH c = LENGTH f) /\
     ~NULL f /\ ~NULL c /\
     (n < LENGTH [a::b::c]) /\ (n < LENGTH [d::e::f]) ==>
     (LENGTH (EL n [a::b::c]) = LENGTH (EL n [d::e::f]))
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[LENGTH]
QED

(*-------------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list6 :
!a b c d e f m n n'.
     (LENGTH c = LENGTH f) /\
     ~NULL f /\
     ~NULL c /\
     (n' < LENGTH (gen_list [a::b::c] m)) /\
     (n' < LENGTH (gen_list [d::e::f] m)) /\
     (n < LENGTH (EL n' (gen_list [a::b::c] m))) /\
     (n < LENGTH (EL n' (gen_list [d::e::f] m))) ==>
     (LENGTH (EL n (EL n' (gen_list [a::b::c] m))) =
      LENGTH (EL n (EL n' (gen_list [d::e::f] m))))
Proof
GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[gen_list_def])
>> RW_TAC list_ss[gen_list_suc]
>> Induct_on `n'`
>- (RW_TAC list_ss[]
   >> MATCH_MP_TAC len_cloud_server_fail_rate_eq_rv_list5
   >> RW_TAC list_ss[LENGTH])
>> RW_TAC list_ss[]
QED
(*---------------------*)
Theorem len_cloud_server_fail_rate_eq_rv_list7 :
!a b c d e f l m n n' n''. ~NULL f /\ ~NULL c /\  (LENGTH c =  LENGTH f)   /\ (n'' < LENGTH (cloud_server_rv_list [a::b::c] m l))
  /\  (n'' <
       LENGTH (cloud_server_fail_rate_list [d::e::f] m l))
  /\  (n' <
       LENGTH (EL n'' (cloud_server_rv_list [a::b::c] m l)))
  /\  (n' <
       LENGTH
         (EL n'' (cloud_server_fail_rate_list [d::e::f] m l)))
  /\  (n <
       LENGTH
         (EL n' (EL n'' (cloud_server_rv_list [a::b::c] m l))))
  /\  (n <
       LENGTH
         (EL n'
            (EL n''
               (cloud_server_fail_rate_list [d::e::f] m l)))) ==> (LENGTH
  (EL n
     (EL n' (EL n'' (cloud_server_rv_list [a::b::c] m l)))) =
LENGTH
  (EL n
     (EL n'
        (EL n'' (cloud_server_fail_rate_list [d::e::f] m l)))))
Proof
NTAC 6 (GEN_TAC)
>> Induct
>- (RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_def])
>> RW_TAC list_ss[cloud_server_rv_list_def,cloud_server_fail_rate_list_def,gen_list_suc]
>> Induct_on `n''`
>- (RW_TAC list_ss[]
   >> MATCH_MP_TAC len_cloud_server_fail_rate_eq_rv_list6
   >> RW_TAC list_ss[])
>> RW_TAC list_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`m:num`,`n:num`,`n'`,`n''`] MP_TAC)
>> FULL_SIMP_TAC list_ss[cloud_server_fail_rate_list_def,cloud_server_rv_list_def]
QED
(*----------------------*)
Theorem VDC_case_study_thm :
!X_VM X_VMM X_HW X_C C_VM C_VMM C_HW C m n p t.
  (0 <=  t)/\ prob_space p /\ ~NULL (cloud_server_rv_list ([X_VM]) m n) /\
  ~NULL (cloud_server_fail_rate_list ([C_VM]) m n) /\
  (!z.
    MEM z (FLAT (FLAT((cloud_server_rv_list ([X_VM]) m n)))) ==>
    ~NULL z) /\ (LENGTH C = LENGTH X_C) /\ ~NULL C_VM /\
  ~NULL X_VM /\ (LENGTH X_VM = LENGTH C_VM) /\
  exp_dist_list p X_C C /\ ~NULL (rel_event_list p X_C t) /\
  (!x'.
    MEM x'
     (FLAT
       (FLAT
         (FLAT
           (four_dim_rel_event_list p
             (cloud_server_rv_list  ([X_VM]) m n) t)))) ==>
    x' IN events p) /\ (rel_event p X_VMM t IN events p) /\
 (rel_event p X_HW t IN events p) /\
 (!z'. MEM z' (rel_event_list p X_C t) ==> z' IN events p) /\
 (LENGTH X_VM = LENGTH C_VM) /\
 four_dim_exp_dist_list p
   (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n)
   (cloud_server_fail_rate_list ([C_VMM::C_HW:: C_VM]) m n) /\
 mutual_indep p
    (rel_event_list p X_C t ++
    FLAT
     (FLAT
       (FLAT
          (four_dim_rel_event_list p
             (cloud_server_rv_list  ([X_VMM::X_HW::X_VM]) m n) t)))) ==>
(prob p
   (rbd_struct p (series (rbd_list (rel_event_list p X_C t))) INTER
    rbd_struct p
       ((series of parallel of series of
         (\a. parallel (rbd_list (rel_event_list p a t))))
          (cloud_server_rv_list  ([X_VMM::X_HW::X_VM]) m n))) =
 (list_prod (exp_func_list C t)) *
  (list_prod of (\a. 1 − list_prod (one_minus_list a)) of
   (\a. list_prod a) of
   (\a. 1 − list_prod (one_minus_list (exp_func_list a t))))
    (cloud_server_fail_rate_list ([C_VMM::C_HW:: C_VM]) m n))
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[GSYM nested_series_parallel_rbd_alt_form]
>> RW_TAC std_ss[]
>> RW_TAC std_ss[of_DEF]
>> DEP_REWRITE_TAC[(REWRITE_RULE[of_DEF]series_rbd_indep_series_parallel_of_series_parallel)]
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[]
   >> POP_ASSUM MP_TAC
   >> MATCH_MP_TAC cloud_server_rv_list_not_null
   >> METIS_TAC[])
>- (FULL_SIMP_TAC list_ss[]
   >> POP_ASSUM MP_TAC
   >> MATCH_MP_TAC in_events_cloud_server_rv_list
   >> METIS_TAC[])
>> DEP_REWRITE_TAC[series_struct_thm]
>> RW_TAC std_ss[]
>- (MATCH_MP_TAC mutual_indep_front_append
   >> EXISTS_TAC(``FLAT
            (FLAT
               (FLAT
                  (four_dim_rel_event_list p
                     (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n)
                     t)))``)
   >> MATCH_MP_TAC mutual_indep_append_sym
   >> RW_TAC std_ss[])
>> DEP_REWRITE_TAC[rel_prod_series_rbd_exp_dist]
>> RW_TAC std_ss[]
>> RW_TAC std_ss[GSYM of_DEF]
>> (`(rbd_struct p
     (series
        (MAP (parallel of series of (\a. parallel (rbd_list a)))
           (four_dim_rel_event_list p
              (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n) t)))) = (rbd_struct p
        ((series of parallel of series of (\a. parallel (rbd_list a)))
           (four_dim_rel_event_list p (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n) t)))` by RW_TAC list_ss[of_DEF,o_DEF])
>> POP_ORW
>> DEP_REWRITE_TAC[nested_series_parallel_rbd_alt_form]
>> RW_TAC std_ss[]
>> (`prob p
  (rbd_struct p
     ((series of parallel of series of
       (\a. parallel (rbd_list (rel_event_list p a t))))
        (cloud_server_rv_list [X_VMM::X_HW::X_VM] m n))) = (list_prod of (\a. 1 − list_prod (one_minus_list a)) of
       (\a. list_prod a) of
       (\a. 1 − list_prod (one_minus_list (exp_func_list a t)))) (cloud_server_fail_rate_list [C_VMM::C_HW::C_VM] m n)` by (MATCH_MP_TAC nested_series_parallel_exp_dist))
>- (RW_TAC std_ss[]
   >- (POP_ASSUM MP_TAC
      >> MATCH_MP_TAC cloud_server_rv_list_not_null3
      >> RW_TAC std_ss[])
   >- (POP_ASSUM MP_TAC
      >> MATCH_MP_TAC in_events_cloud_server_rv_list
      >> RW_TAC std_ss[])
   >- (RW_TAC std_ss[len_cloud_server_fail_rate_eq_rv_list])
   >- (MATCH_MP_TAC len_cloud_server_fail_rate_eq_rv_list2
      >> RW_TAC list_ss[])
   >- (MATCH_MP_TAC len_cloud_server_fail_rate_eq_rv_list4
      >> RW_TAC list_ss[])
   >- (MATCH_MP_TAC len_cloud_server_fail_rate_eq_rv_list7
      >> RW_TAC list_ss[])
   >> MATCH_MP_TAC mutual_indep_front_append
   >> EXISTS_TAC(``rel_event_list p X_C t``)
   >> RW_TAC list_ss[])
>> POP_ORW
>> RW_TAC list_ss[of_DEF,o_DEF]
QED

(*------------parallel_series_exp_fail_rate-------------------------*)
Theorem parallel_series_exp_fail_rate :
∀p t L C.
     (∀z. MEM z L ==> ~NULL z) ∧ 0 <= t ∧ prob_space p ∧
     (∀x'.
        MEM x' (FLAT (two_dim_rel_event_list p L t)) ⇒ x' ∈ events p) ∧
     (LENGTH C = LENGTH L) ∧
     (∀n.
        n < LENGTH L ∧ n < LENGTH C ==>
        (LENGTH (EL n L) = LENGTH (EL n C))) ∧
     two_dim_exp_dist_list p L C ⇒
     (1 - (list_prod o (one_minus_list) of
        (\a. list_prod (list_prob p a))) (two_dim_rel_event_list p L t) =
     1 - (list_prod o (one_minus_list) of
        (\a. list_prod (exp_func_list a t))) C)
Proof
GEN_TAC >> GEN_TAC
>> Induct
   >- (RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,list_prod_def,list_prob_def,LENGTH_NIL])
>> GEN_TAC >> Induct
   >- (RW_TAC list_ss[])
>> GEN_TAC >> RW_TAC std_ss[]
>> RW_TAC list_ss[of_DEF,o_DEF,two_dim_rel_event_list_def,list_prod_def,list_prob_def,one_minus_list_def,exp_func_list_def]
>> (`list_prod (list_prob p (rel_event_list p h t)) = list_prod (exp_func_list h' t)` by MATCH_MP_TAC rel_prod_series_rbd_exp_dist)
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

(*-----------------rel_parallel_series_exp_fail_rate--------------------------------*)
Theorem rel_parallel_series_exp_fail_rate :
∀p t L C.
     (∀z. MEM z L ⇒ ¬NULL z) ∧ 0 ≤ t ∧ prob_space p ∧
     (∀x'.
        MEM x' (FLAT (two_dim_rel_event_list p L t)) ⇒ x' ∈ events p) ∧
     mutual_indep p (FLAT (two_dim_rel_event_list p L t)) ∧
     (LENGTH C = LENGTH L) ∧
     (∀n.
        n < LENGTH L ∧ n < LENGTH C ⇒
        (LENGTH (EL n L) = LENGTH (EL n C))) ∧
     two_dim_exp_dist_list p L C ⇒
     (prob p
        (rbd_struct p
           ((parallel of (λa. series (rbd_list a)))
              (two_dim_rel_event_list p L t))) =
      1 -
      (list_prod o (one_minus_list) of
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


val _ = export_theory();
