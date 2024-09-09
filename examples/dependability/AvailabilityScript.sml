(* ========================================================================= *)
(* File Name: Availability.sml                                               *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Availability Analysis using Theorem Proving           *)
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

(*app load ["arithmeticTheory", "realTheory", "prim_recTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory",
          "probabilityTheory", "numTheory", "transcTheory", "rich_listTheory",
          "pairTheory", "combinTheory","limTheory","sortingTheory", "realLib",
          "optionTheory","satTheory", "util_probTheory", "extrealTheory", "measureTheory",
          "lebesgueTheory","real_sigmaTheory","dep_rewrite","RBDTheory","FT_deepTheory","VDCTheory",
          "seqTheory", "extra_pred_setTools"];*)

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory
     prim_recTheory real_probabilityTheory
      pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory
      util_probTheory extrealTheory real_measureTheory real_lebesgueTheory real_sigmaTheory satTheory numTheory dep_rewrite
      RBDTheory FT_deepTheory VDCTheory seqTheory extra_pred_setTools;

fun K_TAC _ = ALL_TAC;

open HolKernel boolLib bossLib Parse;
val _ = new_theory "Availability";

(*--------------------*)
val op by = BasicProvers.byA;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)

(*----------------------------*)
Definition avail_event_def :
avail_event (L:(('a->extreal) # ('a->extreal)) list) n t =
{x |
(EXTREAL_SUM_IMAGE (\a. (FST (EL a L)) x + (SND (EL a L)) x) (count n)  <= t) /\
(t <
 EXTREAL_SUM_IMAGE (\a. (FST (EL a L)) x + (SND (EL a L)) x) (count n) +
 (FST (EL (n) L)) x)}
End
(*----------------------------*)
Definition union_avail_events_def :
union_avail_events L n t =
(BIGUNION (IMAGE (\a. avail_event L a (Normal t)) (count n)))
End
(*----------------------------*)
Definition union_avail_events1_def :
union_avail_events1 L t =
(BIGUNION (IMAGE (\a. avail_event L a (Normal t)) (count (LENGTH L))))
End
(*----------------------------*)
Definition union_avail_event_list_def :
union_avail_event_list L n t =
 MAP (\a. union_avail_events a n t) L
End
(*----------------------------*)
Definition union_avail_event_list1_def :
union_avail_event_list1 L t =
 MAP (\a. union_avail_events1 a t) L
End
(*----------------------------*)
Definition list_union_avail_event_list_def :
list_union_avail_event_list L t =
 MAP (\a. union_avail_event_list1 a t) L
End
(*----------------------------*)
Definition avail_event_list_def :
avail_event_list L n t =
 MAP (\a. avail_event a n t) L
End
(*---------------------------------*)
Definition expec_avail_def :
expec_avail p (L:(('a->extreal) # ('a->extreal)) list) n t =
 sum (0,n) (\a. prob p (avail_event L a t))
End

(*---------------------------------*)
Definition expec_avail1_def :
expec_avail1 p (L:(('a->extreal) # ('a->extreal)) list) n t =
 sum (0,n) (prob p o (\a. avail_event L a t))
End

(*---------------------------------*)
Definition cdf_def :
cdf p X t = distribution p X {y| y <= t}
End

(*---------------------------------*)
Definition reliability_def :
reliability p X t = 1 - cdf p X t
End


(*---------------------------------*)
Definition rel_event_def :
rel_event1 p X t = PREIMAGE X {y | t < y} INTER p_space p
End
(*-------------------------*)
Definition expec_def :
expec n f = sum (0,n) f
End

(*-------------------------*)
Definition inst_avail_exp_def :
inst_avail_exp p L n m =
 !(t:real). (expec n (\a. prob p (avail_event L a (Normal t))) =
            (SND (m) / (SND m + FST m)) + (FST m /(SND m + FST m)) *
            exp (-((SND m + FST m))*t))
End
(*-------------------------*)
Definition inst_avail_exp1_def :
inst_avail_exp1 p L n m =
 !t. (prob p ( union_avail_events L n &t) =
     (SND m / (SND m + FST m)) +
     (FST m / (SND m + FST m)) * exp (-((SND m + FST m)) * &t))
End
(*-------------------------*)
(*-------------------------*)
Definition inst_avail_exp2_def :
inst_avail_exp2 p L m =
 !t. (prob p ( union_avail_events1 L &t)  =
     (SND (m) / (SND m + FST m)) +
     (FST m /(SND m + FST m)) * exp (-((SND m + FST m)) * &t))
End
(*-------------------------*)
Definition inst_avail_exp3_def :
inst_avail_exp3 p L m =
 !t. (prob p ( union_avail_events1 L &t INTER p_space p)  =
     (SND (m) / (SND m + FST m)) +
     (FST m /(SND m + FST m)) * exp (-((SND m + FST m))* &t))
End
(*-------------------------*)
Definition inst_avail_exp_list_def :
(inst_avail_exp_list p [] n M = T) /\
 (inst_avail_exp_list p (h::t) n M = (inst_avail_exp p h n (HD M) /\
  inst_avail_exp_list p t n (TL M) ))
End
(*-------------------------*)
Definition inst_avail_exp_list1_def :
(inst_avail_exp_list1 p [] M = T) /\
 (inst_avail_exp_list1 p (h::t) M = (inst_avail_exp2 p h (HD M) /\
  inst_avail_exp_list1 p t (TL M) ))
End
(*-------------------------*)
Definition inst_avail_exp_list2_def :
(inst_avail_exp_list2 p [] M = T) /\
 (inst_avail_exp_list2 p (h::t) M = (inst_avail_exp3 p h (HD M) /\
  inst_avail_exp_list2 p t (TL M) ))
End
(*-------------------------*)
Definition two_dim_inst_avail_exp_def :
(two_dim_inst_avail_exp p [] M = T) /\
 (two_dim_inst_avail_exp p (h::t) M = (inst_avail_exp_list1 p h (HD M) /\
  two_dim_inst_avail_exp p t (TL M) ))
End
(*-------------------------*)
Definition steady_state_avail_def :
steady_state_avail m = (SND (m:real#real) / (SND m + FST m))
End
(*-------------------------*)
Definition steady_state_avail_list_def :
(steady_state_avail_list [] = []) /\
 (steady_state_avail_list (h::t) =  steady_state_avail h :: steady_state_avail_list t)
End
(*-------------------------*)
Definition two_dim_steady_state_avail_list_def :
(two_dim_steady_state_avail_list [] = []) /\
 (two_dim_steady_state_avail_list (h::t) =
  steady_state_avail_list h :: two_dim_steady_state_avail_list t)
End
(*-------------------------*)
Definition steady_state_avail_prod_def :
(steady_state_avail_prod [] = (1:real)) /\
 (steady_state_avail_prod (h::t) =
  steady_state_avail h * steady_state_avail_prod t)
End
(*-------------------------*)
Definition two_dim_steady_state_avail_prod_def :
(two_dim_steady_state_avail_prod [] = (1:real)) /\
 (two_dim_steady_state_avail_prod (h::t) =
  steady_state_avail_prod h * two_dim_steady_state_avail_prod t)
End
(*-----------------------------------*)
Definition compl_steady_state_avail_def :
(compl_steady_state_avail [] = 1) /\
 (compl_steady_state_avail (h::t) =
 (1 - steady_state_avail h) * compl_steady_state_avail (t))
End
(*---------------------------------*)
Theorem compl_rel_event_eq_fail_event1 :
!p t s. prob_space p ==>
            ((p_space p DIFF PREIMAGE s {y | t < y} INTER p_space p) =
             (PREIMAGE s {y | y <= t} INTER p_space p))
Proof
SRW_TAC[][PREIMAGE_def,DIFF_DEF,EXTENSION,GSPECIFICATION,REAL_NOT_LT]
>> SET_TAC[extreal_not_le]
QED
(*---------------------------------*)
Theorem compl_fail_event_eq_rel_event1 :
!X t p. p_space p DIFF PREIMAGE X {y | y ≤ t} INTER p_space p =
            rel_event1 p X t
Proof
  RW_TAC std_ss[rel_event_def]
  >> SRW_TAC[][IN_DIFF,PREIMAGE_def,EXTENSION,GSPECIFICATION]
  >> RW_TAC std_ss[GSYM extreal_lt_def]
  >> METIS_TAC[]
QED
(*--------------------------------*)

(*---------------------------------*)
Theorem avail_ge_rel :
!p t L.
        (0 ≤ t) /\
        (~NULL L) /\
        (!n. avail_event L n t IN events p) /\
        (prob_space p) ==>
         ((reliability p (FST (HD L)) t) <=
          expec_avail p L (LENGTH L) t)
Proof
NTAC 2 (GEN_TAC)
>> Cases
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[expec_avail_def,avail_event_def]
>> RW_TAC std_ss[ADD1]
>> ONCE_REWRITE_TAC[ADD_SYM]
>> DEP_REWRITE_TAC[GSYM SUM_TWO]
>> ONCE_REWRITE_TAC[ONE]
>> RW_TAC std_ss[sum]
>> RW_TAC real_ss[count_def]
>> SRW_TAC[][]
>> RW_TAC std_ss[EXTREAL_SUM_IMAGE_THM]
>> RW_TAC real_ss[add_lzero]
>> RW_TAC std_ss[reliability_def]
>> RW_TAC std_ss[cdf_def,distribution_def]
>> DEP_REWRITE_TAC[GSYM PROB_COMPL]
>> RW_TAC std_ss[]
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
   >> RW_TAC real_ss[count_def]
   >> POP_ASSUM MP_TAC
   >> SRW_TAC[][]
   >> FULL_SIMP_TAC std_ss[EXTREAL_SUM_IMAGE_THM,add_lzero]
   >> POP_ASSUM MP_TAC
   >> ASM_REWRITE_TAC[]
   >> RW_TAC std_ss[GSYM compl_rel_event_eq_fail_event1]
   >> DEP_REWRITE_TAC [EVENTS_INTER,EVENTS_DIFF]
   >> RW_TAC std_ss[EVENTS_SPACE]
   >> POP_ASSUM MP_TAC
   >> (`!X. PREIMAGE X {y | t < y} = {y | t < X y}` by SET_TAC[IN_PREIMAGE])
   >> ASM_REWRITE_TAC[])
>> DEP_REWRITE_TAC[ compl_fail_event_eq_rel_event1]
>> RW_TAC std_ss[rel_event_def]
>> (`!X. PREIMAGE X {x | t < x} = {x | t < X x}` by SET_TAC[IN_PREIMAGE])
>> RW_TAC std_ss[]
>> ONCE_REWRITE_TAC[INTER_COMM]
>> DEP_REWRITE_TAC[INTER_PSPACE]
>> RW_TAC std_ss[]
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
   >> RW_TAC real_ss[count_def]
   >> POP_ASSUM MP_TAC
   >> SRW_TAC[][]
   >> FULL_SIMP_TAC std_ss[EXTREAL_SUM_IMAGE_THM,add_lzero]
   >> POP_ASSUM MP_TAC
   >> ASM_REWRITE_TAC[]
   >> RW_TAC std_ss[GSYM compl_rel_event_eq_fail_event1]
   >> DEP_REWRITE_TAC [EVENTS_INTER,EVENTS_DIFF]
   >> RW_TAC std_ss[EVENTS_SPACE])
>> RW_TAC std_ss[REAL_LE_ADDR]
>> DEP_REWRITE_TAC[SUM_POS]
>> RW_TAC std_ss[]
>> DEP_REWRITE_TAC[PROB_POSITIVE]
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[count_def]
QED
(*-------------------------------*)
Theorem avail_ge_rel1 :
!p t L.
       (0 ≤ Normal t) /\
       (~NULL L) /\
       (!a b. (a <> b) ==> DISJOINT (avail_event L a (Normal t))
                                    (avail_event L b (Normal t))) /\
       (!n. avail_event L n (Normal t) IN events p)  /\
       (prob_space p) ==>
         ((reliability p (FST (HD L)) (Normal t)) <=
          prob p (union_avail_events L (LENGTH L) (t)))
Proof
RW_TAC std_ss[]
>> (`prob p (union_avail_events L (LENGTH L) t) =
      sum (0,LENGTH L) (prob p o (\a. avail_event L a (Normal t)))`  by (MATCH_MP_TAC EQ_SYM))
>- (MATCH_MP_TAC PROB_FINITELY_ADDITIVE
   >> RW_TAC std_ss[]
   >> RW_TAC std_ss[union_avail_events_def]
   >> FULL_SIMP_TAC std_ss[IN_FUNSET])
>> POP_ORW
>> FULL_SIMP_TAC std_ss[IN_FUNSET]
>> RW_TAC std_ss[o_DEF,GSYM expec_avail_def,IN_FUNSET]
>> MATCH_MP_TAC avail_ge_rel
>> RW_TAC real_ss[]
>> FULL_SIMP_TAC list_ss[IN_COUNT]
QED


(*-------------------------neg_exp_tend0_new-------------------------------------------*)
Theorem neg_exp_tend0_new :
!t (c:real). (0 < c) ==> (\t. exp (&t*(-c)))--> 0
Proof
GEN_TAC
>> REWRITE_TAC[EXP_N]
>> RW_TAC real_ss[]
>> MATCH_MP_TAC SEQ_POWER
>> RW_TAC real_ss[]
>> RW_TAC real_ss[abs]
>- (RW_TAC real_ss[EXP_NEG]
   >> KNOW_TAC(``(inv (exp c) < (1:real)) =
                (inv (exp c) < (inv (1:real)))``)
       >- (RW_TAC real_ss[REAL_INV_1OVER])
    >> DISCH_TAC >> PURE_ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC
    >> KNOW_TAC(``abs (inv (exp (c:real))) = abs (inv (exp c) - 0)``)
    >- (RW_TAC real_ss[])
    >> DISCH_TAC >> PURE_ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC
    >> KNOW_TAC(``(inv (exp c) < (inv (1:real))) = (1 < exp (c:real))``)
    >- (MATCH_MP_TAC REAL_INV_LT_ANTIMONO
       >> RW_TAC real_ss[EXP_POS_LT])
    >> DISCH_TAC >> PURE_ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC
    >> RW_TAC real_ss[EXP_LT_1])
>> RW_TAC std_ss[EXP_NEG]
>> KNOW_TAC(``(-inv (exp c) < (1:real)) = ((-1:real) < -(-inv (exp c))) ``)
   >- (RW_TAC real_ss[REAL_LT_NEG])
>> RW_TAC real_ss[]
>> MATCH_MP_TAC REAL_LT_TRANS
>> EXISTS_TAC(``0:real``)
>> RW_TAC real_ss[]
>> RW_TAC real_ss[EXP_POS_LT]
QED
(*-----------------steady_avail_temp------------------------------------------*)
Theorem steady_avail_temp :
!a b:real. 0 < a /\ 0 < b ==> 0 < a + b
Proof
REAL_ARITH_TAC
QED

(*---------------------------------------------*)
Theorem steady_state_avail :
!p L n m t.
      ((0 < FST m) /\ (0 < SND m)) /\ inst_avail_exp p L n m ==>
      (lim (\t.  (expec_avail p L n (Normal &t))) =
       SND m / (SND m + FST m))
Proof
RW_TAC std_ss[]
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC (``((\t. expec_avail p L n (Normal &t)))``)
>> STRIP_TAC
>- (RW_TAC std_ss[GSYM SEQ_LIM,convergent]
   >> RW_TAC std_ss [expec_avail_def]
   >> FULL_SIMP_TAC std_ss[inst_avail_exp_def,expec_def]
   >> (`(\t.
     SND m / (SND m + FST m) +
     FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) = (\t.
     (\t. SND m / (SND m + FST m)) t +
     (\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t))t)` by RW_TAC std_ss[])
   >> POP_ORW
   >> EXISTS_TAC (``SND (m:real#real) / (SND m + FST m) + 0``)
   >> DEP_REWRITE_TAC[SEQ_ADD]
   >> RW_TAC std_ss[]
   >- (RW_TAC std_ss[SEQ_CONST])
   >- ((`((\t. (FST (m:real#real) / (SND m + FST m)) * exp (-(SND m + FST m) * &t)) --> 0) =
         ((\t.
             (\t. FST m / (SND m + FST m)) t *
             (\t. exp (-(SND m + FST m) * &t)) t) -->
         ((FST m / (SND m + FST m)) *0))` by (RW_TAC real_ss[]))
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_MUL
      >> RW_TAC real_ss[SEQ_CONST]
      >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      >> MATCH_MP_TAC neg_exp_tend0_new
      >> RW_TAC std_ss[]
      >> RW_TAC std_ss[steady_avail_temp])
  >> (`(\t.
     SND m / (SND m + FST m) +
     FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) = (\t.
     (\t. SND m / (SND m + FST m)) t +
     (\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t))t)` by RW_TAC std_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_ADD
  >> RW_TAC std_ss[SEQ_CONST]
  >> (`((\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) --> 0) =
      ((\t. (\t. FST m / (SND m + FST m))t * (\t. exp (-(SND m + FST m) * &t))t) -->
       ((FST m / (SND m + FST m)) *0))`
       by RW_TAC real_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_MUL
  >> RW_TAC real_ss[SEQ_CONST]
  >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
  >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
  >> MATCH_MP_TAC neg_exp_tend0_new
  >> RW_TAC std_ss[]
  >> RW_TAC std_ss[steady_avail_temp])
>> RW_TAC std_ss [expec_avail_def]
>> FULL_SIMP_TAC std_ss[inst_avail_exp_def,expec_def]
>> (`((\t.
     SND m / (SND m + FST m) +
     FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) --> (SND m / (SND m + FST m))) =
    ((\t.
     (\t. SND m / (SND m + FST m)) t +
     (\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t))t) -->
     ((SND m / (SND m + FST m)) + 0))` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_ADD
>> RW_TAC std_ss[]
>- (RW_TAC std_ss[SEQ_CONST])
>> (`((\t. FST m / (SND m + FST m) * exp (-(SND m + FST m) * &t)) --> 0) =
    ((\t. (\t. FST m / (SND m + FST m))t * (\t. exp (-(SND m + FST m) * &t))t)
     --> ((FST m / (SND m + FST m)) *0))`
      by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC real_ss[SEQ_CONST]
>> ONCE_REWRITE_TAC[REAL_MUL_SYM]
>> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
>> MATCH_MP_TAC neg_exp_tend0_new
>> RW_TAC std_ss[]
>> RW_TAC std_ss[steady_avail_temp]
QED
(*---------------------------------------------*)
Theorem steady_state_avail1 :
!p L n m. prob_space p /\
              (!t. (!a b. (a <> b) ==>
                   DISJOINT (avail_event L a (Normal (t)))
                            (avail_event L b (Normal (t)))) /\
                   (!n. avail_event L n (Normal t) IN events p)) /\
              ((0 < FST m)/\ (0 < SND m)) /\
              inst_avail_exp p L n m ==>
                (lim (\t.
                       (prob p (union_avail_events L n (&t)))) =
                 SND m / (SND m + FST m))
Proof
RW_TAC std_ss[]
>> (`!t. prob p (union_avail_events L n t) = sum (0,n) (prob p o (\a. avail_event L a (Normal t)))`  by RW_TAC std_ss[])
>- (MATCH_MP_TAC EQ_SYM
   >> MATCH_MP_TAC PROB_FINITELY_ADDITIVE
   >> RW_TAC std_ss[]
   >- (FULL_SIMP_TAC std_ss[IN_FUNSET,IN_COUNT])
   >> RW_TAC std_ss[union_avail_events_def]
   >> FULL_SIMP_TAC std_ss[IN_FUNSET])
>> POP_ORW
>> RW_TAC std_ss[o_DEF,GSYM expec_avail_def,IN_FUNSET]
>> MATCH_MP_TAC steady_state_avail
>> RW_TAC real_ss[]
QED

(*=======================SUPPORTING_THEOREMS==============*)

(* ------------------------------------------------------------------------- *)
(*                 EXT_LE_LT               *)
(* ------------------------------------------------------------------------- *)
Theorem EXT_LE_LT :
!x y: extreal. ((x <=  y) \/ y < x) = ((x = y) \/ x < y \/ y < x)
Proof
RW_TAC std_ss []
>> RW_TAC std_ss [le_lt]
>> KNOW_TAC (``(x < y \/ (x = y)) = ( (x = y) \/ x < y)``)
>- (RW_TAC std_ss [DISJ_COMM]
   >> DISCH_TAC >> REWRITE_TAC [])
>> RW_TAC std_ss [DISJ_ASSOC]
QED
(* ------------------------------------------------------------------------- *)
(*                 PERM_refl               *)
(* ------------------------------------------------------------------------- *)
Theorem PERM_refl:  !L. PERM L L
Proof PROVE_TAC[PERM_DEF]
QED

(* ------------------------------------------------------------------------- *)
(*                 LET_ANTISYM               *)
(* ------------------------------------------------------------------------- *)
Theorem LET_ANTISYM :
!x y. ~(x < y /\ y <=  x)
Proof
RW_TAC std_ss[extreal_not_le]
QED

(*---------not_null_leng-------------*)
Theorem not_null_leng :
! L1 . ~NULL L1  ==> 1 <= LENGTH L1
Proof
FULL_SIMP_TAC list_ss[GSYM LENGTH_NOT_NULL]
QED

(*---------------------------*)

(*----------------------------*)
Theorem series_expec_tends_prod_avail :
!p L M.
       prob_space p /\
       (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
       (LENGTH L = LENGTH M) /\
       (inst_avail_exp_list1 p L M) ==>
  ((\t.list_prod
     (list_prob p (union_avail_event_list1 L (&t))))-->
  steady_state_avail_prod M)
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL_SYM]
   >> RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,steady_state_avail_prod_def]
   >> RW_TAC std_ss[SEQ_CONST])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>>  RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,steady_state_avail_prod_def]
>> (`!t. (
   prob p (union_avail_events1 h (&t)) *
   list_prod
     (list_prob p
        (MAP (\a. union_avail_events1 a (&t)) L))) = (\t.
   prob p (union_avail_events1 h (&t))) t *
   (\t. list_prod
     (list_prob p
        (MAP (\a. union_avail_events1 a (&t)) L))) t` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[inst_avail_exp_list1_def,inst_avail_exp2_def]
   >> REWRITE_TAC[steady_state_avail_def]
   >> (`((\t.
     SND (h':real#real) / (SND h' + FST h') +
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) -->
         (SND h' / (SND h' + FST h'))) =
     ((\t.
     (\t. SND h' / (SND  h'+ FST h')) t +
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) t) -->
     (SND h' / (SND h' + FST h') + 0))` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_ADD
   >> RW_TAC std_ss[]
   >- (RW_TAC std_ss[SEQ_CONST])
   >- ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) =
      ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t)) t)
       --> ((FST h' / (SND h' + FST h')) *0))` by RW_TAC real_ss[])
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_MUL
      >> RW_TAC real_ss[SEQ_CONST]
      >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      >> MATCH_MP_TAC neg_exp_tend0_new
      >> RW_TAC std_ss[]
      >> RW_TAC std_ss[steady_avail_temp]))
>> FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
>> RW_TAC std_ss[inst_avail_exp_list1_def, GSYM union_avail_event_list1_def]
>> FULL_SIMP_TAC list_ss[ inst_avail_exp_list1_def]
QED
(*------------------------------*)
Theorem series_rbd_avail :
!p L M.
       prob_space p /\
       (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
       (LENGTH L = LENGTH M) /\
       (!t'. ~NULL (union_avail_event_list1 L &t') /\
       (!z. MEM z (union_avail_event_list1 L ( (&t'))) ==> z IN events p) /\
       mutual_indep p (union_avail_event_list1 L ( (&t')))) /\
       inst_avail_exp_list1 p L M ==>
        (lim (\t.  prob p
             (rbd_struct p
                (series (rbd_list (union_avail_event_list1 L (&t)))))) =
         steady_state_avail_prod M)
Proof
RW_TAC std_ss[]
>> (`!t.  prob p (rbd_struct p
       (series (rbd_list (union_avail_event_list1 L (&t))))) =
        list_prod (list_prob p (union_avail_event_list1 L (&t)))` by RW_TAC std_ss[])
>- (MATCH_MP_TAC series_struct_thm
   >> FULL_SIMP_TAC std_ss[]
   >> RW_TAC std_ss[]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC `t:num`)
   >> RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\t. list_prod
         (list_prob p (union_avail_event_list1 L  (&t))))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC(``steady_state_avail_prod M``)
   >> MATCH_MP_TAC series_expec_tends_prod_avail
   >> RW_TAC std_ss[])
>> MATCH_MP_TAC series_expec_tends_prod_avail
>> RW_TAC std_ss[]
QED

(*-------------------------*)
Theorem lim_inst_parall_tend_steady :
!p L M.
  prob_space p /\
  (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
  (LENGTH L = LENGTH M) /\
  (inst_avail_exp_list1 p L M) ==>
        ((\t. list_prod
               (one_minus_list
                (list_prob p (union_avail_event_list1 L (&t)))))-->
        compl_steady_state_avail M)
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL_SYM]
   >> RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,compl_steady_state_avail_def]
   >> RW_TAC std_ss[one_minus_list_def,list_prod_def,SEQ_CONST])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>>  RW_TAC list_ss[union_avail_event_list1_def,list_prod_def,list_prob_def,compl_steady_state_avail_def]
   >> RW_TAC std_ss[one_minus_list_def,list_prod_def]
>> (` (\t.
   (1 - prob p (union_avail_events1 h (&t))) *
   list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_avail_events1 a (&t)) L)))) = (\t.
   (\t. (1 − prob p (union_avail_events1 h (&t)))) t *
   (\t. list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_avail_events1 a (&t)) L)))) t)` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC std_ss[]
>- ( (`(\t. 1 − prob p (union_avail_events1 h (&t))) = (\t. (\t. 1)t − (\t. prob p (union_avail_events1 h (&t))) t)` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[SEQ_CONST]
   >> FULL_SIMP_TAC list_ss[inst_avail_exp_list1_def,inst_avail_exp2_def]
   >> REWRITE_TAC[steady_state_avail_def]
   >> (`((\t.
     SND (h':real#real) / (SND h' + FST h') +
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) --> (SND h' / (SND h' + FST h'))) =
     ((\t.
     (\t. SND h' / (SND  h'+ FST h')) t +
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))t)
      --> (SND h' / (SND h' + FST h') + 0))`
     by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_ADD
   >> RW_TAC std_ss[]
   >- (RW_TAC std_ss[SEQ_CONST])
   >- ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) =
        ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t)) t)
         --> ((FST h' / (SND h' + FST h')) *0))`
        by RW_TAC real_ss[])
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_MUL
      >> RW_TAC real_ss[SEQ_CONST]
      >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      >> MATCH_MP_TAC neg_exp_tend0_new
      >> RW_TAC std_ss[]
      >> RW_TAC std_ss[steady_avail_temp]))
>> FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
>> RW_TAC std_ss[inst_avail_exp_list1_def, GSYM union_avail_event_list1_def]
>> FULL_SIMP_TAC list_ss[ inst_avail_exp_list1_def]
QED

(*---compl_steady_state_avail_equi---------------------------*)
Theorem compl_steady_state_avail_equi :
!M. compl_steady_state_avail M =
        list_prod (one_minus_list (steady_state_avail_list M))
Proof
Induct
>- (RW_TAC list_ss[compl_steady_state_avail_def,steady_state_avail_list_def,one_minus_list_def,list_prod_def])
>> RW_TAC list_ss[compl_steady_state_avail_def,steady_state_avail_list_def,one_minus_list_def,list_prod_def]
QED
(*---parallel_steady_state_avail---------------------------*)
Theorem parallel_rbd_avail :
!p L M.
       prob_space p /\
       (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
       (LENGTH L = LENGTH M) /\
       (!t'. ~NULL (union_avail_event_list1 L &t') /\
       (!z. MEM z (union_avail_event_list1 L ( (&t'))) ==> z IN events p) /\
       mutual_indep p (union_avail_event_list1 L ( (&t')))) /\
       inst_avail_exp_list1 p L M ==>
        (lim (\t.  prob p
             (rbd_struct p
                (parallel (rbd_list (union_avail_event_list1 L (&t)))))) =
          1 -  list_prod (one_minus_list (steady_state_avail_list M)))
Proof
RW_TAC std_ss[]
>> (`!t.  (prob p (rbd_struct p (parallel (rbd_list (union_avail_event_list1 L (&t))))) =
      1 − list_prod (one_minus_list (list_prob p (union_avail_event_list1 L (&t)))))` by RW_TAC std_ss[])
>- (MATCH_MP_TAC parallel_struct_thm
   >> FULL_SIMP_TAC std_ss[]
   >> RW_TAC std_ss[]
   >> FIRST_X_ASSUM(MP_TAC o Q.SPEC `t:num`)
   >> RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\t. 1 −
       list_prod
         (one_minus_list
            (list_prob p (union_avail_event_list1 L (&t)))))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC(`` 1 -  list_prod (one_minus_list (steady_state_avail_list M))``)
   >> (`(\t.
        1 −
        list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 L (&t))))) = (\t.
        (\t. 1) t −
        (\t. list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 L (&t))))) t)` by RW_TAC real_ss[])
    >> POP_ORW
    >> MATCH_MP_TAC SEQ_SUB
    >> RW_TAC std_ss[SEQ_CONST]
    >> RW_TAC std_ss[GSYM compl_steady_state_avail_equi]
    >> MATCH_MP_TAC lim_inst_parall_tend_steady
    >> RW_TAC std_ss[])
>> (`(\t.
        1 −
        list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 L (&t))))) = (\t.
        (\t. 1) t −
        (\t. list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 L (&t))))) t)` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_SUB
>> RW_TAC std_ss[SEQ_CONST]
>> RW_TAC std_ss[GSYM compl_steady_state_avail_equi]
>> MATCH_MP_TAC lim_inst_parall_tend_steady
>> RW_TAC std_ss[]
QED
(*--------lim_inst_parall_series_tend_steady-----------------------------*)
Theorem lim_inst_parall_series_tend_steady :
!p L M.
       prob_space p /\
       (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
       ((LENGTH L = LENGTH M)) /\
       (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M))) /\
       (two_dim_inst_avail_exp p L M) ==>
        ((\t.
         (list_prod o one_minus_list of
          (λa. list_prod (list_prob p a)))
               (list_union_avail_event_list L (&t))) -->
         list_prod (one_minus_list (MAP (\a. steady_state_avail_prod a) M)))
Proof
GEN_TAC
>> REWRITE_TAC[of_DEF,o_THM]
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL_SYM]
   >> RW_TAC list_ss[list_union_avail_event_list_def,steady_state_avail_prod_def,one_minus_list_def,list_prod_def]
   >> RW_TAC std_ss[SEQ_CONST])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> (RW_TAC std_ss[])
>> RW_TAC list_ss[list_union_avail_event_list_def,steady_state_avail_prod_def,one_minus_list_def,list_prod_def]
>> (`(λt.
   (1 − list_prod (list_prob p (union_avail_event_list1 h (&t)))) *
   list_prod
     (one_minus_list
        (MAP (λa. list_prod (list_prob p a))
           (MAP (λa. union_avail_event_list1 a (&t)) L)))) =
   (\t.
    (λt.
        (1 − list_prod (list_prob p (union_avail_event_list1 h (&t))))) t *
        (\t. list_prod
             (one_minus_list
                (MAP (λa. list_prod (list_prob p a))
                     (MAP (λa. union_avail_event_list1 a (&t)) L)))) t)` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC std_ss[]
>- ((`(\t. 1 − list_prod (list_prob p (union_avail_event_list1 h (&t)))) =
    (\t. (\t. 1)t − (\t. list_prod (list_prob p (union_avail_event_list1 h (&t)))) t)` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[SEQ_CONST]
   >> MATCH_MP_TAC series_expec_tends_prod_avail
   >> FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
   >> FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
   >> RW_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
>> FULL_SIMP_TAC list_ss[]
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
>> NTAC 5 (POP_ASSUM MP_TAC)
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC std_ss[]
>> (`(!n. n < LENGTH M ==> (LENGTH (EL n L) = LENGTH (EL n M)))`  by RW_TAC std_ss[])
>- (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
   >> RW_TAC arith_ss[]
   >> FULL_SIMP_TAC list_ss[])
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC std_ss[GSYM list_union_avail_event_list_def]
QED
(*-------------parallel-series ABD--------*)
Theorem steady_state_parallel_series_ABD :
!p L M .  prob_space p /\
              (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
              ((LENGTH L = LENGTH M)) /\
               (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M)))  /\
                (!t'.
                   (!z. MEM z (list_union_avail_event_list L (&t')) ==> ¬NULL z) /\
                   (!z. MEM z (FLAT (list_union_avail_event_list L (&t'))) ==> z IN events p) /\
                mutual_indep p (FLAT (list_union_avail_event_list L (&t')))) /\
                (two_dim_inst_avail_exp p L M) ==>
                  (lim (\t.
                  prob p
                       (rbd_struct p ((parallel of (λa. series (rbd_list a)))
                                                (list_union_avail_event_list L (&t))))) =
                  1 - list_prod (one_minus_list (MAP (\a. steady_state_avail_prod a) M)))
Proof

RW_TAC std_ss[]
>> (`!t. prob p
         (rbd_struct p ((parallel of (λa. series (rbd_list a)))
                        (list_union_avail_event_list L (&t)))) =
        1 −
          (list_prod o one_minus_list of (λa. list_prod (list_prob p a)))
                (list_union_avail_event_list L (&t))` by ALL_TAC)
>- (GEN_TAC
   >> MATCH_MP_TAC parallel_series_struct_rbd_v2
   >> METIS_TAC[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC (``( \t. 1 −
       (list_prod o one_minus_list of (λa. list_prod (list_prob p a)))
                (list_union_avail_event_list L (&t)))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- ( EXISTS_TAC (``1 - list_prod (one_minus_list (MAP (\a. steady_state_avail_prod a) M))``)
   >> (`(\t.
          1 −
           (list_prod ((one_minus_list of (λa. list_prod (list_prob p a)))
                (list_union_avail_event_list L (&t))))) =
        (\t.
         (\t. 1) t −
          (\t. (list_prod ((one_minus_list of (λa. list_prod (list_prob p a)))
                (list_union_avail_event_list L (&t))))) t)` by RW_TAC real_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_SUB
  >> RW_TAC std_ss[SEQ_CONST]
  >> (`(λt.
   list_prod
     ((one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))) =
       (λt.
   (list_prod o
     one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))` by RW_TAC real_ss[o_THM])
  >> POP_ORW
  >> MATCH_MP_TAC lim_inst_parall_series_tend_steady
  >> METIS_TAC[])
>> (`(\t.
          1 −
           (list_prod ((one_minus_list of (λa. list_prod (list_prob p a)))
                (list_union_avail_event_list L (&t))))) =
        (\t.
         (\t. 1) t −
          (\t. (list_prod ((one_minus_list of (λa. list_prod (list_prob p a)))
                (list_union_avail_event_list L (&t))))) t)` by RW_TAC real_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_SUB
  >> RW_TAC std_ss[SEQ_CONST]
  >> (`(λt.
   list_prod
     ((one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))) =
       (λt.
   (list_prod o
     one_minus_list of (λa. list_prod (list_prob p a)))
        (list_union_avail_event_list L (&t)))` by RW_TAC real_ss[o_THM])
  >> POP_ORW
  >> MATCH_MP_TAC lim_inst_parall_series_tend_steady
  >> METIS_TAC[]
QED



(*------------------------*)
Theorem lim_inst_series_parall_tend_steady :
!p L M.
     prob_space p /\ (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
     (LENGTH L = LENGTH M) /\
     (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M))) /\
     two_dim_inst_avail_exp p L M ==>
     ((\t.
      (list_prod of
       (λa. 1 − list_prod (one_minus_list (list_prob p a))))
            (list_union_avail_event_list L (&t))) -->
     list_prod (one_minus_list (MAP (\a. compl_steady_state_avail a) M)))
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL_SYM]
   >> RW_TAC list_ss[of_DEF,o_THM,list_union_avail_event_list_def,one_minus_list_def,list_prod_def]
   >> RW_TAC std_ss[SEQ_CONST])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>> RW_TAC list_ss[of_DEF,o_THM,list_union_avail_event_list_def,one_minus_list_def,list_prod_def]
>> (`(\t.
   (1 −
    list_prod
      (one_minus_list (list_prob p (union_avail_event_list1 h (&t))))) *
   list_prod
     (MAP (λa. 1 − list_prod (one_minus_list (list_prob p a)))
        (MAP (λa. union_avail_event_list1 a (&t)) L))) = (\t.
   (\t. (1 −
    list_prod
      (one_minus_list (list_prob p (union_avail_event_list1 h (&t))))))t *
   (\t. list_prod
     (MAP (λa. 1 − list_prod (one_minus_list (list_prob p a)))
        (MAP (λa. union_avail_event_list1 a (&t)) L))) t)` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC std_ss[]
>- ( (`(\t.
        1 −
        list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 h (&t))))) = (\t.
        (\t. 1) t −
        (\t. list_prod
          (one_minus_list
             (list_prob p (union_avail_event_list1 h (&t))))) t)` by RW_TAC real_ss[])
    >> POP_ORW
    >> MATCH_MP_TAC SEQ_SUB
    >> RW_TAC std_ss[SEQ_CONST]
    >> MATCH_MP_TAC lim_inst_parall_tend_steady
    >> FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
    >> FIRST_X_ASSUM (Q.SPECL_THEN [`0`] MP_TAC)
    >> RW_TAC arith_ss[EL,HD])
>> FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
>> RW_TAC std_ss[]
>> FULL_SIMP_TAC list_ss[two_dim_inst_avail_exp_def]
>> NTAC 3 (POP_ASSUM MP_TAC)
>> FULL_SIMP_TAC std_ss[]
>> RW_TAC std_ss[]
>> (`(!n. n < LENGTH M ==> (LENGTH (EL n L) = LENGTH (EL n M)))` by RW_TAC std_ss[])
 >- (FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`] MP_TAC)
    >> RW_TAC arith_ss[EL,TL])
>> FULL_SIMP_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[of_DEF,o_THM]
>> RW_TAC std_ss[GSYM list_union_avail_event_list_def]
QED
(*-------------Series_parallel ABD---------------------------------*)

Theorem steady_state_series_parallel_avail :
!p L M.
       prob_space p /\
       (!z. MEM z (FLAT M) ==> 0 < FST z /\ 0 < SND z) /\
       ((LENGTH L = LENGTH M)) /\
       (!n. n < LENGTH L ==> (LENGTH (EL n L) = LENGTH (EL n M))) /\
       (!t'.
        (!z. MEM z (list_union_avail_event_list L (&t')) ==> ¬NULL z) /\
        (!z. MEM z (FLAT (list_union_avail_event_list L (&t'))) ==> z IN events p) /\
        mutual_indep p (FLAT (list_union_avail_event_list L (&t')))) /\
      (two_dim_inst_avail_exp p L M) ==>
         (lim (\t. prob p
              (rbd_struct p
                     ((series of (λa. parallel (rbd_list a)))
                        (list_union_avail_event_list L (&t))))) =
          list_prod (one_minus_list (MAP (\a. compl_steady_state_avail a) M)))
Proof
RW_TAC std_ss[]
>> (`!t. prob p
      (rbd_struct p
          ((series of (λa. parallel (rbd_list a)))
               (list_union_avail_event_list L (&t)))) = (list_prod of
       (λa. 1 − list_prod (one_minus_list (list_prob p a))))
            (list_union_avail_event_list L (&t))` by RW_TAC std_ss[])
>- (MATCH_MP_TAC series_parallel_struct_thm_v2
   >> METIS_TAC[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\t.
                   (list_prod of
                     (λa. 1 − list_prod (one_minus_list (list_prob p a))))
                          (list_union_avail_event_list L (&t)))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC(``list_prod (one_minus_list (MAP (\a. compl_steady_state_avail a) M))``)
   >> MATCH_MP_TAC lim_inst_series_parall_tend_steady
   >> RW_TAC std_ss[])
>> MATCH_MP_TAC lim_inst_series_parall_tend_steady
>> RW_TAC std_ss[]
QED

(*--------------------------------------------------------*)
(* Definition. Unavailability Event       *)
(* ------------------------------------------------------------------------- *)
Definition unavail_event_def :
unavail_event p L n t  =
p_space p DIFF (avail_event L n t INTER p_space p)
End
(*--------------------------------------------------------*)
(* Definition. Union Unavailability Event       *)
(* ------------------------------------------------------------------------- *)
Definition union_unavail_events_def :
union_unavail_events p L t  =
p_space p DIFF (union_avail_events1 L t INTER p_space p)
End
(*---------------------------------------------------------*)
(* Definition : Unavailability event list                   *)
(* ------------------------------------------------------------------------- *)
Definition union_unavail_event_list_def :
union_unavail_event_list p L t  =
MAP (\a. union_unavail_events p a t) L
End
(* ------------------------------------------------------------------------- *)
(* Definition: steady state unavailiabilility with failure and repair rate                               *)
(* ------------------------------------------------------------------------- *)
Definition steady_state_unavail_def :
( steady_state_unavail (m:real#real) = FST m / (SND m + FST m))
End

(* ------------------------------------------------------------------------- *)
(* Definition: steady state unavailiabilility with failure and repair rate  list                             *)
(* ------------------------------------------------------------------------- *)
Definition steady_state_unavail_list_def :
( steady_state_unavail_list M = MAP (\a. steady_state_unavail a) M)
End

(*---------------------------------------------------------*)
(* Definition: Instantenous Unavailability pair                  *)
(* ------------------------------------------------------------------------- *)
(*-------------------------*)
Definition inst_unavail_exp_def :
inst_unavail_exp p L m =
 !(t). (prob p ( union_unavail_events p L &t)  =
       (FST (m) / (SND m + FST m)) -
       (FST m /(SND m + FST m)) * exp (-((SND m + FST m))* &t))
End
(*-------------------------*)
Definition inst_unavail_exp_list_def :
(inst_unavail_exp_list p [] M = T) /\
(inst_unavail_exp_list p (h::t) M =
(inst_unavail_exp p h (HD M) /\ inst_unavail_exp_list p t (TL M) ))
End
(*-------------------------*)
Definition two_dim_inst_unavail_exp_def :
(two_dim_inst_unavail_exp p [] M = T) /\
 (two_dim_inst_unavail_exp p (h::t) M =
  (inst_unavail_exp_list p h (HD M) /\ two_dim_inst_unavail_exp p t (TL M) ))
End

(* ------------------------------------------------------------------------- *)
(*--- Definition.  Unavailability FT gates     ----  *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(*--- Definition. AND unavail FT gate     ----  *)
(* ------------------------------------------------------------------------- *)
Definition AND_unavail_FT_gate_def :
 AND_unavail_FT_gate p L t =
       FTree p (AND (gate_list (union_unavail_event_list p L t)))
End
(* ------------------------------------------------------------------------- *)
(* Definition. OR unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
Definition OR_unavail_FT_gate_def :
 OR_unavail_FT_gate p L t =
       FTree p (OR (gate_list (union_unavail_event_list p L t)))
End
(* ------------------------------------------------------------------------- *)
(* Definition. NOR unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
Definition NOR_unavail_FT_gate_def :
 NOR_unavail_FT_gate p L t  =
       p_space p DIFF FTree p (OR (gate_list (union_unavail_event_list p L t)))
End
(* ------------------------------------------------------------------------- *)
(* Definition. NAND unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
Definition NAND_unavail_FT_gate_def :
 NAND_unavail_FT_gate p L1 L2 t  =
             FTree p
               (AND (gate_list (compl_list p (union_unavail_event_list p L1 t) ++
                                             (union_unavail_event_list p L2 t))))
End

(* ------------------------------------------------------------------------- *)
(* Definition. XOR unavail FT gate                                 *)
(* ------------------------------------------------------------------------- *)
Definition XOR_unavail_FT_gate_def :
 XOR_unavail_FT_gate p X Y t  =
           (XOR_FT_gate p (atomic (union_unavail_events p X t))
                          (atomic (union_unavail_events p Y t)))
End

(*---------------------------------------*)
Theorem AND_inst_avail_prod_tends_steady :
 !p L M.
     prob_space p /\ (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
     (LENGTH L = LENGTH M) /\ inst_unavail_exp_list p L M ==>
     ((\t. list_prod (list_prob p (union_unavail_event_list p L (&t)))) -->
     list_prod (steady_state_unavail_list M))
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL_SYM]
   >> RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def]
   >> RW_TAC std_ss[SEQ_CONST])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>>  RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def]
>> (`!t. (
   prob p (union_unavail_events p h (&t)) *
   list_prod
     (list_prob p
        (MAP (\a. union_unavail_events p a (&t)) L))) = (\t.
   prob p (union_unavail_events p h (&t))) t *
   (\t. list_prod
     (list_prob p
        (MAP (\a. union_unavail_events p a (&t)) L))) t` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC std_ss[]
>- (FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def,inst_unavail_exp_def]
   >> REWRITE_TAC[steady_state_unavail_def]
   >> (`((\t.
     FST (h':real#real) / (SND h' + FST h') -
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) --> (FST h' / (SND h' + FST h'))) =
     ((\t.
     (\t. FST (h':real#real) / (SND  h'+ FST h')) t -
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) t)
      --> (FST h' / (SND h' + FST h') - 0))`
      by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[]
   >- (RW_TAC std_ss[SEQ_CONST])
   >- ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) =
        ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t)) t)
         --> ((FST h' / (SND h' + FST h')) * 0))`
          by RW_TAC real_ss[])
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_MUL
      >> RW_TAC real_ss[SEQ_CONST]
      >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      >> MATCH_MP_TAC neg_exp_tend0_new
      >> RW_TAC std_ss[]
      >> RW_TAC std_ss[steady_avail_temp]))
>> FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
>> FULL_SIMP_TAC std_ss[inst_unavail_exp_list_def, GSYM union_unavail_event_list_def, GSYM steady_state_unavail_list_def]
>> FULL_SIMP_TAC list_ss[ inst_unavail_exp_list_def]
QED

(*---------------------------*)
Theorem AND_gate_unavail :
!p L M.  prob_space p /\
             (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
             (LENGTH L = LENGTH M) /\
             (!t'.
               ~NULL (union_unavail_event_list p L &t') /\
                (!z. MEM z (union_unavail_event_list p L ( (&t'))) ==> z IN events p) /\
                mutual_indep p (union_unavail_event_list p L ( (&t')))) /\
             inst_unavail_exp_list p L M ==>
              (lim (\t.  prob p (AND_unavail_FT_gate p L &t)) =
               list_prod (steady_state_unavail_list M))
Proof
RW_TAC std_ss[]
>> RW_TAC std_ss[AND_unavail_FT_gate_def]
>> (`!t.
       prob p
       (FTree p
          (AND (gate_list (union_unavail_event_list p L (&t))))) =
        list_prod (list_prob p (union_unavail_event_list p L (&t)))` by RW_TAC std_ss[])
>- ( MATCH_MP_TAC AND_gate_thm
   >> METIS_TAC[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\t. list_prod
         (list_prob p (union_unavail_event_list p L  (&t))))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC(``list_prod (steady_state_unavail_list M)``)
   >> MATCH_MP_TAC AND_inst_avail_prod_tends_steady
   >> RW_TAC std_ss[])
>> MATCH_MP_TAC AND_inst_avail_prod_tends_steady
>> RW_TAC std_ss[]
QED

(*-------------------*)
Theorem lim_inst_OR_tend_steady0 :
!p L M. prob_space p /\
            (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
            (LENGTH L = LENGTH M) /\
            (inst_unavail_exp_list p L M) ==>
              ((\t.
                 list_prod
                   (one_minus_list
                        (list_prob p (union_unavail_event_list p L (&t)))))-->
               list_prod (one_minus_list (steady_state_unavail_list M)))
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL_SYM]
   >> RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def]
   >> RW_TAC std_ss[one_minus_list_def,list_prod_def,SEQ_CONST])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>>  RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_unavail_list_def]
   >> RW_TAC std_ss[one_minus_list_def,list_prod_def]
>> (` (\t.
   (1 - prob p (union_unavail_events p h (&t))) *
   list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_unavail_events p a (&t)) L)))) = (\t.
   (\t. (1 − prob p (union_unavail_events p h (&t)))) t *
   (\t. list_prod
     (one_minus_list
        (list_prob p (MAP (\a. union_unavail_events p a (&t)) L)))) t)` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC std_ss[]
>- ( (`(\t. 1 − prob p (union_unavail_events p h (&t))) =
    (\t. (\t. 1)t − (\t. prob p (union_unavail_events p h (&t))) t)` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[SEQ_CONST]
   >> FULL_SIMP_TAC list_ss[inst_unavail_exp_list_def,inst_unavail_exp_def]
   >> REWRITE_TAC[steady_state_unavail_def]
   >> (`((\t.
     FST (h':real#real) / (SND h' + FST h') -
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) --> (FST h' / (SND h' + FST h'))) =
     ((\t.
     (\t. FST h' / (SND  h'+ FST h')) t -
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) t)
      --> (FST h' / (SND h' + FST h') - 0))`
         by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[]
   >- (RW_TAC std_ss[SEQ_CONST])
   >- ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) =
        ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t)) t)
         --> ((FST h' / (SND h' + FST h')) *0))`
                 by RW_TAC real_ss[])
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_MUL
      >> RW_TAC real_ss[SEQ_CONST]
      >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      >> MATCH_MP_TAC neg_exp_tend0_new
      >> RW_TAC std_ss[]
      >> RW_TAC std_ss[steady_avail_temp]))
>> FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
>> RW_TAC std_ss[inst_unavail_exp_list_def, GSYM union_unavail_event_list_def,GSYM steady_state_unavail_list_def]
>> FULL_SIMP_TAC list_ss[ inst_unavail_exp_list_def]
QED

(*----------------------------*)
Theorem OR_steady_state_unavail :
!p L M. prob_space p /\
            (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
            (LENGTH L = LENGTH M) /\
            (!t'.
              ~NULL (union_unavail_event_list p L (&t')) /\
              (!z. MEM z (union_unavail_event_list p L (&t')) ==> z IN events p) /\
              mutual_indep p (union_unavail_event_list p L (&t'))) /\
            inst_unavail_exp_list p L M ==>
              (lim
               (\t.
                 prob p (OR_unavail_FT_gate p L &t)) =
              1 -  list_prod (one_minus_list (steady_state_unavail_list M)))
Proof
RW_TAC std_ss[]
>> RW_TAC std_ss[OR_unavail_FT_gate_def]
>> (`!t.
      prob p
       (FTree p (OR (gate_list (union_unavail_event_list p L (&t))))) =
      1 - list_prod (one_minus_list (list_prob p (union_unavail_event_list p L (&t))))` by RW_TAC std_ss[])
>- (MATCH_MP_TAC OR_gate_thm
   >> METIS_TAC[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\t. 1 -list_prod
         (one_minus_list (list_prob p (union_unavail_event_list p L  (&t)))))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC(``1 - list_prod (one_minus_list (steady_state_unavail_list M))``)
   >> (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) t) ` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[SEQ_CONST]
   >> MATCH_MP_TAC lim_inst_OR_tend_steady0
   >> RW_TAC std_ss[])
>> (`(\t.
   1 −
   list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) = (\t.
   (\t. 1) t −
   (\t. list_prod
     (one_minus_list
        (list_prob p (union_unavail_event_list p L (&t))))) t) ` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[SEQ_CONST]
>> MATCH_MP_TAC lim_inst_OR_tend_steady0
>> RW_TAC std_ss[]
QED
(*------------------------------------*)
Theorem steady_state_NOR_unavail_FT_gate :
!p L M.
       prob_space p /\ (!z. MEM z M ==> 0 < FST z /\ 0 < SND z) /\
       (LENGTH L = LENGTH M) /\
       (!t'.
        ~NULL (union_unavail_event_list p L (&t')) /\
        (!z. MEM z (union_unavail_event_list p L (&t')) ==> z IN events p) /\
        mutual_indep p (union_unavail_event_list p L (&t'))) /\
       inst_unavail_exp_list p L M ==>
         (lim
          (\t.
           prob p (NOR_unavail_FT_gate p L &t)) =
         list_prod (one_minus_list (steady_state_unavail_list M)))
Proof
RW_TAC std_ss[NOR_unavail_FT_gate_def]
>> (`!t. (prob p
           (p_space p DIFF
                    FTree p (OR (gate_list (union_unavail_event_list p L (&t))))) =
         1 - prob p (FTree p (OR (gate_list (union_unavail_event_list p L (&t)))))) ` by RW_TAC std_ss[])
>- (MATCH_MP_TAC PROB_COMPL
   >> METIS_TAC[OR_lem3])
>> POP_ORW
>> (`!t.  prob p
       (FTree p (OR (gate_list (union_unavail_event_list p L (&t))))) =
        1 - list_prod (one_minus_list (list_prob p (union_unavail_event_list p L (&t))))` by RW_TAC std_ss[])
>- (MATCH_MP_TAC OR_gate_thm
   >> METIS_TAC[])
>> POP_ORW
>> RW_TAC real_ss[]
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC (``( \ t.
       list_prod
         (one_minus_list (list_prob p (union_unavail_event_list p L (&t)))))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC (``list_prod (one_minus_list (steady_state_unavail_list M))``)
   >> MATCH_MP_TAC lim_inst_OR_tend_steady0
   >> RW_TAC std_ss[])
>> MATCH_MP_TAC lim_inst_OR_tend_steady0
>> RW_TAC std_ss[]
QED
(*------------------------*)
Theorem in_events_normal_events :
!p A t. prob_space p /\ (p_space p DIFF (A INTER p_space p) IN events p) ==> (A INTER p_space p IN events p)
Proof
 REPEAT GEN_TAC
 >> RW_TAC std_ss[]
 >> (`A INTER p_space p = p_space p DIFF (p_space p DIFF (A INTER p_space p))` by MATCH_MP_TAC EQ_SYM)
 >- (DEP_REWRITE_TAC[DIFF_DIFF_SUBSET]
    >> RW_TAC std_ss[INTER_SUBSET])
 >> POP_ORW
 >> MATCH_MP_TAC EVENTS_COMPL
 >> RW_TAC std_ss[]
QED


(*-------------------------*)
Theorem lim_inst_OR_tend_steady :
!p L M. prob_space p /\
            (!z. MEM z M ==> (0 < FST z /\ 0 < SND z)) /\
            (LENGTH L = LENGTH M) /\
            (!t'.
              (!z. MEM z ((union_unavail_event_list p L (&t'))) ==> z IN events p)) /\
            (inst_avail_exp_list2 p L M) ==>
              (\t.
                list_prod
                  (list_prob p
                    (compl_list p (union_unavail_event_list p L (&t))))) -->
              list_prod (steady_state_avail_list M)
Proof
GEN_TAC
>> Induct
>- (RW_TAC list_ss[LENGTH_NIL_SYM]
   >> RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_avail_list_def,compl_list_def]
   >> RW_TAC std_ss[SEQ_CONST])
>> GEN_TAC
>> Induct
>- (RW_TAC list_ss[])
>>  RW_TAC list_ss[union_unavail_event_list_def,list_prod_def,list_prob_def,steady_state_avail_list_def,compl_list_def]
   >> RW_TAC std_ss[one_minus_list_def,list_prod_def]
>> (` (\t.
   prob p (p_space p DIFF union_unavail_events p h (&t)) *
   list_prod
     (list_prob p
        (MAP (\a. p_space p DIFF a)
           (MAP (\a. union_unavail_events p a (&t)) L)))) = (\t.
   (\t. prob p (p_space p DIFF union_unavail_events p h (&t))) t *
   (\t. list_prod
     (list_prob p
        (MAP (\a. p_space p DIFF a)
           (MAP (\a. union_unavail_events p a (&t)) L)))) t)` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_MUL
>> RW_TAC std_ss[]
>- ( RW_TAC std_ss[union_unavail_events_def]
   >> (`!t. (p_space p DIFF
      (p_space p DIFF union_avail_events1 h (&t) INTER p_space p)) = union_avail_events1 h (&t) INTER p_space p ` by RW_TAC std_ss[])
      >- ( DEP_REWRITE_TAC[DIFF_DIFF_SUBSET]
         >> RW_TAC std_ss[INTER_SUBSET])
      >> POP_ORW
      >> FULL_SIMP_TAC list_ss[inst_avail_exp_list2_def,inst_avail_exp3_def]
      >> RW_TAC std_ss[steady_state_avail_def]
      >> (`((\t.
     SND (h':real#real) / (SND h' + FST h') +
     FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t)) --> (SND h' / (SND h' + FST h'))) =
     ((\t.
     (\t. SND h' / (SND  h'+ FST h')) t +
     (\t. FST h' / (SND h' + FST h') * exp (-(SND h' + FST h') * &t))t)
      --> (SND h' / (SND h' + FST h') + 0))`
            by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_ADD
   >> RW_TAC std_ss[]
   >- (RW_TAC std_ss[SEQ_CONST])
   >- ((`((\t. FST  h'/ (SND h' + FST h') * exp (-(SND h'  + FST h') * &t)) --> 0) =
        ((\t. (\t. FST h' / (SND h' + FST h'))t * (\t. exp (-(SND h' + FST h') * &t))t)
         --> ((FST h' / (SND h' + FST h')) *0))`
          by RW_TAC real_ss[])
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_MUL
      >> RW_TAC real_ss[SEQ_CONST]
      >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      >> MATCH_MP_TAC neg_exp_tend0_new
      >> RW_TAC std_ss[]
      >> RW_TAC std_ss[steady_avail_temp]))
>> FIRST_X_ASSUM (Q.SPECL_THEN [`M`] MP_TAC)
>> FULL_SIMP_TAC list_ss[ inst_avail_exp_list2_def,union_unavail_event_list_def]
>> RW_TAC std_ss[]
>> (`(!t' z.
         MEM z (MAP (\a. union_unavail_events p a (&t')) L) ==>
         z IN events p)` by RW_TAC std_ss[])
   >- (FIRST_X_ASSUM (Q.SPECL_THEN [`t'`,`z`] MP_TAC)
      >> RW_TAC list_ss[])
   >> METIS_TAC[GSYM compl_list_def]
QED


(*-------------------------*)
Theorem NAND_steady_state_avail :
!p L1 L2 M1 M2.
          prob_space p /\
          (!z. MEM z (M1++M2) ==> 0 < FST z /\ 0 < SND z) /\
          ((LENGTH (L1) = LENGTH (M1)) /\ (LENGTH L2 = LENGTH M2)) /\
          (!t'.
            1 ≤ LENGTH  (union_unavail_event_list p L1 (&t') ++
                         union_unavail_event_list p L2 (&t')) /\
            (!z. MEM z ((union_unavail_event_list p L1 (&t')) ++
                        (union_unavail_event_list p L2 (&t'))) ==> z IN events p) /\
            mutual_indep p ((union_unavail_event_list p L1 (&t')) ++
                         (union_unavail_event_list p L2 (&t')))) /\
         inst_avail_exp_list2 p L1 M1 /\ inst_unavail_exp_list p L2 M2 ==>
          (lim
            (\t.
             prob p (NAND_unavail_FT_gate p L1 L2 &t)) =
          list_prod ((steady_state_avail_list M1)) *
          list_prod ((steady_state_unavail_list M2)))
Proof
RW_TAC std_ss[]
>> (`!t. prob p
            (NAND_unavail_FT_gate p L1 L2 (&t)) =
         list_prod (list_prob p (compl_list p (union_unavail_event_list p L1 (&t)))) *
         list_prod (list_prob p (union_unavail_event_list p L2 (&t)))`  by RW_TAC std_ss[])
>- (RW_TAC std_ss[NAND_unavail_FT_gate_def]
   >> MATCH_MP_TAC NAND_FT_gate
   >> ASM_REWRITE_TAC[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\t. list_prod
         (list_prob p
            (compl_list p (union_unavail_event_list p L1 (&t)))) *
       list_prod (list_prob p (union_unavail_event_list p L2 (&t))))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC(``( list_prod (steady_state_avail_list M1) *list_prod (steady_state_unavail_list M2))``)
   >> (`(\t.
   list_prod
     (list_prob p (compl_list p (union_unavail_event_list p L1 (&t)))) *
   list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) =
   (\t.
        (\t. list_prod
             (list_prob p (compl_list p (union_unavail_event_list p L1 (&t))))) t *
                (\t. list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) t)  ` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_MUL
   >> RW_TAC std_ss[]
   >- (MATCH_MP_TAC lim_inst_OR_tend_steady
      >> FULL_SIMP_TAC list_ss[]
      >> RW_TAC std_ss[]
      >> FIRST_X_ASSUM (Q.SPECL_THEN [`t'`] MP_TAC)
      >> FULL_SIMP_TAC list_ss[])
   >> MATCH_MP_TAC  AND_inst_avail_prod_tends_steady
   >> FULL_SIMP_TAC list_ss[])
>> (`(\t.
   list_prod
     (list_prob p (compl_list p (union_unavail_event_list p L1 (&t)))) *
   list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) =(\t.
   (\t. list_prod
     (list_prob p (compl_list p (union_unavail_event_list p L1 (&t))))) t *
   (\t. list_prod (list_prob p (union_unavail_event_list p L2 (&t)))) t)  ` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_MUL
   >> RW_TAC std_ss[]
   >- (MATCH_MP_TAC lim_inst_OR_tend_steady
      >> FULL_SIMP_TAC list_ss[]
      >> RW_TAC std_ss[]
      >> FIRST_X_ASSUM (Q.SPECL_THEN [`t'`] MP_TAC)
      >> FULL_SIMP_TAC list_ss[])
   >> MATCH_MP_TAC  AND_inst_avail_prod_tends_steady
   >> FULL_SIMP_TAC list_ss[]
QED
(*---------------------*)
Theorem inst_XOR_tends_steady :
!p X1 m1.
       inst_unavail_exp p X1 m1 /\
       (0 < FST m1 /\ 0 < SND m1) ==>
        ((\t. prob p (union_unavail_events p X1 (&t))) --> steady_state_unavail m1)
Proof
RW_TAC std_ss[]
>> FULL_SIMP_TAC std_ss[inst_unavail_exp_def]
     >> RW_TAC std_ss[steady_state_unavail_def]
     >> (`((\t.
     FST (m1:real#real) / (SND m1 + FST m1) -
     FST m1 / (SND m1 + FST m1) * exp (-(SND m1 + FST m1) * &t)) --> (FST m1 / (SND m1 + FST m1))) =
    ((\t.
     (\t. FST m1 / (SND  m1+ FST m1)) t -
     (\t. FST m1 / (SND m1 + FST m1) * exp (-(SND m1 + FST m1) * &t)) t)
      --> (FST m1 / (SND m1 + FST m1) - 0))`
           by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_SUB
   >> RW_TAC std_ss[]
   >- (RW_TAC std_ss[SEQ_CONST])
   >> (`((\t. FST  (m1:real#real) / (SND m1 + FST m1) * exp (-(SND m1  + FST m1) * &t)) --> 0) =
       ((\t. (\t. FST m1 / (SND m1 + FST m1))t * (\t. exp (-(SND m1 + FST m1) * &t)) t)
        --> ((FST m1 / (SND m1 + FST m1)) *0))`
         by RW_TAC real_ss[])
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_MUL
      >> RW_TAC real_ss[SEQ_CONST]
      >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> RW_TAC std_ss[GSYM REAL_MUL_RNEG]
      >> MATCH_MP_TAC neg_exp_tend0_new
      >> RW_TAC std_ss[]
      >> RW_TAC std_ss[steady_avail_temp]
QED

(*--------------------*)

Theorem XOR_steady_unavail :
!p X1 X2 m1 m2 t.
     prob_space p  /\
     (!t'.
       union_unavail_events p X1 (&t') IN events p /\
       union_unavail_events p X2 (&t') IN events p /\
       indep p (union_unavail_events p X1 (&t'))
       (union_unavail_events p X2 (&t'))) /\
     ((0 < FST m1) /\ (0 < SND m1)) /\
     ((0 < FST m2) /\ 0 < SND m2) /\
     (inst_unavail_exp p X1 m1) /\
     (inst_unavail_exp p X2 m2) ==>
       (lim (\t.
            prob p
             (XOR_FT_gate p (atomic (union_unavail_events p X1 &t))
                            (atomic (union_unavail_events p X2 &t)))) =
       steady_state_unavail m1 * (1 - steady_state_unavail m2) +
       steady_state_unavail m2 * (1 - steady_state_unavail m1))
Proof
RW_TAC std_ss[]
>> (`!t. prob p
           (XOR_FT_gate p (atomic (union_unavail_events p X1 &t))
                      (atomic (union_unavail_events p X2 &t))) =
        prob p(union_unavail_events p X1 (&t))  *
        (1 - prob p (union_unavail_events p X2 (&t))) +
        prob p  (union_unavail_events p X2 (&t)) * (1- prob p (union_unavail_events p X1 (&t)))` by RW_TAC std_ss[])
>- (MATCH_MP_TAC XOR_FT_gate_thm
   >> METIS_TAC[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_UNIQ
>> EXISTS_TAC(``(\t.
                 prob p (union_unavail_events p X1 (&t)) *
                 (1 − prob p (union_unavail_events p X2 (&t))) +
                 prob p (union_unavail_events p X2 (&t)) *
                 (1 − prob p (union_unavail_events p X1 (&t))))``)
>> RW_TAC std_ss[GSYM SEQ_LIM,convergent]
>- (EXISTS_TAC(``
(steady_state_unavail m1 * (1 − steady_state_unavail m2) +
 steady_state_unavail m2 * (1 − steady_state_unavail m1))``)
   >> (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t))) +
   prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) =(\t.
   (\t. prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) t +
   (\t. prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) t) ` by RW_TAC real_ss[])
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_ADD
   >> RW_TAC std_ss[]
   >- ( (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) = (\t.
   (\t. prob p (union_unavail_events p X1 (&t))) t *
  (\t.  (1 − prob p (union_unavail_events p X2 (&t)))) t)` by RW_TAC real_ss[])
     >> POP_ORW
     >> MATCH_MP_TAC SEQ_MUL
     >> RW_TAC std_ss[]
     >- ( MATCH_MP_TAC inst_XOR_tends_steady
        >> METIS_TAC[])
     >> (`(\t. 1 − prob p (union_unavail_events p X2 (&t))) =
          (\t. (\t. 1) t − (\t. prob p (union_unavail_events p X2 (&t))) t) `  by RW_TAC real_ss[])
     >> POP_ORW
     >> MATCH_MP_TAC SEQ_SUB
     >> RW_TAC std_ss[SEQ_CONST]
     >> MATCH_MP_TAC inst_XOR_tends_steady
     >> METIS_TAC[])
   >> (`(\t.
   prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) = (\t.
   (\t. prob p (union_unavail_events p X2 (&t))) t *
  (\t.  (1 − prob p (union_unavail_events p X1 (&t)))) t)` by RW_TAC real_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_MUL
  >> RW_TAC std_ss[]
  >- (MATCH_MP_TAC inst_XOR_tends_steady
     >> METIS_TAC[])
  >> (`(\t. 1 − prob p (union_unavail_events p X1 (&t))) =
      (\t. (\t. 1) t − (\t. prob p (union_unavail_events p X1 (&t))) t) `  by RW_TAC real_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_SUB
  >> RW_TAC std_ss[SEQ_CONST]
  >> MATCH_MP_TAC inst_XOR_tends_steady
  >> METIS_TAC[])
>> (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t))) +
   prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) =(\t.
   (\t. prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) t +
   (\t. prob p (union_unavail_events p X2 (&t)) *
   (1 − prob p (union_unavail_events p X1 (&t)))) t) ` by RW_TAC real_ss[])
>> POP_ORW
>> MATCH_MP_TAC SEQ_ADD
>> RW_TAC std_ss[]
>- ( (`(\t.
   prob p (union_unavail_events p X1 (&t)) *
   (1 − prob p (union_unavail_events p X2 (&t)))) =
   (\t.
   (\t. prob p (union_unavail_events p X1 (&t))) t *
  (\t.  (1 − prob p (union_unavail_events p X2 (&t)))) t)` by RW_TAC real_ss[])
     >> POP_ORW
     >> MATCH_MP_TAC SEQ_MUL
     >> RW_TAC std_ss[]
     >- ( MATCH_MP_TAC inst_XOR_tends_steady
        >> METIS_TAC[])
     >> (`(\t. 1 − prob p (union_unavail_events p X2 (&t))) =
          (\t. (\t. 1) t − (\t. prob p (union_unavail_events p X2 (&t))) t) `  by RW_TAC real_ss[])
     >> POP_ORW
     >> MATCH_MP_TAC SEQ_SUB
     >> RW_TAC std_ss[SEQ_CONST]
     >> MATCH_MP_TAC inst_XOR_tends_steady
     >> METIS_TAC[])
>> (`(\t.
     prob p (union_unavail_events p X2 (&t)) *
     (1 − prob p (union_unavail_events p X1 (&t)))) =
     (\t.
     (\t. prob p (union_unavail_events p X2 (&t))) t *
    (\t.  (1 − prob p (union_unavail_events p X1 (&t)))) t)` by RW_TAC real_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_MUL
  >> RW_TAC std_ss[]
  >- (MATCH_MP_TAC inst_XOR_tends_steady
     >> METIS_TAC[])
  >> (`(\t. 1 − prob p (union_unavail_events p X1 (&t))) =
       (\t. (\t. 1) t − (\t. prob p (union_unavail_events p X1 (&t))) t) `  by RW_TAC real_ss[])
  >> POP_ORW
  >> MATCH_MP_TAC SEQ_SUB
  >> RW_TAC std_ss[SEQ_CONST]
  >> MATCH_MP_TAC inst_XOR_tends_steady
  >> METIS_TAC[]
QED

val _ = export_theory();
