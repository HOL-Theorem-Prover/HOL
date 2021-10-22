(* ========================================================================= *)
(* The Theory of (general) Stochastic Processes (ongoing)                    *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2021)                 *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory pred_setTheory pred_setLib logrootTheory
     realTheory realLib seqTheory transcTheory real_sigmaTheory iterateTheory
     real_topologyTheory numLib posetTheory;

open hurdUtils util_probTheory sigma_algebraTheory extrealTheory measureTheory
     borelTheory lebesgueTheory martingaleTheory probabilityTheory;

val _ = new_theory "stochastic_process";

(* ------------------------------------------------------------------------- *)
(*  General filtration/martingale with poset indexes (Chapter 25 of [9])     *)
(*  (moved here from martingaleTheory)                                       *)
(* ------------------------------------------------------------------------- *)

Theorem POSET_NUM_LE :
    poset (univ(:num),$<=)
Proof
    RW_TAC std_ss [poset_def]
 >- (Q.EXISTS_TAC `0` >> REWRITE_TAC [GSYM IN_APP, IN_UNIV])
 >- (MATCH_MP_TAC LESS_EQUAL_ANTISYM >> art [])
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC `y` >> art []
QED

(* below J is an index set, R is a partial order on J *)
Definition general_filtration_def :
   general_filtration (J,R) A a =
     (poset (J,R) /\ (!n. n IN J ==> sub_sigma_algebra (a n) A) /\
      (!i j. i IN J /\ j IN J /\ R i j ==> subsets (a i) SUBSET subsets (a j)))
End

Theorem filtration_alt_general : (* was: filtration_alt *)
    !A a. filtration A a = general_filtration (univ(:num),$<=) A a
Proof
    RW_TAC std_ss [filtration_def, general_filtration_def, POSET_NUM_LE, IN_UNIV]
QED

Definition general_filtered_measure_space_def :
    general_filtered_measure_space (J,R) (sp,sts,m) a =
      (measure_space (sp,sts,m) /\ general_filtration (J,R) (sp,sts) a)
End

Theorem filtered_measure_space_alt_general :
    !sp sts m a. filtered_measure_space (sp,sts,m) a <=>
                 general_filtered_measure_space (univ(:num),$<=) (sp,sts,m) a
Proof
    RW_TAC std_ss [filtered_measure_space_def, general_filtered_measure_space_def,
                   filtration_alt_general, POSET_NUM_LE, IN_UNIV]
QED

Definition general_sigma_finite_filtered_measure_space_def :
    general_sigma_finite_filtered_measure_space (J,R) (sp,sts,m) a =
      (general_filtered_measure_space (J,R) (sp,sts,m) a /\
       !n. n IN J ==> sigma_finite (sp,subsets (a n),m))
End

Theorem sigma_finite_filtered_measure_space_alt_general :
    !sp sts m a. sigma_finite_filtered_measure_space (sp,sts,m) a <=>
                 general_sigma_finite_filtered_measure_space (univ(:num),$<=) (sp,sts,m) a
Proof
    rw [sigma_finite_filtered_measure_space_alt_all, GSYM CONJ_ASSOC,
        general_sigma_finite_filtered_measure_space_def,
        GSYM filtered_measure_space_alt_general, filtered_measure_space_def]
QED

(* `general_martingale m a u (univ(:num),$<=) = martingale m a u`

   This is Definition 25.3 [1, p.301].
 *)
Definition general_martingale_def :
   general_martingale (J,R) m a u =
     (general_sigma_finite_filtered_measure_space (J,R) m a /\
      (!n. n IN J ==> integrable m (u n)) /\
      !i j s. i IN J /\ j IN J /\ R i j /\ s IN (subsets (a i)) ==>
             (integral m (\x. u i x * indicator_fn s x) =
              integral m (\x. u j x * indicator_fn s x)))
End

(* or "upwards directed" *)
Definition general_upwards_filtering_def :
    general_upwards_filtering (J,R) = !a b. a IN J /\ b IN J ==> ?c. c IN J /\ R a c /\ R b c
End

val _ = export_theory ();
val _ = html_theory "stochastic_process";

(* References:

  [1] Kolmogorov, A.N.: Foundations of the Theory of Probability (Grundbegriffe der
      Wahrscheinlichkeitsrechnung). Chelsea Publishing Company, New York. (1950).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [3] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Editoin).
      World Scientific Publishing Company (2006).
  [4] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [5] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [6] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).
  [7] Cinlar, E.: Probability and Stochastics. Springer (2011).
  [8] J.L. Doob (1953), Stochastic processes (2nd ed.). John Wiley & Sons, New York.
  [9] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [10] Lindgren, G.: Stationary Stochastic Processes. CRC Press (2012).
  [11] Wentzell, A.D.: Theorie zufalliger Prozesse. Springer-Verlag, Basel (2014).
 *)
