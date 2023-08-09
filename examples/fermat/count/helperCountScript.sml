(* ------------------------------------------------------------------------- *)
(* Count Helper.                                                             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperCount";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* val _ = load "EulerTheory"; *)
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open arithmeticTheory pred_setTheory;


(* ------------------------------------------------------------------------- *)
(* Count Helper Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   over f s t      = !x. x IN s ==> f x IN t
   s bij_eq t      = ?f. BIJ f s t
   s =b= t         = ?f. BIJ f s t
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Set Theorems:
   over_inj            |- !f s t. INJ f s t ==> over f s t
   over_surj           |- !f s t. SURJ f s t ==> over f s t
   over_bij            |- !f s t. BIJ f s t ==> over f s t
   SURJ_CARD_IMAGE_EQ  |- !f s t. FINITE t /\ over f s t ==>
                                  (SURJ f s t <=> CARD (IMAGE f s) = CARD t)
   FINITE_SURJ_IFF     |- !f s t. FINITE t ==>
                                  (SURJ f s t <=> CARD (IMAGE f s) = CARD t /\ over f s t)
   INJ_IMAGE_BIJ_IFF   |- !f s t. INJ f s t <=> BIJ f s (IMAGE f s) /\ over f s t
   INJ_IFF_BIJ_IMAGE   |- !f s t. over f s t ==> (INJ f s t <=> BIJ f s (IMAGE f s))
   INJ_IMAGE_IFF       |- !f s t. INJ f s t <=> INJ f s (IMAGE f s) /\ over f s t
   FUNSET_ALT          |- !P Q. FUNSET P Q = {f | over f P Q}

   Bijective Equivalence:
   bij_eq_empty        |- !s t. s =b= t ==> (s = {} <=> t = {})
   bij_eq_refl         |- !s. s =b= s
   bij_eq_sym          |- !s t. s =b= t <=> t =b= s
   bij_eq_trans        |- !s t u. s =b= t /\ t =b= u ==> s =b= u
   bij_eq_equiv_on     |- !P. $=b= equiv_on P
   bij_eq_finite       |- !s t. s =b= t ==> (FINITE s <=> FINITE t)
   bij_eq_count        |- !s. FINITE s ==> s =b= count (CARD s)
   bij_eq_card         |- !s t. s =b= t /\ (FINITE s \/ FINITE t) ==> CARD s = CARD t
   bij_eq_card_eq      |- !s t. FINITE s /\ FINITE t ==> (s =b= t <=> CARD s = CARD t)

   Alternate characterisation of maps:
   surj_preimage_not_empty
                       |- !f s t. SURJ f s t <=>
                                  over f s t /\ !y. y IN t ==> preimage f s y <> {}
   inj_preimage_empty_or_sing
                       |- !f s t. INJ f s t <=>
                                  over f s t /\ !y. y IN t ==> preimage f s y = {} \/
                                                               SING (preimage f s y)
   bij_preimage_sing   |- !f s t. BIJ f s t <=>
                                  over f s t /\ !y. y IN t ==> SING (preimage f s y)
   surj_iff_preimage_card_not_0
                       |- !f s t. FINITE s /\ over f s t ==>
                                  (SURJ f s t <=>
                                   !y. y IN t ==> CARD (preimage f s y) <> 0)
   inj_iff_preimage_card_le_1
                       |- !f s t. FINITE s /\ over f s t ==>
                                  (INJ f s t <=>
                                   !y. y IN t ==> CARD (preimage f s y) <= 1)
   bij_iff_preimage_card_eq_1
                       |- !f s t. FINITE s /\ over f s t ==>
                                  (BIJ f s t <=>
                                   !y. y IN t ==> CARD (preimage f s y) = 1)
   finite_surj_inj_iff |- !f s t. FINITE s /\ SURJ f s t ==>
                                  (INJ f s t <=>
                                   !e. e IN IMAGE (preimage f s) t ==> CARD e = 1)
*)

(* ------------------------------------------------------------------------- *)
(* Set Theorems                                                              *)
(* ------------------------------------------------------------------------- *)

(* Overload a function from domain to range. *)
val _ = overload_on("over", ``\f s t. !x. x IN s ==> f x IN t``);
(* not easy to make this a good infix operator! *)

(* Theorem: INJ f s t ==> over f s t *)
(* Proof: by INJ_DEF. *)
Theorem over_inj:
  !f s t. INJ f s t ==> over f s t
Proof
  simp[INJ_DEF]
QED

(* Theorem: SURJ f s t ==> over f s t *)
(* Proof: by SURJ_DEF. *)
Theorem over_surj:
  !f s t. SURJ f s t ==> over f s t
Proof
  simp[SURJ_DEF]
QED

(* Theorem: BIJ f s t ==> over f s t *)
(* Proof: by BIJ_DEF, INJ_DEF. *)
Theorem over_bij:
  !f s t. BIJ f s t ==> over f s t
Proof
  simp[BIJ_DEF, INJ_DEF]
QED

(* Theorem: FINITE t /\ over f s t ==>
            (SURJ f s t <=> CARD (IMAGE f s) = CARD t) *)
(* Proof:
   If part: SURJ f s t ==> CARD (IMAGE f s) = CARD t
      Note IMAGE f s = t           by IMAGE_SURJ
      Hence true.
   Only-if part: CARD (IMAGE f s) = CARD t ==> SURJ f s t
      By contradiction, suppose ~SURJ f s t.
      Then IMAGE f s <> t          by IMAGE_SURJ
       but IMAGE f s SUBSET t      by IMAGE_SUBSET_TARGET
        so IMAGE f s PSUBSET t     by PSUBSET_DEF
       ==> CARD (IMAGE f s) < CARD t
                                   by CARD_PSUBSET
      This contradicts CARD (IMAGE f s) = CARD t.
*)
Theorem SURJ_CARD_IMAGE_EQ:
  !f s t. FINITE t /\ over f s t ==>
          (SURJ f s t <=> CARD (IMAGE f s) = CARD t)
Proof
  rw[EQ_IMP_THM] >-
  fs[IMAGE_SURJ] >>
  spose_not_then strip_assume_tac >>
  `IMAGE f s <> t` by rw[GSYM IMAGE_SURJ] >>
  `IMAGE f s PSUBSET t` by fs[IMAGE_SUBSET_TARGET, PSUBSET_DEF] >>
  imp_res_tac CARD_PSUBSET >>
  decide_tac
QED

(* Theorem: FINITE t ==>
            (SURJ f s t <=> CARD (IMAGE f s) = CARD t /\ over f s t) *)
(* Proof:
   If part: true       by SURJ_DEF, IMAGE_SURJ
   Only-if part: true  by SURJ_CARD_IMAGE_EQ
*)
Theorem FINITE_SURJ_IFF:
  !f s t. FINITE t ==>
          (SURJ f s t <=> CARD (IMAGE f s) = CARD t /\ over f s t)
Proof
  metis_tac[SURJ_CARD_IMAGE_EQ, SURJ_DEF]
QED

(* Note: this cannot be proved:
g `!f s t. FINITE t /\ over f s t ==>
          (INJ f s t <=> CARD (IMAGE f s) = CARD t)`;
Take f = I, s = count m, t = count n, with m <= n.
Then INJ I (count m) (count n)
and IMAGE I (count m) = (count m)
so CARD (IMAGE f s) = m, CARD t = n, may not equal.
*)

(* INJ_IMAGE_BIJ |- !s f. (?t. INJ f s t) ==> BIJ f s (IMAGE f s) *)

(* Theorem: INJ f s t <=> (BIJ f s (IMAGE f s) /\ over f s t) *)
(* Proof:
   If part: INJ f s t ==> BIJ f s (IMAGE f s) /\ over f s t
      Note BIJ f s (IMAGE f s)     by INJ_IMAGE_BIJ
       and over f s t by INJ_DEF
   Only-if: BIJ f s (IMAGE f s) /\ over f s t ==> INJ f s t
      By INJ_DEF, this is to show:
      (1) x IN s ==> f x IN t, true by given
      (2) x IN s /\ y IN s /\ f x = f y ==> x = y
          Note f x IN (IMAGE f s)  by IN_IMAGE
           and f y IN (IMAGE f s)  by IN_IMAGE
            so f x = f y ==> x = y by BIJ_IS_INJ
*)
Theorem INJ_IMAGE_BIJ_IFF:
  !f s t. INJ f s t <=> (BIJ f s (IMAGE f s) /\ over f s t)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[INJ_IMAGE_BIJ] >-
  fs[INJ_DEF] >>
  rw[INJ_DEF] >>
  metis_tac[BIJ_IS_INJ, IN_IMAGE]
QED

(* Theorem: over f s t ==> (INJ f s t <=> BIJ f s (IMAGE f s)) *)
(* Proof: by INJ_IMAGE_BIJ_IFF. *)
Theorem INJ_IFF_BIJ_IMAGE:
  !f s t. over f s t ==> (INJ f s t <=> BIJ f s (IMAGE f s))
Proof
  metis_tac[INJ_IMAGE_BIJ_IFF]
QED

(*
INJ_IMAGE  |- !f s t. INJ f s t ==> INJ f s (IMAGE f s)
*)

(* Theorem: INJ f s t <=> INJ f s (IMAGE f s) /\ over f s t *)
(* Proof:
   Let P = over f s t.
   If part: INJ f s t ==> INJ f s (IMAGE f s) /\ P
      Note INJ f s (IMAGE f s)     by INJ_IMAGE
       and P is true               by INJ_DEF
   Only-if part: INJ f s (IMAGE f s) /\ P ==> INJ f s t
      Note s SUBSET s              by SUBSET_REFL
       and (IMAGE f s) SUBSET t    by IMAGE_SUBSET_TARGET
      Thus INJ f s t               by INJ_SUBSET
*)
Theorem INJ_IMAGE_IFF:
  !f s t. INJ f s t <=> INJ f s (IMAGE f s) /\ over f s t
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[INJ_IMAGE] >-
  fs[INJ_DEF] >>
  `s SUBSET s` by rw[] >>
  `(IMAGE f s) SUBSET t` by fs[IMAGE_SUBSET_TARGET] >>
  metis_tac[INJ_SUBSET]
QED

(* pred_setTheory:
FUNSET |- !P Q. FUNSET P Q = (\f. over f P Q)
*)

(* Theorem: FUNSET P Q = {f | over f P Q} *)
(* Proof: by FUNSET, EXTENSION *)
Theorem FUNSET_ALT:
  !P Q. FUNSET P Q = {f | over f P Q}
Proof
  rw[FUNSET, EXTENSION]
QED

(* ------------------------------------------------------------------------- *)
(* Bijective Equivalence                                                     *)
(* ------------------------------------------------------------------------- *)

(* Overload bijectively equal. *)
val _ = overload_on("bij_eq", ``\s t. ?f. BIJ f s t``);
val _ = set_fixity "bij_eq" (Infix(NONASSOC, 450)); (* same as relation *)

val _ = overload_on ("=b=", ``$bij_eq``);
val _ = set_fixity "=b=" (Infix(NONASSOC, 450));

(*
> BIJ_SYM;
val it = |- !s t. s bij_eq t <=> t bij_eq s: thm
> BIJ_SYM;
val it = |- !s t. s =b= t <=> t =b= s: thm
> FINITE_BIJ_COUNT_CARD
val it = |- !s. FINITE s ==> count (CARD s) =b= s: thm
*)

(* Theorem: s =b= t ==> (s = {} <=> t = {}) *)
(* Proof: by BIJ_EMPTY. *)
Theorem bij_eq_empty:
  !s t. s =b= t ==> (s = {} <=> t = {})
Proof
  metis_tac[BIJ_EMPTY]
QED

(* Theorem: s =b= s *)
(* Proof: by BIJ_I_SAME *)
Theorem bij_eq_refl:
  !s. s =b= s
Proof
  metis_tac[BIJ_I_SAME]
QED

(* Theorem alias *)
Theorem bij_eq_sym = BIJ_SYM;
(* val bij_eq_sym = |- !s t. s =b= t <=> t =b= s: thm *)

Theorem bij_eq_trans = BIJ_TRANS;
(* val bij_eq_trans = |- !s t u. s =b= t /\ t =b= u ==> s =b= u: thm *)

(* Idea: bij_eq is an equivalence relation on any set of sets. *)

(* Theorem: $=b= equiv_on P *)
(* Proof:
   By equiv_on_def, this is to show:
   (1) s IN P ==> s =b= s, true    by bij_eq_refl
   (2) s IN P /\ t IN P ==> (t =b= s <=> s =b= t)
       This is true                by bij_eq_sym
   (3) s IN P /\ s' IN P /\ t IN P /\
       BIJ f s s' /\ BIJ f' s' t ==> s =b= t
       This is true                by bij_eq_trans
*)
Theorem bij_eq_equiv_on:
  !P. $=b= equiv_on P
Proof
  rw[equiv_on_def] >-
  simp[bij_eq_refl] >-
  simp[Once bij_eq_sym] >>
  metis_tac[bij_eq_trans]
QED

(* Theorem: s =b= t ==> (FINITE s <=> FINITE t) *)
(* Proof: by BIJ_FINITE_IFF *)
Theorem bij_eq_finite:
  !s t. s =b= t ==> (FINITE s <=> FINITE t)
Proof
  metis_tac[BIJ_FINITE_IFF]
QED

(* This is the iff version of:
pred_setTheory.FINITE_BIJ_CARD;
|- !f s t. FINITE s /\ BIJ f s t ==> CARD s = CARD t
*)

(* Theorem: FINITE s ==> s =b= (count (CARD s)) *)
(* Proof: by FINITE_BIJ_COUNT_CARD, BIJ_SYM *)
Theorem bij_eq_count:
  !s. FINITE s ==> s =b= (count (CARD s))
Proof
  metis_tac[FINITE_BIJ_COUNT_CARD, BIJ_SYM]
QED

(* Theorem: s =b= t /\ (FINITE s \/ FINITE t) ==> CARD s = CARD t *)
(* Proof: by FINITE_BIJ_CARD, BIJ_SYM. *)
Theorem bij_eq_card:
  !s t. s =b= t /\ (FINITE s \/ FINITE t) ==> CARD s = CARD t
Proof
  metis_tac[FINITE_BIJ_CARD, BIJ_SYM]
QED

(* Theorem: FINITE s /\ FINITE t ==> (s =b= t <=> CARD s = CARD t) *)
(* Proof:
   If part: s =b= t ==> CARD s = CARD t
      This is true                 by FINITE_BIJ_CARD
   Only-if part: CARD s = CARD t ==> s =b= t
      Let n = CARD s = CARD t.
      Note ?f. BIJ f s (count n)   by bij_eq_count
       and ?g. BIJ g (count n) t   by FINITE_BIJ_COUNT_CARD
      Thus s =b= t                 by bij_eq_trans
*)
Theorem bij_eq_card_eq:
  !s t. FINITE s /\ FINITE t ==> (s =b= t <=> CARD s = CARD t)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[FINITE_BIJ_CARD] >>
  `?f. BIJ f s (count (CARD s))` by rw[bij_eq_count] >>
  `?g. BIJ g (count (CARD t)) t` by rw[FINITE_BIJ_COUNT_CARD] >>
  metis_tac[bij_eq_trans]
QED

(* ------------------------------------------------------------------------- *)
(* Alternate characterisation of maps.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: SURJ f s t <=>
            over f s t /\ (!y. y IN t ==> preimage f s y <> {}) *)
(* Proof:
   Let P = over f s t,
       Q = !y. y IN t ==> preimage f s y <> {}.
   If part: SURJ f s t ==> P /\ Q
      P is true                by SURJ_DEF
      Q is true                by preimage_def, SURJ_DEF
   Only-if part: P /\ Q ==> SURJ f s t
      This is true             by preimage_def, SURJ_DEF
*)
Theorem surj_preimage_not_empty:
  !f s t. SURJ f s t <=>
          over f s t /\ (!y. y IN t ==> preimage f s y <> {})
Proof
  rw[SURJ_DEF, preimage_def, EXTENSION] >>
  metis_tac[]
QED

(* Theorem: INJ f s t <=>
            over f s t /\
            (!y. y IN t ==> (preimage f s y = {} \/
                             SING (preimage f s y))) *)
(* Proof:
   Let P = over f s t,
       Q = !y. y IN t ==> preimage f s y = {} \/ SING (preimage f s y).
   If part: INJ f s t ==> P /\ Q
      P is true                          by INJ_DEF
      For Q, if preimage f s y <> {},
      Then ?x. x IN preimage f s y       by MEMBER_NOT_EMPTY
        or ?x. x IN s /\ f x = y         by in_preimage
      Thus !z. z IN preimage f s y ==> z = x
                                         by in_preimage, INJ_DEF
        or SING (preimage f s y)         by SING_DEF, EXTENSION
   Only-if part: P /\ Q ==> INJ f s t
      By INJ_DEF, this is to show:
         !x y. x IN s /\ y IN s /\ f x = f y ==> x = y
      Let z = f x, then z IN t           by over f s t
        so x IN preimage f s z           by in_preimage
       and y IN preimage f s z           by in_preimage
      Thus preimage f s z <> {}          by MEMBER_NOT_EMPTY
        so SING (preimage f s z)         by implication
       ==> x = y                         by SING_ELEMENT
*)
Theorem inj_preimage_empty_or_sing:
  !f s t. INJ f s t <=>
          over f s t /\
          (!y. y IN t ==> (preimage f s y = {} \/
                           SING (preimage f s y)))
Proof
  rw[EQ_IMP_THM] >-
  fs[INJ_DEF] >-
 ((Cases_on `preimage f s y = {}` >> simp[]) >>
  `?x. x IN s /\ f x = y` by metis_tac[in_preimage, MEMBER_NOT_EMPTY] >>
  simp[SING_DEF] >>
  qexists_tac `x` >>
  rw[preimage_def, EXTENSION] >>
  metis_tac[INJ_DEF]) >>
  rw[INJ_DEF] >>
  qabbrev_tac `z = f x` >>
  `z IN t` by fs[Abbr`z`] >>
  `x IN preimage f s z` by fs[preimage_def] >>
  `y IN preimage f s z` by fs[preimage_def] >>
  metis_tac[MEMBER_NOT_EMPTY, SING_ELEMENT]
QED

(* Theorem: BIJ f s t <=>
           over f s t /\
           (!y. y IN t ==> SING (preimage f s y)) *)
(* Proof:
   Let P = over f s t,
       Q = !y. y IN t ==> SING (preimage f s y).
   If part: BIJ f s t ==> P /\ Q
      P is true                          by BIJ_DEF, INJ_DEF
      For Q,
      Note INJ f s t /\ SURJ f s t       by BIJ_DEF
        so preimage f s y <> {}          by surj_preimage_not_empty
      Thus SING (preimage f s y)         by inj_preimage_empty_or_sing
   Only-if part: P /\ Q ==> BIJ f s t
      Note !y. y IN t ==> (preimage f s y) <> {}
                                         by SING_DEF, NOT_EMPTY_SING
        so SURJ f s t                    by surj_preimage_not_empty
       and INJ f s t                     by inj_preimage_empty_or_sing
      Thus BIJ f s t                     by BIJ_DEF
*)
Theorem bij_preimage_sing:
  !f s t. BIJ f s t <=>
          over f s t /\
          (!y. y IN t ==> SING (preimage f s y))
Proof
  rw[EQ_IMP_THM] >-
  fs[BIJ_DEF, INJ_DEF] >-
  metis_tac[BIJ_DEF, surj_preimage_not_empty, inj_preimage_empty_or_sing] >>
  `INJ f s t` by metis_tac[inj_preimage_empty_or_sing] >>
  `SURJ f s t` by metis_tac[SING_DEF, NOT_EMPTY_SING, surj_preimage_not_empty] >>
  simp[BIJ_DEF]
QED

(* Theorem: FINITE s /\ over f s t ==>
            (SURJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <> 0) *)
(* Proof:
   Note !y. FINITE (preimage f s y)      by preimage_finite
    and !y. CARD (preimage f s y) = 0 <=> preimage f s y = {}
                                         by CARD_EQ_0
   The result follows                    by surj_preimage_not_empty
*)
Theorem surj_iff_preimage_card_not_0:
  !f s t. FINITE s /\ over f s t ==>
          (SURJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <> 0)
Proof
  metis_tac[surj_preimage_not_empty, preimage_finite, CARD_EQ_0]
QED

(* Theorem: FINITE s /\ over f s t ==>
            (INJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <= 1) *)
(* Proof:
   Note !y. FINITE (preimage f s y)      by preimage_finite
    and !y. CARD (preimage f s y) = 0 <=> preimage f s y = {}
                                         by CARD_EQ_0
    and !y. CARD (preimage f s y) = 1 <=> SING (preimage f s y)
                                         by CARD_EQ_1
   The result follows                    by inj_preimage_empty_or_sing, LE_ONE
*)
Theorem inj_iff_preimage_card_le_1:
  !f s t. FINITE s /\ over f s t ==>
          (INJ f s t <=> !y. y IN t ==> CARD (preimage f s y) <= 1)
Proof
  metis_tac[inj_preimage_empty_or_sing, preimage_finite, CARD_EQ_0, CARD_EQ_1, LE_ONE]
QED

(* Theorem: FINITE s /\ over f s t ==>
            (BIJ f s t <=> !y. y IN t ==> CARD (preimage f s y) = 1) *)
(* Proof:
   Note !y. FINITE (preimage f s y)      by preimage_finite
    and !y. CARD (preimage f s y) = 1 <=> SING (preimage f s y)
                                         by CARD_EQ_1
   The result follows                    by bij_preimage_sing
*)
Theorem bij_iff_preimage_card_eq_1:
  !f s t. FINITE s /\ over f s t ==>
          (BIJ f s t <=> !y. y IN t ==> CARD (preimage f s y) = 1)
Proof
  metis_tac[bij_preimage_sing, preimage_finite, CARD_EQ_1]
QED

(* Theorem: FINITE s /\ SURJ f s t ==>
            (INJ f s t <=> !e. e IN IMAGE (preimage f s) t ==> CARD e = 1) *)
(* Proof:
   If part: INJ f s t /\ x IN t ==> CARD (preimage f s x) = 1
      Note BIJ f s t                     by BIJ_DEF
       and over f s t                    by BIJ_DEF, INJ_DEF
        so CARD (preimage f s x) = 1     by bij_iff_preimage_card_eq_1
   Only-if part: !e. (?x. e = preimage f s x /\ x IN t) ==> CARD e = 1 ==> INJ f s t
      Note over f s t                                  by SURJ_DEF
       and !x. x IN t ==> ?y. y IN s /\ f y = x        by SURJ_DEF
      Thus !y. y IN t ==> CARD (preimage f s y) = 1    by IN_IMAGE
        so INJ f s t                                   by inj_iff_preimage_card_le_1
*)
Theorem finite_surj_inj_iff:
  !f s t. FINITE s /\ SURJ f s t ==>
      (INJ f s t <=> !e. e IN IMAGE (preimage f s) t ==> CARD e = 1)
Proof
  rw[EQ_IMP_THM] >-
  prove_tac[BIJ_DEF, INJ_DEF, bij_iff_preimage_card_eq_1] >>
  fs[SURJ_DEF] >>
  `!y. y IN t ==> CARD (preimage f s y) = 1` by metis_tac[] >>
  rw[inj_iff_preimage_card_le_1]
QED



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
