open HolKernel boolLib bossLib BasicProvers;
open optionTheory pairTheory stringTheory;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open comparisonTheory;

val _ = new_theory "balanced_map";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(* ------------------------ Preliminaries ------------------------ *)

val _ = numLib.temp_prefer_num();

Triviality list_rel_lem1:
  !f l l'.
  ~LIST_REL f l l'
  ⇒
  ∃n. n ≤ LENGTH l ∧ n ≤ LENGTH l' ∧ LIST_REL f (TAKE n l) (TAKE n l') ∧
    ((n = LENGTH l ∧ n ≠ LENGTH l') ∨
     (n ≠ LENGTH l ∧ n = LENGTH l') ∨
     (n ≠ LENGTH l ∧ n ≠ LENGTH l' ∧ ~f (EL n l) (EL n l')))
Proof
 Induct_on ‘l’ >> simp[] >> Cases_on‘l'’ >> rw[]
 >- (qexists_tac ‘0’ >> simp[]) >>
 rename [‘¬P (EL _ (h1::l1)) (EL _ (h2 :: l2))’] >>
 reverse (Cases_on ‘P h1 h2’)
 >- (qexists_tac ‘0’ >> simp[]) >>
 first_x_assum (drule_then (qx_choose_then ‘m’ strip_assume_tac)) >>
 (* 3 cases *)
 qexists_tac ‘SUC m’ >> simp[] >> rw[] >> fs[]
QED

val _ = augment_srw_ss [rewrites [listTheory.TAKE_def]]
Triviality list_rel_lem2:
 !l l'.
  LIST_REL f l l'
  ⇒
  ¬∃n. n ≤ LENGTH l ∧ n ≤ LENGTH l' ∧ LIST_REL f (TAKE n l) (TAKE n l') ∧
    ((n = LENGTH l ∧ n ≠ LENGTH l') ∨
     (n ≠ LENGTH l ∧ n = LENGTH l') ∨
     (n ≠ LENGTH l ∧ n ≠ LENGTH l' ∧ ~f (EL n l) (EL n l')))
Proof
 ho_match_mp_tac LIST_REL_ind >>
 srw_tac[] [] >>
 CCONTR_TAC >>
 full_simp_tac (srw_ss()) [] >>
 EVERY_CASE_TAC >>
 full_simp_tac (srw_ss()) [] >>
 srw_tac[] []
 >- (first_x_assum (qspecl_then [`LENGTH l`] mp_tac) >>
     srw_tac[] [])
 >- (first_x_assum (qspecl_then [`LENGTH l'`] mp_tac) >>
     srw_tac[] [])
 >- (first_x_assum (qspecl_then [`n-1`] mp_tac) >>
     srw_tac[] [] >>
     fs[] >>
     full_simp_tac (srw_ss()) [LIST_REL_EL_EQN] >>
     `n - 1 ≤ LENGTH l ∧ n - 1 ≤ LENGTH l'` by decide_tac >>
     `n ≤ LENGTH l ∧ n ≤ LENGTH l'` by decide_tac >>
     full_simp_tac (srw_ss()) [LENGTH_TAKE, rich_listTheory.EL_TAKE] >>
     srw_tac[] [] >>
     `0 < n` by decide_tac >>
     full_simp_tac (srw_ss()++ARITH_ss) [rich_listTheory.EL_CONS] >>
     `PRE n = n - 1` by decide_tac >>
     full_simp_tac (srw_ss()) [])
QED

Triviality list_rel_thm0:
 !f l l'.
  LIST_REL f l l' ⇔
  !n.
    ¬(n ≤ LENGTH l) ∨ ¬(n ≤ LENGTH l') ∨ ¬LIST_REL f (TAKE n l) (TAKE n l') ∨
    (n ≠ LENGTH l ∨ n = LENGTH l') ∧
    (n = LENGTH l ∨ n ≠ LENGTH l') ∧
    (n = LENGTH l ∨ n = LENGTH l' ∨ f (EL n l) (EL n l'))
Proof
 rw [] >>
 eq_tac >>
 rw [] >>
 imp_res_tac list_rel_lem2 >>
 fs [] >>
 metis_tac [list_rel_lem1]
QED

Triviality list_rel_thm:
 !f l l'.
  LIST_REL f l l' ⇔
  !n.
    n ≤ LENGTH l ∧ n ≤ LENGTH l' ∧ LIST_REL f (TAKE n l) (TAKE n l') ∧
    (n ≠ LENGTH l ∨ n ≠ LENGTH l') ⇒
    (n ≠ LENGTH l ∧ n ≠ LENGTH l' ∧ f (EL n l) (EL n l'))
Proof metis_tac [list_rel_thm0]
QED

val _ = bossLib.augment_srw_ss [rewrites
  [FUNION_FUPDATE_1,FUNION_ASSOC,FUNION_FEMPTY_2,FUNION_FEMPTY_1,FDOM_DRESTRICT,
   DRESTRICT_UNIV]]

fun fs x = full_simp_tac (srw_ss()++ARITH_ss) x;
fun rfs x = REV_FULL_SIMP_TAC (srw_ss()++ARITH_ss) x;
val rw = srw_tac [ARITH_ss];

val fmrw = srw_tac [ARITH_ss, rewrites [FLOOKUP_UPDATE,FLOOKUP_FUNION,FLOOKUP_DRESTRICT,
                    FUNION_FUPDATE_2,FAPPLY_FUPDATE_THM,FUNION_DEF, DRESTRICT_DEF]];

fun inv_to_front_tac tm (g as (asl,w)) = let
  val tms = strip_conj w
  val (tms1,tms2) = List.partition (fn x => can (find_term (can (match_term tm))) x) tms
  val tms = tms1@tms2
  val thm = prove (``^w ⇔ ^(list_mk_conj tms)``, SIMP_TAC (std_ss) [AC CONJ_COMM CONJ_ASSOC])
in
  ONCE_REWRITE_TAC [thm] g
end

val inv_mp_tac = let
  val lemma = PROVE [] ``!A B C D. (A ⇒ B ∧ C) ⇒ (A ∧ (B ∧ C ⇒  D)) ⇒ (B ∧ D)``
in
  fn th => fn (g as (asl,w)) => let
    val c = th |> concl
    val (xs,b) = strip_forall c
    val tm = b |> dest_imp |> snd |> strip_conj |> hd
    val tm2 = hd (strip_conj w)
    val s = fst (match_term tm tm2)
    val th2 = SPECL (map (Term.subst s) xs) th
    val th3 = MATCH_MP lemma th2
  in
    MATCH_MP_TAC (GEN_ALL th3) g
  end
end

val fdom_eq = PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``;

Triviality TIMES_MIN: !x y z. x * MIN y z = MIN (x * y) (x * z)
Proof rw [MIN_DEF] >> fs []
QED

Triviality FCARD_DISJOINT_UNION:
  !m1 m2.
    DISJOINT (FDOM m1) (FDOM m2) ∨ DISJOINT (FDOM m2) (FDOM m1)
  ⇒
    FCARD (FUNION m1 m2) = FCARD m1 + FCARD m2
Proof
 rw [DISJOINT_DEF, FCARD_DEF] >>
 metis_tac [CARD_UNION, FDOM_FINITE, CARD_DEF, ADD_0, INTER_COMM]
QED

Triviality CARD_DISJOINT_UNION:
  !s1 s2.
    FINITE s1 ∧ FINITE s2
  ⇒
    DISJOINT s1 s2 ∨ DISJOINT s2 s1
  ⇒
    CARD (s1 ∪ s2) = CARD s1 + CARD s2
Proof
 rw [DISJOINT_DEF] >>
 metis_tac [CARD_UNION, CARD_DEF, ADD_0, INTER_COMM]
QED

Triviality FCARD_DRESTRICT:
  ∀m s. FCARD (DRESTRICT m s) = CARD (FDOM m ∩ s)
Proof rw [FCARD_DEF, FDOM_DRESTRICT]
QED

Triviality DELETE_INTER2:
  ∀s t x. t ∩ (s DELETE x) = s ∩ t DELETE x
Proof
 metis_tac [DELETE_INTER, INTER_COMM]
QED

Triviality POS_CARD_HAS_MEM:
  !s. FINITE s ⇒ 0 < CARD s ⇒ ?x. x ∈ s
Proof
 Cases_on `s` >> rw [CARD_INSERT] >> metis_tac []
QED

Definition all_distinct_up_to_def:
(all_distinct_up_to cmp [] ⇔ T) ∧
(all_distinct_up_to cmp (k::t) ⇔
  (∀k'. cmp k k' = Equal ⇒ ~MEM k' t) ∧ all_distinct_up_to cmp t)
End

val every_case_tac = BasicProvers.EVERY_CASE_TAC;

(* ----------------------------------------------------------------------
    Finite maps up to key equivalence
   ---------------------------------------------------------------------- *)

Definition key_set_def:
  key_set cmp k = { k' | cmp k k' = Equal }
End

Theorem key_set_equiv:
 !cmp.
  good_cmp cmp
  ⇒
  (!k. k ∈ key_set cmp k) ∧
  (!k1 k2. k1 ∈ key_set cmp k2 ⇒ k2 ∈ key_set cmp k1) ∧
  (!k1 k2 k3. k1 ∈ key_set cmp k2 ∧ k2 ∈ key_set cmp k3 ⇒ k1 ∈ key_set cmp k3)
Proof rw [key_set_def] >> metis_tac [good_cmp_def]
QED

Theorem key_set_partition:
  !cmp k1 k2.
    good_cmp cmp ∧
    key_set cmp k1 ≠ key_set cmp k2
  ⇒
    DISJOINT (key_set cmp k1) (key_set cmp k2)
Proof
   rw [DISJOINT_DEF, EXTENSION] >> metis_tac [key_set_equiv]
QED

Theorem key_set_eq:
 !cmp k1 k2.
    good_cmp cmp
  ⇒
    (key_set cmp k1 = key_set cmp k2 ⇔ cmp k1 k2 = Equal)
Proof
 rw [key_set_def, EXTENSION] >>
 metis_tac [cmp_thms, key_set_equiv]
QED

Definition key_set_cmp_def:
  key_set_cmp cmp k ks res ⇔ ∀k'. k' ∈ ks ⇒ cmp k k' = res
End

Theorem key_set_cmp_thm:
  !cmp k k' res.
    good_cmp cmp
  ⇒
    (key_set_cmp cmp k (key_set cmp k') res ⇔ cmp k k' = res)
Proof
 rw [key_set_cmp_def, key_set_def] >> metis_tac [cmp_thms]
QED

Definition key_set_cmp2_def:
  key_set_cmp2 cmp ks1 ks2 res ⇔
    ∀k1 k2. k1 ∈ ks1 ∧ k2 ∈ ks2 ⇒ cmp k1 k2 = res
End

Theorem key_set_cmp2_thm:
  !cmp k k' res.
    good_cmp cmp
  ⇒
    (key_set_cmp2 cmp (key_set cmp k) (key_set cmp k') res ⇔ cmp k k' = res)
Proof
 rw [key_set_cmp2_def, key_set_def] >> metis_tac [cmp_thms]
QED

(* Maps based on balanced binary trees. Copied from ghc-7.8.3
 * libraries/containers/Data/Map/Base.hs. It starts with the following comment:

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Map.Base
-- Copyright   :  (c) Daan Leijen 2002
--                (c) Andriy Palamarchuk 2008
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- An efficient implementation of maps from keys to values (dictionaries).
--
-- Since many function names (but not the type name) clash with
-- "Prelude" names, this module is usually imported @qualified@, e.g.
--
-- >  import Data.Map (Map)
-- >  import qualified Data.Map as Map
--
-- The implementation of 'Map' is based on /size balanced/ binary trees (or
-- trees of /bounded balance/) as described by:
--
--    * Stephen Adams, \"/Efficient sets: a balancing act/\",
--     Journal of Functional Programming 3(4):553-562, October 1993,
--     <http://www.swiss.ai.mit.edu/~adams/BB/>.
--
--    * J. Nievergelt and E.M. Reingold,
--      \"/Binary search trees of bounded balance/\",
--      SIAM journal of computing 2(1), March 1973.
--
-- Note that the implementation is /left-biased/ -- the elements of a
-- first argument are always preferred to the second, for example in
-- 'union' or 'insert'.
--
-- Operation comments contain the operation time complexity in
-- the Big-O notation <http://en.wikipedia.org/wiki/Big_O_notation>.
-----------------------------------------------------------------------------

*)

Datatype:
  balanced_map = Tip | Bin num 'k 'v balanced_map balanced_map
End

Definition ratio_def: ratio = 2:num
End

Definition delta_def: delta = 3:num
End

Definition size_def:
  size Tip = 0 ∧
  size (Bin s k v l r) = s
End

Definition bin_def:
  bin k x l r = Bin (size l + size r + 1) k x l r
End

Definition null_def:
  null Tip = T ∧
  null (Bin s k v m1 m2) = F
End

Definition lookup_def:
  lookup cmp k Tip = NONE ∧
  lookup cmp k (Bin s k' v l r) =
    case cmp k k' of
       | Less => lookup cmp k l
       | Greater => lookup cmp k r
       | Equal => SOME v
End

Definition member_def:
  member cmp k Tip = F ∧
  member cmp k (Bin s k' v l r) =
    case cmp k k' of
       | Less => member cmp k l
       | Greater => member cmp k r
       | Equal => T
End

Definition empty_def: empty = Tip
End

Definition singleton_def: singleton k x = Bin 1 k x Tip Tip
End

(* Just like the Haskell, but w/o @ patterns *)
Definition balanceL'_def:
balanceL' k x l r =
  case r of
     | Tip =>
         (case l of
            | Tip => Bin 1 k x Tip Tip
            | (Bin _ _ _ Tip Tip) => Bin 2 k x l Tip
            | (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) =>
                 Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
            | (Bin _ lk lx (Bin s' k' v' l' r') Tip) =>
                 Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)
            | (Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl lrr)) =>
                if lrs < ratio*lls then
                  Bin (1+ls) lk lx
                      (Bin lls k' v' l' r')
                      (Bin (1+lrs) k x (Bin lrs lrk lrx lrl lrr) Tip)
                else
                  Bin (1+ls) lrk lrx
                      (Bin (1+lls+size lrl) lk lx (Bin lls k' v' l' r') lrl)
                      (Bin (1+size lrr) k x lrr Tip))
     | (Bin rs _ _ _ _) =>
         case l of
            | Tip => Bin (1+rs) k x Tip r
            | (Bin ls lk lx ll lr) =>
                if ls > delta*rs  then
                  case (ll, lr) of
                    | (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr) =>
                         if lrs < ratio*lls then
                           Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                         else
                           Bin (1+ls+rs) lrk lrx
                               (Bin (1+lls+size lrl) lk lx ll lrl)
                               (Bin (1+rs+size lrr) k x lrr r)
                     | (_, _) => Tip (* error "Failure in Data.Map.balanceL" *)
                else Bin (1+ls+rs) k x l r
End

val balanceR'_def = Define `
balanceR' k x l r =
  case l of
    | Tip =>
        (case r of
           | Tip => Bin 1 k x Tip Tip
           | (Bin _ _ _ Tip Tip) => Bin 2 k x Tip r
           | (Bin _ rk rx Tip (Bin s' k' v' l' r')) => Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')
           | (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) => Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
           | (Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v' l' r')) =>
               if rls < ratio*rrs then Bin (1+rs) rk rx (Bin (1+rls) k x Tip (Bin rls rlk rlx rll rlr)) (Bin rrs k' v' l' r')
               else Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr (Bin rrs k' v' l' r')))
   | (Bin ls _ _ _ _) =>
       case r of
          | Tip => Bin (1+ls) k x l Tip
          | (Bin rs rk rx rl rr) =>
              if rs > delta*ls then
                case (rl, rr) of
                   | (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _) =>
                     if  rls < ratio*rrs then Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                     else Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                   | (_, _) => Tip (* error "Failure in Data.Map.balanceR" *)
              else Bin (1+ls+rs) k x l r`;

val balanceL_def = Define `
(balanceL k x Tip Tip =
  Bin 1 k x Tip Tip) ∧
(balanceL k x (Bin s' k' v' Tip Tip) Tip =
  Bin 2 k x (Bin s' k' v' Tip Tip) Tip) ∧
(balanceL k x (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) Tip =
  Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)) ∧
(balanceL k x  (Bin _ lk lx (Bin s' k' v' l' r') Tip) Tip =
  Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)) ∧
(balanceL k x (Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl lrr)) Tip =
  if lrs < ratio*lls then
    Bin (1+ls) lk lx (Bin lls k' v' l' r')
                     (Bin (1+lrs) k x (Bin lrs lrk lrx lrl lrr) Tip)
  else
    Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx (Bin lls k' v' l' r') lrl)
                       (Bin (1+size lrr) k x lrr Tip)) ∧
(balanceL k x Tip (Bin rs k' v' l' r') =
  Bin (1+rs) k x Tip (Bin rs k' v' l' r')) ∧
(balanceL k x (Bin ls lk lx ll lr) (Bin rs k' v' l' r') =
  if ls > delta*rs  then
    case (ll, lr) of
       | (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr) =>
           if lrs < ratio*lls then
             Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr (Bin rs k' v' l' r'))
           else
             Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl)
                                   (Bin (1+rs+size lrr) k x lrr (Bin rs k' v' l' r'))
       | (_, _) => Tip (* error "Failure in Data.Map.balanceL" *)
  else
    Bin (1+ls+rs) k x (Bin ls lk lx ll lr) (Bin rs k' v' l' r'))`;

val balanceR_def = Define `
(balanceR k x Tip Tip =
  Bin 1 k x Tip Tip) ∧
(balanceR k x Tip (Bin s' k' v' Tip Tip) =
  Bin 2 k x Tip (Bin s' k' v' Tip Tip)) ∧
(balanceR k x Tip (Bin _ rk rx Tip (Bin s' k' v' l' r')) =
  Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')) ∧
(balanceR k x Tip (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) =
  Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)) ∧
(balanceR k x Tip (Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v' l' r')) =
  if rls < ratio*rrs then
    Bin (1+rs) rk rx (Bin (1+rls) k x Tip (Bin rls rlk rlx rll rlr)) (Bin rrs k' v' l' r')
  else
    Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll)
                       (Bin (1+rrs+size rlr) rk rx rlr (Bin rrs k' v' l' r'))) ∧
(balanceR k x (Bin ls k' v' l' r') Tip =
  Bin (1+ls) k x (Bin ls k' v' l' r') Tip) ∧
(balanceR k x (Bin ls k' v' l' r') (Bin rs rk rx rl rr) =
  if rs > delta*ls then
    case (rl, rr) of
       | (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _) =>
           if rls < ratio*rrs then
             Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x (Bin ls k' v' l' r') rl) rr
           else
             Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x (Bin ls k' v' l' r') rll)
                                   (Bin (1+rrs+size rlr) rk rx rlr rr)
       | (_, _) => Tip (* error "Failure in Data.Map.balanceR" *)
  else
    Bin (1+ls+rs) k x (Bin ls k' v' l' r') (Bin rs rk rx rl rr))`;

val insert_def = Define `
(insert cmp k v Tip = singleton k v) ∧
(insert cmp k v (Bin s k' v' l r) =
  case cmp k k' of
     | Less => balanceL k' v' (insert cmp k v l) r
     | Greater => balanceR k' v' l (insert cmp k v r)
     | Equal => Bin s k v l r)`;

val insertR_def = Define `
(insertR cmp k v Tip = singleton k v) ∧
(insertR cmp k v (Bin s k' v' l r) =
  case cmp k k' of
     | Less => balanceL k' v' (insertR cmp k v l) r
     | Greater => balanceR k' v' l (insertR cmp k v r)
     | Equal => Bin s k' v' l r)`;

val insertMax_def = Define `
(insertMax k v Tip = singleton k v) ∧
(insertMax k v (Bin s k' v' l r) = balanceR k' v' l (insertMax k v r))`;

val insertMin_def = Define `
(insertMin k v Tip = singleton k v) ∧
(insertMin k v (Bin s k' v' l r) = balanceL k' v' (insertMin k v l) r)`;

val deleteFindMax_def = Define `
(deleteFindMax (Bin s k x l Tip) = ((k,x),l)) ∧
(deleteFindMax (Bin s k x l r) =
  let (km,r') = deleteFindMax r in
    (km,balanceL k x l r')) ∧
(deleteFindMax Tip =
  (ARB,Tip))`; (*(error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)*)

val deleteFindMin_def = Define `
(deleteFindMin (Bin s k x Tip r) = ((k,x),r)) ∧
(deleteFindMin (Bin s k x l r) =
  let (km,l') = deleteFindMin l in
    (km,balanceR k x l' r)) ∧
(deleteFindMin Tip =
  (ARB,Tip))`; (*(error "Map.deleteFindMin: can not return the maximal element of an empty map", Tip)*)

val glue_def = Define `
(glue Tip r = r) ∧
(glue l Tip = l) ∧
(glue l r =
  if size l > size r then
    let ((km,m),l') = deleteFindMax l in
      balanceR km m l' r
  else
    let ((km,m),r') = deleteFindMin r in
      balanceL km m l r')`;

val delete_def = Define `
(delete cmp k Tip = Tip) ∧
(delete cmp k (Bin s k' v l r) =
  case cmp k k' of
     | Less => balanceR k' v (delete cmp k l) r
     | Greater => balanceL k' v l (delete cmp k r)
     | Eq => glue l r)`;

val trim_help_greater_def = Define `
(trim_help_greater cmp lo (Bin s' k v' l' r) =
  if cmp k lo = Less ∨ cmp k lo = Equal then
    trim_help_greater cmp lo r
  else
    Bin s' k v' l' r) ∧
(trim_help_greater cmp lo Tip = Tip)`;

val trim_help_lesser_def = Define `
(trim_help_lesser cmp hi (Bin s' k v' l r') =
  if cmp k hi = Greater ∨ cmp k hi = Equal then
    trim_help_lesser cmp hi l
  else
    Bin s' k v' l r') ∧
(trim_help_lesser cmp lo Tip = Tip)`;

val trim_help_middle_def = Define `
(trim_help_middle cmp lo hi (Bin s' k v' l r) =
  if cmp k lo = Less ∨ cmp k lo = Equal then
    trim_help_middle cmp lo hi r
  else if cmp k hi = Greater ∨ cmp k hi = Equal then
    trim_help_middle cmp lo hi l
  else
    Bin s' k v' l r) ∧
(trim_help_middle lo cmp hi Tip = Tip)`;

val trim_def = Define `
(trim cmp NONE NONE t = t) ∧
(trim cmp (SOME lk) NONE t = trim_help_greater cmp lk t) ∧
(trim cmp NONE (SOME hk) t = trim_help_lesser cmp hk t) ∧
(trim cmp (SOME lk) (SOME hk) t = trim_help_middle cmp lk hk t)`;

val link_def = Define `
(link k v Tip r = insertMin k v r) ∧
(link k v l Tip = insertMax k v l) ∧
(link k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz) =
  if delta*sizeL < sizeR then
    balanceL kz z (link k v (Bin sizeL ky y ly ry) lz) rz
  else if delta*sizeR < sizeL then
    balanceR ky y ly (link k v ry (Bin sizeR kz z lz rz))
  else
    bin k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz))`;

(* From the Haskell implementation:
 * [link2 l r] merges two trees.
 *)

Definition link2_def:
  (link2 l Tip = l) ∧
  (link2 Tip r = r) ∧
  (link2 (Bin sizeL kx x lx rx) (Bin sizeR ky y ly ry) =
    if delta*sizeL < sizeR then
      balanceL ky y (link2 (Bin sizeL kx x lx rx) ly) ry
    else if delta*sizeR < sizeL then
      balanceR kx x lx (link2 rx (Bin sizeR ky y ly ry))
    else
       glue (Bin sizeL kx x lx rx) (Bin sizeR ky y ly ry))
End

val filterLt_help_def = Define `
(filterLt_help cmp b Tip = Tip) ∧
(filterLt_help cmp b' (Bin s kx x l r) =
  case cmp kx b' of
     | Less => link kx x l (filterLt_help cmp b' r)
     | Equal => l
     | Greater => filterLt_help cmp b' l)`;

val filterLt_def = Define `
(filterLt cmp NONE t = t) ∧
(filterLt cmp (SOME b) t = filterLt_help cmp b t)`;

val filterGt_help_def = Define `
(filterGt_help cmp b Tip = Tip) ∧
(filterGt_help cmp b' (Bin s kx x l r) =
  case cmp b' kx of
     | Less => link kx x (filterGt_help cmp b' l) r
     | Equal => r
     | Greater => filterGt_help cmp b' r)`;

val filterGt_def = Define `
(filterGt cmp NONE t = t) ∧
(filterGt cmp (SOME b) t = filterGt_help cmp b t)`;

val hedgeUnion_def = Define `
(hedgeUnion cmp blo bhi t1 Tip = t1) ∧
(hedgeUnion cmp blo bhi Tip (Bin _ kx x l r) =
  link kx x (filterGt cmp blo l) (filterLt cmp bhi r)) ∧
(hedgeUnion cmp blo bhi t1 (Bin _ kx x Tip Tip) = insertR cmp kx x t1) ∧
(hedgeUnion cmp blo bhi (Bin s kx x l r) t2 =
  link kx x (hedgeUnion cmp blo (SOME kx) l (trim cmp blo (SOME kx) t2))
            (hedgeUnion cmp (SOME kx) bhi r (trim cmp (SOME kx) bhi t2)))`;

val union_def = Define `
(union cmp Tip t2 = t2) ∧
(union cmp t1 Tip = t1) ∧
(union cmp t1 t2 = hedgeUnion cmp NONE NONE t1 t2)`;

Definition hedgeUnionWithKey_def:
  (hedgeUnionWithKey _ _ _ _ t1 Tip = t1) ∧
  (hedgeUnionWithKey cmp _ blo bhi Tip (Bin _ kx x l r) =
    link kx x (filterGt cmp blo l) (filterLt cmp bhi r)) ∧
  (hedgeUnionWithKey cmp f blo bhi (Bin _ kx x l r) t2 =
    let newx = (case lookup cmp kx t2 of NONE => x | SOME y => f kx x y) in
    link kx newx
      (hedgeUnionWithKey cmp f blo (SOME kx) l (trim cmp blo (SOME kx) t2))
      (hedgeUnionWithKey cmp f (SOME kx) bhi r (trim cmp (SOME kx) bhi t2)))
End

Definition unionWithKey_def:
  (unionWithKey _ _ Tip t2 = t2) ∧
  (unionWithKey _ _ t1 Tip = t1) ∧
  (unionWithKey cmp f t1 t2 =
    hedgeUnionWithKey cmp f NONE NONE t1 t2)
End

Definition unionWith_def:
  unionWith cmp f t1 t2 = unionWithKey cmp (λk x y. f x y) t1 t2
End

Definition filterWithKey_def:
  filterWithKey f Tip = Tip ∧
  filterWithKey f (Bin s kx x l r) =
    let l' = filterWithKey f l in
    let r' = filterWithKey f r in
      if f kx x then link kx x l' r' else link2 l' r'
End

Definition filter_def:
  filter f t = filterWithKey (λk x. f x) t
End

val foldrWithKey_def = Define `
(foldrWithKey f z' Tip = z') ∧
(foldrWithKey f z' (Bin _ kx x l r) =
  foldrWithKey f (f kx x (foldrWithKey f z' r)) l)`;

val toAscList_def = Define `
toAscList t = foldrWithKey (\k x xs. (k,x)::xs) [] t`;

val compare_def = Define `
compare cmp1 cmp2 t1 t2 = list_cmp (pair_cmp cmp1 cmp2) (toAscList t1) (toAscList t2)`;

Definition mapWithKey_def:
  (mapWithKey f Tip = Tip) ∧
  (mapWithKey f (Bin sx kx x l r) =
     Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r))
End

Definition map_def:
  map f t = mapWithKey (λk x. f x) t
End

val splitLookup_def = Define `
(splitLookup cmp k Tip = (Tip,NONE,Tip)) ∧
(splitLookup cmp k (Bin _ kx x l r) =
  case cmp k kx of
     | Less =>
         let (lt,z,gt) = splitLookup cmp k l in
         let gt' = link kx x gt r in
           (lt,z,gt')
     | Greater =>
         let (lt,z,gt) = splitLookup cmp k r in
         let lt' = link kx x l lt in
           (lt',z,gt)
     | Equal =>
         (l,SOME x,r))`;

val submap'_def = Define `
(submap' cmp _ Tip _ = T) ∧
(submap' cmp _ _ Tip = F) ∧
(submap' cmp f (Bin _ kx x l r) t =
  case splitLookup cmp kx t of
     | (lt,NONE,gt) => F
     | (lt,SOME y,gt) => f x y ∧ submap' cmp f l lt ∧ submap' cmp f r gt)`;

val isSubmapOfBy_def = Define `
isSubmapOfBy cmp f t1 t2 ⇔ size t1 ≤ size t2 ∧ submap' cmp f t1 t2`;

val isSubmapOf_def = Define `
isSubmapOf cmp t1 t2 ⇔ isSubmapOfBy cmp (=) t1 t2`;

(* TODO: The ghc implementation is more complex and efficient *)
val fromList_def = Define `
fromList cmp l = FOLDR (λ(k,v) t. insert cmp k v t) empty l`;

(* ----------------------- proofs ------------------------ *)

val balanceL_ind = fetch "-" "balanceL_ind";
val balanceR_ind = fetch "-" "balanceR_ind";

Triviality balanceL'_thm: !k v l r. balanceL k v l r = balanceL' k v l r
Proof
 ho_match_mp_tac balanceL_ind >> rw [balanceL_def, balanceL'_def]
QED

Triviality balanceR'_thm: !k v l r. balanceR k v l r = balanceR' k v l r
Proof
  ho_match_mp_tac balanceR_ind >> rw [balanceR_def, balanceR'_def]
QED

Definition to_fmap_def:
  to_fmap cmp Tip = FEMPTY ∧
  to_fmap cmp (Bin s k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)
End

Theorem to_fmap_key_set:
  ∀cmp ks t.
     ks ∈ FDOM (to_fmap cmp t) ⇒ ∃k. ks = key_set cmp k
Proof
 Induct_on `t` >> rw [to_fmap_def] >> metis_tac []
QED

Definition balanced_def:
  balanced l r ⇔ l + r ≤ 1 ∨ MAX l r ≤ delta * MIN l r
End

val structure_size_def = Define `
(structure_size Tip = 0) ∧
(structure_size (Bin n k v l r) = 1 + structure_size l + structure_size r)`;

val key_ordered_def = Define `
(key_ordered cmp k Tip res ⇔ T) ∧
(key_ordered cmp k (Bin n k' v l r) res ⇔
  cmp k k' = res ∧
  key_ordered cmp k l res ∧
  key_ordered cmp k r res)`;

Triviality key_ordered_to_fmap:
!cmp k t res.
  good_cmp cmp ⇒
    (key_ordered cmp k t res
   ⇔
    ∀ks. ks ∈ FDOM (to_fmap cmp t) ⇒ key_set_cmp cmp k ks res)
Proof
 Induct_on `t` >>
 rw [key_ordered_def, to_fmap_def] >>
 eq_tac >>
 rw [] >>
 metis_tac [key_set_cmp_thm]
QED

val invariant_def = Define `
(invariant cmp Tip ⇔ T) ∧
(invariant cmp (Bin s k v l r) ⇔
  s = 1 + structure_size l + structure_size r ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  balanced (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r)`;

val invariant_eq = Q.store_thm ("invariant_eq",
`(invariant cmp Tip ⇔ T) ∧
 (invariant cmp (Bin s k v l r) ⇔
  (good_cmp cmp ⇒ DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))) ∧
  (good_cmp cmp ⇒ key_set cmp k ∉ FDOM (to_fmap cmp l)) ∧
  (good_cmp cmp ⇒ key_set cmp k ∉ FDOM (to_fmap cmp r)) ∧
  s = 1 + structure_size l + structure_size r ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  balanced (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r)`,
 rw [invariant_def] >>
 eq_tac >>
 rw [DISJOINT_DEF, EXTENSION] >>
 CCONTR_TAC >>
 fs [] >>
 imp_res_tac key_ordered_to_fmap >>
 fs [] >>
 imp_res_tac to_fmap_key_set >>
 rw [] >>
 rfs [key_set_cmp_thm] >>
 metis_tac [cmp_thms]);

Triviality inv_props:
!cmp s k v l r.
  good_cmp cmp ∧
  invariant cmp (Bin s k v l r)
  ⇒
  DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r)) ∧
  (!x. key_set cmp x ∈ FDOM (to_fmap cmp l) ⇒ cmp k x = Greater) ∧
  (!x. key_set cmp x ∈ FDOM (to_fmap cmp r) ⇒ cmp k x = Less)
Proof
 rw [invariant_eq] >>
 imp_res_tac key_ordered_to_fmap >>
 rfs [key_set_cmp_thm]
QED

Triviality structure_size_thm:
  !cmp t. invariant cmp t ⇒ size t = structure_size t
Proof
 Cases_on `t` >>
 rw [size_def, invariant_def, structure_size_def]
QED

Triviality structure_size_to_fmap:
  !cmp t. good_cmp cmp ∧ invariant cmp t ⇒
          FCARD (to_fmap cmp t) = structure_size t
Proof
 Induct_on `t` >>
 rw [invariant_eq, structure_size_def, to_fmap_def, FCARD_FEMPTY] >>
 rw [FCARD_FUPDATE, FCARD_DISJOINT_UNION]
QED

val size_thm = Q.store_thm ("size_thm",
`!cmp t. good_cmp cmp ∧ invariant cmp t ⇒ size t = FCARD (to_fmap cmp t)`,
 metis_tac [structure_size_thm, structure_size_to_fmap]);

val null_thm = Q.store_thm ("null_thm",
`!cmp t. null t ⇔ (to_fmap cmp t = FEMPTY)`,
 Cases_on `t` >>
 rw [null_def, to_fmap_def]);

val lookup_thm = Q.store_thm ("lookup_thm",
`!cmp k t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  lookup cmp k t = FLOOKUP (to_fmap cmp t) (key_set cmp k)`,
 Induct_on `t` >>
 rw [lookup_def, to_fmap_def] >>
 imp_res_tac inv_props >>
 every_case_tac >>
 fs [invariant_eq, FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 rfs [key_set_eq] >>
 fs [FLOOKUP_DEF] >>
 metis_tac [cmp_thms]);

val member_thm = Q.store_thm ("member_thm",
`!cmp k t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  (member cmp k t ⇔ key_set cmp k ∈ FDOM (to_fmap cmp t))`,
 Induct_on `t` >>
 rw [member_def, to_fmap_def] >>
 imp_res_tac inv_props >>
 every_case_tac >>
 fs [invariant_def, FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 rfs [key_set_eq] >>
 fs [FLOOKUP_DEF] >>
 metis_tac [cmp_thms]);

val empty_thm = Q.store_thm ("empty_thm",
`!cmp. invariant cmp empty ∧ to_fmap cmp empty = FEMPTY`,
 rw [invariant_def, empty_def, to_fmap_def, FCARD_DEF]);

val singleton_thm = Q.store_thm ("singleton_thm",
`!cmp k v. invariant cmp (singleton k v) ∧ to_fmap cmp (singleton k v) = FEMPTY |+ (key_set cmp k,v)`,
 rw [balanced_def, invariant_def, singleton_def, to_fmap_def, size_def, structure_size_def,
     key_ordered_def]);

(* The balance routine from the comments in the Haskell file *)

val singleL_def = Define `
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3`;

val singleR_def = Define `
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)`;

val doubleL_def = Define `
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) =
  bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)`;

val doubleR_def = Define `
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 =
  bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)`;

val rotateL_def = Define `
(rotateL k x l (Bin s' k' x' ly ry) =
  if size ly < ratio * size ry then
    singleL k x l (Bin s' k' x' ly ry)
  else
    doubleL k x l (Bin s' k' x' ly ry)) ∧
(rotateL k x l Tip =
  doubleL k x l Tip)`;

val rotateR_def = Define `
(rotateR k x (Bin s' k' x' ly ry) r =
  if size ry < ratio * size ly then
    singleR k x (Bin s' k' x' ly ry) r
  else
    doubleR k x (Bin s' k' x' ly ry) r) ∧
(rotateR k x Tip r =
  doubleR k x Tip r)`;

val bal_def = Define `
bal k x l r =
  if size l + size r ≤ 1 then
    Bin (size l + size r + 1) k x l r
  else if size r > delta * size l then
    rotateL k x l r
  else if size l > delta * size r then
    rotateR k x l r
  else
    Bin (size l + size r + 1) k x l r`;

val balL_def = Define `
balL k x l r =
  if size l + size r ≤ 1 then
    Bin (size l + size r + 1) k x l r
  else if size l > delta * size r then
    rotateR k x l r
  else
    Bin (size l + size r + 1) k x l r`;

val balR_def = Define `
balR k x l r =
  if size l + size r ≤ 1 then
    Bin (size l + size r + 1) k x l r
  else if size r > delta * size l then
    rotateL k x l r
  else
    Bin (size l + size r + 1) k x l r`;

(* We want a formula that states how unbalanced two trees can be
 * and still be re-balanced by the balancer. It also has to allow the
 * trees to be as unbalanced as the link, insert and delete functions need. The
 * formula below is the result of guesswork. *)
val almost_balancedL_def = Define `
almost_balancedL l r =
  if l + r ≤ 1 ∨ l ≤ delta * r then
    balanced l r
  else if r = 0 then
    l < 5
  else if r = 1 then
    l < 8
  else
    2 * l < (2 * delta + 3) * r + 2`;

val almost_balancedR_def = Define `
almost_balancedR l r =
  if l + r ≤ 1 ∨ r ≤ delta * l then
    balanced l r
  else if l = 0 then
    r < 5
  else if l = 1 then
    r < 8
  else
    2 * r < (2 * delta + 3) * l + 2`;

Triviality balanced_lem1: !l r. l + r ≤ 1 ⇒ balanced l r
Proof rw [balanced_def]
QED

Triviality balanced_lem2:
  !l r.
    ¬(l > delta * r) ∧
    almost_balancedL l r ∧
    ¬(l + r ≤ 1)
  ⇒
    balanced l r
Proof rw [almost_balancedL_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER,
          TIMES_MIN, delta_def]
QED

Triviality balanced_lem3:
  !b b0 r.
     almost_balancedL (b + b0 + 1) r ∧
     b + b0 + 1 > delta * r ∧
     b0 < ratio * b ∧
     balanced b b0
   ⇒
     balanced b (b0 + r + 1) ∧
     balanced b0 r
Proof
 rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]
QED

Triviality balanced_lem4:
!b b' b0' r.
  almost_balancedL (b + b' + b0' + 2) r ∧
  b + b' + b0' + 2 > delta * r ∧
  ¬(b' + b0' + 1 < ratio * b) ∧
  balanced b (b' + b0' + 1) ∧
  balanced b' b0'
  ⇒
  balanced (b + b' + 1) (b0' + r + 1) ∧
  balanced b b' ∧
  balanced b0' r
Proof
 rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]
QED

Triviality balanced_lem5:
!l r.
   ¬(r > delta * l) ∧ almost_balancedR l r
  ⇒
   balanced l r
Proof rw [almost_balancedR_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER,
          TIMES_MIN, delta_def]
QED

Triviality balanced_lem6:
  !b b0 l.
    almost_balancedR l (b + b0 + 1) ∧
    b + b0 + 1 > delta * l ∧
    b < ratio * b0 ∧
    balanced b b0
   ⇒
    balanced (b + l + 1) b0 ∧ balanced l b
Proof
 rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]
QED

Triviality balanced_lem7:
  !b b0 b0' l b'.
    almost_balancedR l (b' + b0 + b0' + 2) ∧
    b' + b0 + b0' + 2 > delta * l ∧
    ¬(b' + b0' + 1 < ratio * b0) ∧
    balanced (b' + b0' + 1) b0 ∧
    balanced b' b0'
   ⇒
    balanced (b' + l + 1) (b0 + b0' + 1) ∧
    balanced l b' ∧
    balanced b0' b0
Proof
 rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def] >>
 fs [MIN_DEF]
QED

Triviality singleR_thm:
!k v r cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL n (size r) ∧
  ¬(size r + n ≤ 1) ∧
  n > delta * size r ∧
  size b0 < ratio * size b ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp r
 ⇒
  invariant cmp (singleR k v (Bin n k' v' b b0) r) ∧
  to_fmap cmp (singleR k v (Bin n k' v' b b0) r) =
    (to_fmap cmp (Bin n k' v' b b0) ⊌ to_fmap cmp r) |+ (key_set cmp k,v)
Proof
 rw [singleR_def] >>
 imp_res_tac inv_props
 >- (fs [invariant_def, bin_def, size_def, structure_size_def, bin_def,
         key_ordered_def] >>
     imp_res_tac structure_size_thm >>
     rw [size_def] >>
     rfs [size_def, key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, balanced_lem3,
                ADD_ASSOC])
 >- (rw [to_fmap_def, bin_def, FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [to_fmap_def, invariant_def, key_ordered_def] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, FUPDATE_COMMUTES,
                FUNION_ASSOC])
QED

Triviality doubleR_thm:
!k v r cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL n (size r) ∧
  ¬(size r + n ≤ 1) ∧
  n > delta * size r ∧
  ¬(size b0 < ratio * size b) ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp r
 ⇒
  invariant cmp (doubleR k v (Bin n k' v' b b0) r) ∧
  to_fmap cmp (doubleR k v (Bin n k' v' b b0) r) =
    (to_fmap cmp (Bin n k' v' b b0) ⊌ to_fmap cmp r) |+ (key_set cmp k,v)
Proof
 rw [] >>
 `structure_size b0 ≠ 0`
          by (fs [delta_def, ratio_def, invariant_def, size_def,
                  NOT_LESS_EQUAL, NOT_LESS, NOT_GREATER] >>
              imp_res_tac structure_size_thm >>
              fs []) >>
 Cases_on `b0` >>
 fs [structure_size_def, doubleR_def, bin_def] >>
 imp_res_tac inv_props >>
 fs [Once invariant_def] >>
 imp_res_tac inv_props >>
 fs [invariant_def, to_fmap_def]
 >- (fs [size_def, bin_def, to_fmap_def] >>
     imp_res_tac structure_size_thm >>
     simp [structure_size_def, key_ordered_def] >>
     fs [structure_size_def, to_fmap_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     rw []
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms] >>
     metis_tac [ADD_ASSOC, balanced_lem4])
 >- (rw [FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [key_ordered_def] >>
     rfs [key_ordered_to_fmap]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms] >>
     `key_set cmp k' ≠ key_set cmp k'' ∧
      key_set cmp k ≠ key_set cmp k' ∧
      key_set cmp k ≠ key_set cmp k''`
                   by metis_tac [key_set_eq, cmp_thms] >>
     metis_tac [FUPDATE_COMMUTES, FUNION_ASSOC])
QED

Triviality rotateR_thm:
!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  ¬(size l + size r ≤ 1) ∧
  size l > delta * size r ∧
  almost_balancedL (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (rotateR k v l r) ∧
  to_fmap cmp (rotateR k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)
Proof
  Cases_on `l`
  >- fs [size_def] >>
  rw [size_def, rotateR_def] >>
  metis_tac [singleR_thm, doubleR_thm, ADD_COMM, NOT_ZERO_LT_ZERO, GREATER_DEF]
QED

Triviality balanceL_balL:
!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  balanceL k v l r = balL k v l r
Proof
 ho_match_mp_tac balanceL_ind >>
 rw [] >>
 rw [balanceL_def, balL_def, rotateR_def, doubleR_def, bin_def, singleR_def] >>
 imp_res_tac structure_size_thm >>
 fs [size_def, invariant_def, structure_size_def] >>
 imp_res_tac structure_size_thm >>
 fs [balanced_def] >>
 TRY (Cases_on `l` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `r` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (fs [ratio_def] >> NO_TAC) >>
 every_case_tac >>
 fs [size_def, structure_size_def, ratio_def, delta_def] >>
 imp_res_tac structure_size_thm >>
 fs [invariant_def, doubleR_def, bin_def, size_def] >>
 imp_res_tac structure_size_thm >>
 rw []
QED

Triviality balanceL_thm:
!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceL k v l r) ∧
  to_fmap cmp (balanceL k v l r) =
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)
Proof
 rw [] >>
 `balanceL k v l r = balL k v l r` by metis_tac [balanceL_balL] >>
 rw [] >>
 rw [balL_def, invariant_def] >>
 imp_res_tac structure_size_thm >>
 rw [balanced_lem1, balanced_lem2, to_fmap_def] >>
 metis_tac [rotateR_thm]
QED

Triviality singleL_thm:
!k v l cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) n ∧
  ¬(size l + n ≤ 1) ∧
  n > delta * size l ∧
  size b < ratio * size b0 ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp l
  ⇒
  invariant cmp (singleL k v l (Bin n k' v' b b0)) ∧
  to_fmap cmp (singleL k v l (Bin n k' v' b b0)) =
    (to_fmap cmp l ⊌ to_fmap cmp (Bin n k' v' b b0)) |+ (key_set cmp k,v)
Proof
 rw [singleL_def] >>
 imp_res_tac inv_props
 >- (fs [invariant_def, bin_def, size_def, structure_size_def, bin_def, key_ordered_def] >>
     imp_res_tac structure_size_thm >>
     rw [size_def] >>
     rfs [size_def, key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, balanced_lem6,
                ADD_ASSOC])
 >- (rw [to_fmap_def, bin_def, FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [to_fmap_def, invariant_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, FUPDATE_COMMUTES,
                FUNION_ASSOC])
QED

Triviality doubleL_thm:
!k v l cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) n ∧
  ¬(n + size l ≤ 1) ∧
  n > delta * size l ∧
  ¬(size b < ratio * size b0) ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp l
  ⇒
  invariant cmp (doubleL k v l (Bin n k' v' b b0)) ∧
  to_fmap cmp (doubleL k v l (Bin n k' v' b b0)) =
    (to_fmap cmp l ⊌ to_fmap cmp (Bin n k' v' b b0)) |+ (key_set cmp k,v)
Proof
 rw [] >>
 `structure_size b ≠ 0`
          by (fs [delta_def, ratio_def, invariant_def, size_def,
                  NOT_LESS_EQUAL, NOT_LESS, NOT_GREATER] >>
              imp_res_tac structure_size_thm >>
              fs []) >>
 Cases_on `b` >>
 fs [structure_size_def, doubleL_def, bin_def] >>
 imp_res_tac inv_props >>
 fs [Once invariant_def] >>
 imp_res_tac inv_props >>
 fs [invariant_def, to_fmap_def]
 >- (fs [size_def, bin_def, to_fmap_def] >>
     imp_res_tac structure_size_thm >>
     simp [structure_size_def, key_ordered_def] >>
     fs [structure_size_def, to_fmap_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     rw []
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms] >>
     metis_tac [ADD_ASSOC, balanced_lem7])
 >- (rw [FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [key_ordered_def] >>
     rfs [key_ordered_to_fmap]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- (`key_set cmp k' ≠ key_set cmp k'' ∧
          key_set cmp k ≠ key_set cmp k' ∧
          key_set cmp k ≠ key_set cmp k''`
                   by metis_tac [key_set_eq, cmp_thms] >>
         metis_tac [FUPDATE_COMMUTES, FUNION_ASSOC]))
QED

Triviality rotateL_thm:
!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k r Less ∧
  key_ordered cmp k l Greater ∧
  ¬(size l + size r ≤ 1) ∧
  size r > delta * size l ∧
  almost_balancedR (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (rotateL k v l r) ∧
  to_fmap cmp (rotateL k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)
Proof
 Cases_on `r`
 >- fs [size_def] >>
 rw [size_def, rotateL_def] >>
 metis_tac [singleL_thm, doubleL_thm, ADD_COMM, NOT_ZERO_LT_ZERO, GREATER_DEF]
QED

Triviality balanceR_balR:
!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  balanceR k v l r = balR k v l r
Proof
 ho_match_mp_tac balanceR_ind >>
 rw [] >>
 rw [balanceR_def, balR_def, rotateL_def, doubleL_def, bin_def, singleL_def] >>
 imp_res_tac structure_size_thm >>
 fs [size_def, invariant_def, structure_size_def] >>
 imp_res_tac structure_size_thm >>
 fs [balanced_def] >>
 TRY (Cases_on `l` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `r` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `v4` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (fs [ratio_def] >> NO_TAC) >>
 every_case_tac >>
 fs [size_def, structure_size_def, ratio_def, delta_def] >>
 imp_res_tac structure_size_thm >>
 fs [invariant_def, doubleL_def, bin_def, size_def] >>
 imp_res_tac structure_size_thm >>
 rw []
QED

Triviality balanceR_thm:
!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k r Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceR k v l r) ∧
  to_fmap cmp (balanceR k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)
Proof
 rw [] >>
 `balanceR k v l r = balR k v l r` by metis_tac [balanceR_balR] >>
 rw [balR_def, invariant_def] >>
 imp_res_tac structure_size_thm >>
 rw [balanced_lem1, balanced_lem5, to_fmap_def] >>
 metis_tac [rotateL_thm]
QED

Triviality almost_balancedL_thm:
  !l r.
    balanced l r
   ⇒
    almost_balancedL l r ∧ almost_balancedL (l + 1) r ∧
    almost_balancedL l (r - 1)
Proof
 rw [almost_balancedL_def] >>
 fs [balanced_def, NOT_LESS_EQUAL, TIMES_MIN] >>
 rw [] >>
 CCONTR_TAC >>
 fs [] >>
 fs [NOT_LESS_EQUAL] >>
 fs [delta_def, MIN_DEF]
QED

Triviality almost_balancedR_thm:
  !l r.
    balanced l r
   ⇒
    almost_balancedR l r ∧ almost_balancedR l (r + 1) ∧
    almost_balancedR (l - 1) r
Proof
 rw [almost_balancedR_def] >>
 fs [balanced_def, NOT_LESS_EQUAL, TIMES_MIN] >>
 rw [] >>
 CCONTR_TAC >>
 fs [] >>
 fs [NOT_LESS_EQUAL] >>
 fs [delta_def, MIN_DEF] >>
 fs [NOT_LESS, LESS_OR_EQ] >>
 rw [] >>
 decide_tac
QED

Theorem insert_thm:
∀t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (insert cmp k v t) ∧
  to_fmap cmp (insert cmp k v t) = to_fmap cmp t |+ (key_set cmp k,v)
Proof
 Induct_on `t`
 >- fs [insert_def, singleton_def, to_fmap_def, invariant_eq,
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 simp [invariant_eq] >>
 rpt gen_tac >>
 strip_tac >>
 fs [insert_def] >>
 Cases_on `cmp k k'` >>
 fs [] >>
 simp [] >>
 TRY (inv_mp_tac balanceL_thm) >>
 TRY (inv_mp_tac balanceR_thm) >>
 conj_asm1_tac >>
 rw [to_fmap_def]
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     imp_res_tac to_fmap_key_set >>
     rw [key_set_cmp_thm] >>
     metis_tac [cmp_thms])
 >- (imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [key_ordered_to_fmap] >>
     metis_tac [almost_balancedL_thm])
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     `key_set cmp k ≠ key_set cmp k'` by metis_tac [key_set_eq, cmp_thms] >>
     metis_tac [FUPDATE_COMMUTES])
 >- (fs [invariant_def] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms])
 >- metis_tac [key_set_eq, FUPDATE_EQ]
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     imp_res_tac to_fmap_key_set >>
     rw [key_set_cmp_thm] >>
     metis_tac [cmp_thms])
 >- (imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [key_ordered_to_fmap] >>
     metis_tac [almost_balancedR_thm])
 >- (rw [FUNION_FUPDATE_2, to_fmap_def] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [FUPDATE_COMMUTES, cmp_thms, to_fmap_key_set, key_set_cmp_thm])
QED

val lookup_insert = Q.store_thm("lookup_insert",
  `good_cmp cmp ∧ invariant cmp t ⇒
   lookup cmp k (insert cmp k' v t) =
   if cmp k k' = Equal then SOME v else lookup cmp k t`,
  rw[] \\ rw[lookup_thm,insert_thm,FLOOKUP_UPDATE] \\
  metis_tac[key_set_eq,comparisonTheory.cmp_thms]);

val comparison_distinct = TypeBase.distinct_of ``:ordering``

val insertR_thm = Q.store_thm ("insertR_thm",
`∀t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (insertR cmp k v t) ∧
  to_fmap cmp (insertR cmp k v t) =
    if key_set cmp k ∈ FDOM (to_fmap cmp t) then to_fmap cmp t else to_fmap cmp t |+ (key_set cmp k,v)`,
 Induct_on `t`
 >- fs [insertR_def, singleton_def, to_fmap_def, invariant_def,
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 rpt gen_tac >>
 strip_tac >>
 imp_res_tac inv_props >>
 fs [insertR_def, invariant_def] >>
 Cases_on `cmp k k'` >>
 fs [] >>
 simp [to_fmap_def]
 >- (`almost_balancedL (size (insertR cmp k v t)) (size t')`
             by (imp_res_tac size_thm >>
                 rw [FCARD_FUPDATE] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [almost_balancedL_thm]) >>
     `key_ordered cmp k' (insertR cmp k v t) Greater`
              by (rfs [key_ordered_to_fmap] >>
                  rw [] >>
                  rw [key_set_cmp_thm] >>
                  metis_tac [good_cmp_def]) >>
     rw [balanceL_thm] >>
     imp_res_tac balanceL_thm >>
     rw [FUNION_FUPDATE_1] >>
     metis_tac [FUPDATE_COMMUTES, good_cmp_def, comparison_distinct])
 >- (fs [invariant_def] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms,key_set_eq, FUPDATE_EQ])
 >- (`almost_balancedR (size t) (size (insertR cmp k v t'))`
             by (imp_res_tac size_thm >>
                 rw [FCARD_FUPDATE] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [almost_balancedR_thm]) >>
     `key_ordered cmp k' (insertR cmp k v t') Less`
              by (fs [key_ordered_to_fmap] >>
                  rw [] >>
                  imp_res_tac to_fmap_key_set >>
                  rw [key_set_cmp_thm] >>
                  metis_tac [cmp_thms]) >>
     rw [balanceR_thm] >>
     imp_res_tac balanceR_thm >>
     rw [FUNION_FUPDATE_2] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [FUPDATE_COMMUTES, good_cmp_def, comparison_distinct]));

val insertMax_thm = Q.store_thm ("insertMax_thm",
`∀t.
  good_cmp cmp ∧
  invariant cmp t ∧
  (!k1. k1 ∈ FDOM (to_fmap cmp t) ⇒ key_set_cmp cmp k k1 Greater)
  ⇒
  invariant cmp (insertMax k v t) ∧
  to_fmap cmp (insertMax k v t) = to_fmap cmp t |+ (key_set cmp k,v)`,
 Induct_on `t`
 >- fs [insertMax_def, singleton_def, to_fmap_def, invariant_def,
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 rpt gen_tac >>
 strip_tac >>
 fs [insertMax_def, invariant_def, to_fmap_def] >>
 inv_mp_tac balanceR_thm >>
 conj_asm1_tac >>
 simp []
 >- (rfs [key_ordered_to_fmap] >>
     imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [] >>
     metis_tac [almost_balancedR_thm, good_cmp_def, key_set_cmp_thm]) >>
 rw [FUNION_FUPDATE_2] >>
 rfs [key_ordered_to_fmap] >>
 metis_tac [FUPDATE_COMMUTES, cmp_thms, key_set_cmp_thm]);

val insertMin_thm = Q.store_thm ("insertMin_thm",
`∀t.
  good_cmp cmp ∧
  invariant cmp t ∧
  (!k1. k1 ∈ FDOM (to_fmap cmp t) ⇒ key_set_cmp cmp k k1 Less)
  ⇒
  invariant cmp (insertMin k v t) ∧
  to_fmap cmp (insertMin k v t) = to_fmap cmp t |+ (key_set cmp k,v)`,
 Induct_on `t`
 >- fs [insertMin_def, singleton_def, to_fmap_def, invariant_def,
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 rpt gen_tac >>
 strip_tac >>
 fs [insertMin_def, invariant_def, to_fmap_def] >>
 simp [] >>
 `almost_balancedL (size (insertMin k v t)) (size t')`
         by (imp_res_tac size_thm >>
             rw [FCARD_FUPDATE] >>
             fs [key_ordered_to_fmap] >>
             metis_tac [almost_balancedL_thm]) >>
 `key_ordered cmp k' (insertMin k v t) Greater`
              by (rfs [key_ordered_to_fmap] >>
                  rw [] >>
                  imp_res_tac to_fmap_key_set >>
                  rw [key_set_cmp_thm] >>
                  metis_tac [cmp_thms, key_set_cmp_thm]) >>
 rw [balanceL_thm] >>
 imp_res_tac balanceL_thm >>
 rw [FUNION_FUPDATE_1] >>
 metis_tac [FUPDATE_COMMUTES, cmp_thms, key_set_cmp_thm]);

val deleteFindMin = Q.store_thm ("deleteFindMin",
`∀t t' k v.
  good_cmp cmp ∧
  invariant cmp t ∧
  ~null t ∧
  deleteFindMin t = ((k,v),t')
  ⇒
  invariant cmp t' ∧
  key_ordered cmp k t' Less ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v ∧
  to_fmap cmp t' =
    DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
 ho_match_mp_tac (fetch "-" "deleteFindMin_ind") >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac >>
 rpt gen_tac >>
 TRY DISCH_TAC >>
 fs [deleteFindMin_def, invariant_eq, to_fmap_def] >>
 fs [null_def, to_fmap_def, FUNION_FEMPTY_1, deleteFindMin_def] >>
 BasicProvers.VAR_EQ_TAC >>
 fs [to_fmap_def, FLOOKUP_UPDATE, key_ordered_def, LET_THM, null_def]
 >- (rw [] >>
     fs [key_ordered_to_fmap] >>
     rw [FLOOKUP_EXT, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FUN_EQ_THM] >>
     rw [flookup_thm] >>
     fs [] >>
     metis_tac [comparison_distinct, good_cmp_def]) >>
 `?km l. deleteFindMin (Bin (structure_size v8 + (structure_size v9 + 1)) v6 v7 v8 v9) = (km,l)`
            by metis_tac [pairTheory.pair_CASES] >>
 fs [] >>
 rpt BasicProvers.VAR_EQ_TAC >>
 inv_mp_tac balanceR_thm >>
 simp [] >>
 Cases_on `key_set cmp v6 = key_set cmp k'` >>
 fs []
 >- (`FDOM (to_fmap cmp l) = FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
             by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                 fs [FDOM_DRESTRICT, EXTENSION] >>
                 rfs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             metis_tac [])
         >- (fs [size_def] >>
             imp_res_tac size_thm >>
             rw [DELETE_INSERT, FCARD_DRESTRICT] >>
             `key_set cmp k' ∉ FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
                          by (fs [key_ordered_to_fmap] >>
                              metis_tac [good_cmp_def, comparison_distinct]) >>
             imp_res_tac DELETE_NON_ELEMENT >>
             rw [CARD_DISJOINT_UNION] >>
             imp_res_tac almost_balancedR_thm >>
             fs [] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [FLOOKUP_EXT, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION,
         FUN_EQ_THM]
     >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm])
 >- (`key_set cmp k' ∈ FDOM (to_fmap cmp v8 ⊌ to_fmap cmp v9)`
           by (every_case_tac >>
               fs [FLOOKUP_DEF]) >>
     `key_set cmp k ≠ key_set cmp k' ∧ cmp k' k = Less`
             by (rfs [key_ordered_to_fmap] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms, to_fmap_key_set, key_set_cmp_thm]) >>
     simp [] >>
     `FDOM (to_fmap cmp l) = (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) DELETE key_set cmp k'`
                   by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                       fs [FDOM_DRESTRICT, EXTENSION] >>
                       rfs [key_ordered_to_fmap] >>
                       metis_tac [cmp_thms]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             fs [key_ordered_to_fmap] >>
             rw [key_set_cmp_thm] >>
             metis_tac [key_set_cmp_thm, to_fmap_key_set])
         >- (imp_res_tac size_thm >>
             rw [FCARD_FUPDATE, FDOM_DRESTRICT] >>
             rw [FCARD_DRESTRICT, DELETE_INSERT] >>
             `(FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) ∩
              (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k')
              =
              FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k'`
                       by (rw [EXTENSION] >>
                           metis_tac [key_set_eq, EXTENSION]) >>
             simp [CARD_UNION_EQN] >>
             fs [DISJOINT_DEF] >|
             [`CARD (FDOM (to_fmap cmp v8)) ≠ 0`
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v8))` by decide_tac,
              `CARD (FDOM (to_fmap cmp v9)) ≠ 0`
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v9))` by decide_tac] >>
             rw [] >>
             imp_res_tac almost_balancedR_thm >>
             fs [size_def] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [FLOOKUP_EXT, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION,
         FUN_EQ_THM]
     >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]));

val deleteFindMax = Q.store_thm ("deleteFindMax",
`∀t t' k v.
  good_cmp cmp ∧
  invariant cmp t ∧
  ~null t ∧
  deleteFindMax t = ((k,v),t')
  ⇒
  invariant cmp t' ∧
  key_ordered cmp k t' Greater ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v ∧
  to_fmap cmp t' =
    DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
 ho_match_mp_tac (fetch "-" "deleteFindMax_ind") >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac >>
 rpt gen_tac >>
 TRY DISCH_TAC >>
 fs [deleteFindMax_def, invariant_eq, to_fmap_def] >>
 fs [null_def, to_fmap_def, FUNION_FEMPTY_2, deleteFindMax_def] >>
 BasicProvers.VAR_EQ_TAC >>
 fs [to_fmap_def, FLOOKUP_UPDATE, key_ordered_def, LET_THM, null_def]
 >- (rw [] >>
     fs [key_ordered_to_fmap] >>
     rw [FLOOKUP_EXT, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FUN_EQ_THM] >>
     rw [flookup_thm] >>
     fs [] >>
     metis_tac [comparison_distinct, good_cmp_def]) >>
 `?km l. deleteFindMax (Bin (structure_size v8 + (structure_size v9 + 1)) v6 v7 v8 v9) = (km,l)`
            by metis_tac [pairTheory.pair_CASES] >>
 fs [] >>
 rpt BasicProvers.VAR_EQ_TAC >>
 inv_mp_tac balanceL_thm >>
 simp [] >>
 Cases_on `key_set cmp v6 = key_set cmp k'` >>
 fs []
 >- (`FDOM (to_fmap cmp l') = FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
             by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                 fs [FDOM_DRESTRICT, EXTENSION] >>
                 rfs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             metis_tac [])
         >- (fs [size_def] >>
             imp_res_tac size_thm >>
             rw [DELETE_INSERT, FCARD_DRESTRICT] >>
             `key_set cmp k' ∉ FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)`
                          by (fs [key_ordered_to_fmap] >>
                              metis_tac [good_cmp_def, comparison_distinct]) >>
             imp_res_tac DELETE_NON_ELEMENT >>
             rw [CARD_DISJOINT_UNION] >>
             imp_res_tac almost_balancedL_thm >>
             fs [] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [FLOOKUP_EXT, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION,
         FUN_EQ_THM]
     >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm])
 >- (`key_set cmp k' ∈ FDOM (to_fmap cmp v8 ⊌ to_fmap cmp v9)`
             by (every_case_tac >>
                 fs [FLOOKUP_DEF]) >>
     `key_set cmp k' ≠ key_set cmp k ∧ cmp k' k = Greater`
             by (rfs [key_ordered_to_fmap] >>
                 fs [key_ordered_to_fmap] >>
                 metis_tac [cmp_thms, to_fmap_key_set, key_set_cmp_thm]) >>
     simp [] >>
     `FDOM (to_fmap cmp l') = (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) DELETE key_set cmp k'`
                   by (FIRST_ASSUM (assume_tac o MATCH_MP (METIS_PROVE [] ``m1 = m2 ⇒ FDOM m1 = FDOM m2``)) >>
                       fs [FDOM_DRESTRICT, EXTENSION] >>
                       metis_tac [comparison_distinct, key_ordered_to_fmap, good_cmp_def]) >>
     conj_asm1_tac
     >- (rw []
         >- (rfs [key_ordered_to_fmap] >>
             fs [key_ordered_to_fmap] >>
             rw [key_set_cmp_thm] >>
             metis_tac [key_set_cmp_thm, to_fmap_key_set])
         >- (imp_res_tac size_thm >>
             rw [FCARD_FUPDATE, FDOM_DRESTRICT] >>
             rw [FCARD_DRESTRICT, DELETE_INSERT] >>
             `(FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9)) ∩
              (key_set cmp v6 INSERT FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k')
              =
              FDOM (to_fmap cmp v8) ∪ FDOM (to_fmap cmp v9) DELETE key_set cmp k'`
                       by (rw [EXTENSION] >>
                           metis_tac [key_set_eq, EXTENSION]) >>
             simp [CARD_UNION_EQN] >>
             fs [DISJOINT_DEF] >|
             [`CARD (FDOM (to_fmap cmp v8)) ≠ 0`
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v8))` by decide_tac,
              `CARD (FDOM (to_fmap cmp v9)) ≠ 0`
                        by (rw [CARD_EQ_0, EXTENSION] >>
                            metis_tac []) >>
                  `0 < CARD (FDOM (to_fmap cmp v9))` by decide_tac] >>
             rw [] >>
             imp_res_tac almost_balancedL_thm >>
             fs [size_def] >>
             metis_tac [FCARD_DEF, structure_size_thm, size_thm])) >>
     strip_tac >>
     simp [] >>
     rw [FLOOKUP_EXT, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, FLOOKUP_FUNION,
         FUN_EQ_THM]
    >- (rfs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         fs [key_ordered_to_fmap, FDOM_DRESTRICT] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]) >>
     every_case_tac >>
     fs [flookup_thm,key_ordered_to_fmap] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm]));


val FLOOKUP_EXT' = FLOOKUP_EXT |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]
val glue_thm = Q.store_thm ("glue_thm",
`!l r.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r ∧
  (!ks ks'. ks ∈ FDOM (to_fmap cmp l) ∧ ks' ∈ FDOM (to_fmap cmp r) ⇒ key_set_cmp2 cmp ks ks' Less) ∧
  balanced (size l) (size r)
  ⇒
  invariant cmp (glue l r) ∧
  to_fmap cmp (glue l r) = FUNION (to_fmap cmp l) (to_fmap cmp r)`,
 Cases_on `l` >>
 Cases_on `r` >>
 simp [size_def, glue_def] >>
 TRY (simp [to_fmap_def, FUNION_FEMPTY_2, FUNION_FEMPTY_1] >> NO_TAC) >>
 strip_tac >>
 Cases_on `n > n'` >>
 simp []
 >- (`?k' v' l. deleteFindMax (Bin n k v b b0) = ((k',v'),l)`
              by metis_tac [pairTheory.pair_CASES] >>
     simp [] >>
     inv_mp_tac balanceR_thm >>
     simp [] >>
     inv_to_front_tac ``invariant`` >>
     inv_mp_tac deleteFindMax >>
     simp [Once SWAP_EXISTS_THM] >>
     qexists_tac `Bin n k v b b0` >>
     simp [null_def] >>
     strip_tac >>
     imp_res_tac fdom_eq >>
     fs [FDOM_DRESTRICT, DELETE_INSERT, FLOOKUP_UPDATE] >>
     fs [DELETE_INTER2] >>
     rw []
     >- (rw [FLOOKUP_EXT', FLOOKUP_FUNION, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
         every_case_tac >>
         fs [invariant_eq, FLOOKUP_DEF] >>
         metis_tac [good_cmp_def, comparison_distinct])
     >- (rfs [key_ordered_to_fmap] >>
         fs [FLOOKUP_DEF] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp2_thm])
     >- (fs [invariant_eq] >>
         `size l = size (Bin n k v b b0) - 1`
                     by (rw [size_def] >>
                         imp_res_tac size_thm >>
                         rw [FCARD_DEF, FDOM_FUPDATE, FDOM_DRESTRICT, to_fmap_def,
                             CARD_DISJOINT_UNION, DELETE_INTER2] >>
                         fs [to_fmap_def, FLOOKUP_DEF] >>
                         metis_tac [structure_size_thm, FCARD_DEF]) >>
         imp_res_tac almost_balancedR_thm >>
         fs [size_def] >>
         rw [] >>
         FULL_SIMP_TAC (srw_ss()++ARITH_ss) []))
 >- (`?k v l. deleteFindMin (Bin n' k' v' b' b0') = ((k,v),l)`
              by metis_tac [pairTheory.pair_CASES] >>
     simp [] >>
     inv_mp_tac balanceL_thm >>
     simp [] >>
     inv_to_front_tac ``invariant`` >>
     inv_mp_tac deleteFindMin >>
     simp [Once SWAP_EXISTS_THM] >>
     qexists_tac `Bin n' k' v' b' b0'` >>
     simp [null_def] >>
     strip_tac >>
     imp_res_tac fdom_eq >>
     fs [FDOM_DRESTRICT, DELETE_INSERT, FLOOKUP_UPDATE] >>
     fs [DELETE_INTER2] >>
     rw []
     >- (rw [FLOOKUP_EXT', FLOOKUP_FUNION, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
         every_case_tac
         >- metis_tac [] >>
         fs [invariant_eq, FLOOKUP_DEF]
         >- metis_tac [cmp_thms, key_set_cmp2_thm])
     >- (rfs [key_ordered_to_fmap] >>
         fs [FLOOKUP_DEF] >>
         rw [] >>
         imp_res_tac to_fmap_key_set >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp2_thm])
     >- (fs [invariant_eq] >>
         `size l = size (Bin n' k' v' b' b0') - 1`
                     by (rw [size_def] >>
                         imp_res_tac size_thm >>
                         rw [FCARD_DEF, FDOM_FUPDATE, FDOM_DRESTRICT, to_fmap_def,
                             CARD_DISJOINT_UNION, DELETE_INTER2] >>
                         fs [to_fmap_def, FLOOKUP_DEF] >>
                         metis_tac [structure_size_thm, FCARD_DEF]) >>
         imp_res_tac almost_balancedL_thm >>
         fs [size_def] >>
         rw [] >>
         FULL_SIMP_TAC (srw_ss()++ARITH_ss) [])));

val to_fmap_tac =
  rw [to_fmap_def] >>
  rw [FLOOKUP_EXT', FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [FLOOKUP_DEF] >>
  fs [to_fmap_def] >>
  fs [key_ordered_to_fmap] >>
  rfs [key_ordered_to_fmap] >>
  metis_tac [cmp_thms, to_fmap_key_set, key_set_eq, key_set_cmp_thm];

val delete_thm = Q.store_thm ("delete_thm",
`!t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (delete cmp k t) ∧
  to_fmap cmp (delete cmp k t) =
    DRESTRICT (to_fmap cmp t) (FDOM (to_fmap cmp t) DELETE key_set cmp k)`,
 Induct_on `t`
 >- rw [delete_def, to_fmap_def] >>
 rpt gen_tac >>
 strip_tac >>
 simp [delete_def] >>
 fs [invariant_eq] >>
 Cases_on `cmp k k'` >>
 simp []
 >- (inv_mp_tac balanceR_thm >>
     simp [] >>
     rw []
     >- (fs [key_ordered_to_fmap] >>
         rfs [key_ordered_to_fmap] >>
         rw [FDOM_DRESTRICT] >>
         metis_tac [to_fmap_key_set, key_set_cmp_thm])
     >- (imp_res_tac size_thm >>
         rw [FCARD_DRESTRICT, DELETE_INTER2] >>
         imp_res_tac almost_balancedR_thm >>
         metis_tac [FCARD_DEF])
     >- to_fmap_tac)
 >- (inv_mp_tac glue_thm >>
     rw [] >>
     rfs [key_ordered_to_fmap]
     >- metis_tac [key_set_cmp2_thm, to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- to_fmap_tac)
 >- (inv_mp_tac balanceL_thm >>
     simp [] >>
     rw []
     >- (fs [key_ordered_to_fmap] >>
         rfs [key_ordered_to_fmap] >>
         rw [FDOM_DRESTRICT] >>
         metis_tac [to_fmap_key_set, key_set_cmp_thm])
     >- (imp_res_tac size_thm >>
         rw [FCARD_DRESTRICT, DELETE_INTER2] >>
         imp_res_tac almost_balancedL_thm >>
         metis_tac [FCARD_DEF])
     >- to_fmap_tac));

Theorem lookup_delete:
 good_cmp cmp /\ invariant cmp t ==>
 lookup cmp k (delete cmp k' t) =
 if cmp k k' = Equal then NONE else lookup cmp k t
Proof
 rw[lookup_thm,delete_thm,FLOOKUP_DRESTRICT] \\ metis_tac[key_set_eq,FLOOKUP_DEF]
QED

val restrict_set_def = Define `
restrict_set cmp lo hi =
{ k | option_cmp cmp lo (SOME k) = Less ∧
      option_cmp2 cmp (SOME k) hi = Less }`;

val restrict_domain_def = Define `
  restrict_domain cmp lo hi m =
    DRESTRICT m (IMAGE (key_set cmp) (restrict_set cmp lo hi))`;

Triviality restrict_domain_union:
  restrict_domain cmp lo hi (FUNION m1 m2) =
    FUNION (restrict_domain cmp lo hi m1) (restrict_domain cmp lo hi m2)
Proof
 rw [restrict_domain_def, FLOOKUP_EXT', FLOOKUP_DRESTRICT, FLOOKUP_FUNION] >>
 rw [FLOOKUP_DRESTRICT, FLOOKUP_FUNION]
QED

Triviality restrict_domain_update:
  good_cmp cmp
 ⇒
  restrict_domain cmp lo hi (m1 |+ (key_set cmp k,v)) =
   if k ∈ restrict_set cmp lo hi then
     restrict_domain cmp lo hi m1 |+ (key_set cmp k,v)
   else
     restrict_domain cmp lo hi m1
Proof
 rw [restrict_domain_def, FLOOKUP_EXT', FLOOKUP_DRESTRICT, FLOOKUP_FUNION] >>
 rfs [key_set_eq] >>
 fs [restrict_set_def] >>
 Cases_on `hi` >>
 Cases_on `lo` >>
 fs [option_cmp_def, option_cmp2_def] >>
 metis_tac [cmp_thms]
QED

Triviality restrict_domain_FMERGE_WITH_KEY:
  restrict_domain cmp lo hi (FMERGE_WITH_KEY f m1 m2) =
    FMERGE_WITH_KEY f (restrict_domain cmp lo hi m1) (restrict_domain cmp lo hi m2)
Proof
  rw[restrict_domain_def, fmap_eq_flookup,
     FLOOKUP_DRESTRICT, FLOOKUP_FMERGE_WITH_KEY] >>
  IF_CASES_TAC >> gvs[]
QED

Definition bounded_root_def:
  bounded_root cmp lk hk t ⇔
    !s k v l r. t = Bin s k v l r ⇒ k ∈ restrict_set cmp lk hk
End

Triviality trim_thm:
!t lk hk cmp.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (trim cmp lk hk t) ∧
  bounded_root cmp lk hk (trim cmp lk hk t) ∧
  to_fmap cmp (trim cmp lk hk t) SUBMAP to_fmap cmp t ∧
  restrict_domain cmp lk hk (to_fmap cmp (trim cmp lk hk t)) =
     restrict_domain cmp lk hk (to_fmap cmp t)
Proof
 Cases_on `lk` >>
 Cases_on `hk` >>
 simp [bounded_root_def, trim_def, restrict_set_def, option_cmp_def,
       option_cmp2_def] >>
 Induct_on `t` >>
 simp [trim_help_lesser_def, trim_help_greater_def, trim_help_middle_def,
       key_ordered_def] >>
 fs [invariant_eq] >>
 rpt gen_tac >>
 strip_tac >>
 every_case_tac >>
 fs [] >>
 simp [to_fmap_def] >>
 fs [SUBMAP_DEF, restrict_domain_def, DRESTRICTED_FUNION, DRESTRICT_FUPDATE] >>
 rw [invariant_def] >>
 rw [FAPPLY_FUPDATE_THM, FUNION_DEF, FLOOKUP_EXT', FLOOKUP_DRESTRICT,
     FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
 rw [] >>
 every_case_tac >>
 fs [flookup_thm, key_ordered_to_fmap, restrict_set_def, option_cmp_def,
     option_cmp2_def] >>
 rfs [key_ordered_to_fmap] >>
 metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm, to_fmap_key_set]
QED

Triviality link_balanced_lem1:
!r rz l.
  balanced r rz ∧
  delta * (l + 1) < r + (rz + 1)
  ⇒
  almost_balancedL (l + (r + 2)) rz
Proof
 fs [almost_balancedL_def, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def, LEFT_ADD_DISTRIB] >>
 CCONTR_TAC >>
 fs [NOT_LESS, LESS_OR_EQ] >>
 fs [MIN_DEF] >>
 rw [] >>
 every_case_tac >>
 fs [NOT_LESS, LESS_OR_EQ]
QED

Triviality link_balanced_lem2:
!r l ly.
  balanced ly l ∧
  ¬(delta * (l + (ly + 1)) < r + 1) ∧
  delta * (r + 1) < l + (ly + 1)
  ⇒
  almost_balancedR ly (SUC (l + r) + 1)
Proof
 fs [ADD1, almost_balancedR_def, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def, LEFT_ADD_DISTRIB] >>
 CCONTR_TAC >>
 fs [NOT_LESS, LESS_OR_EQ] >>
 fs [MIN_DEF] >>
 rw [] >>
 every_case_tac >>
 fs [NOT_LESS, LESS_OR_EQ]
QED

Triviality link_balanced_lem3:
!r l.
  ¬(delta * (l + 1) < r + 1) ∧
  ¬(delta * (r + 1) < l + 1)
  ⇒
  balanced (l + 1) (r + 1)
Proof
 fs [ADD1, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def, LEFT_ADD_DISTRIB] >>
 CCONTR_TAC >>
 fs [NOT_LESS, LESS_OR_EQ, MIN_DEF]
QED

Triviality link2_balanced_lem:
  balanced lx l ∧
  balanced r ry ∧
  delta * (l + lx + 1) < r + ry + 1 ⇒
    almost_balancedL (l + lx + r + 1) ry
Proof
  simp [almost_balancedL_def, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def,
        LEFT_ADD_DISTRIB]
  \\ CCONTR_TAC
  \\ fs [NOT_LESS, LESS_OR_EQ] \\ fs [MIN_DEF]
  \\ rw [] \\ every_case_tac \\ gs [NOT_LESS, LESS_OR_EQ]
QED

Triviality link2_balanced_lem2:
  balanced lx l ∧
  balanced r ry ∧
  ¬(delta * (l + lx + 1) < r + ry + 1) ∧
  delta * (r + ry + 1) < l + lx + 1 ⇒
    almost_balancedR lx (l + r + ry + 1)
Proof
  simp [almost_balancedR_def, balanced_def, TIMES_MIN, LESS_OR_EQ, delta_def,
        LEFT_ADD_DISTRIB]
  \\ CCONTR_TAC
  \\ fs [NOT_LESS, LESS_OR_EQ] \\ fs [MIN_DEF]
  \\ rw [] \\ every_case_tac \\ gs [NOT_LESS, LESS_OR_EQ]
QED

Triviality link_thm:
!k v l r.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less
  ⇒
  invariant cmp (link k v l r) ∧
  to_fmap cmp (link k v l r) =
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)
Proof
 ho_match_mp_tac (fetch "-" "link_ind") >>
 rpt conj_tac >>
 simp [link_def] >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac
 >- (inv_mp_tac insertMin_thm >>
     rw []
     >- metis_tac [key_ordered_to_fmap] >>
     rw [to_fmap_def, FUNION_FEMPTY_1])
 >- (inv_mp_tac insertMax_thm >>
     rw []
     >- metis_tac [key_ordered_to_fmap] >>
     rw [to_fmap_def, FUNION_FEMPTY_2]) >>
 Cases_on `sizeL * delta < sizeR` >>
 simp [] >>
 fs []
 >- (strip_tac >>
     fs [invariant_eq, link_def, key_ordered_def] >>
     inv_mp_tac balanceL_thm >>
     simp [] >>
     rw []
     >- (rfs [key_ordered_to_fmap, to_fmap_def] >>
         rw [] >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
     >- (imp_res_tac size_thm >>
         rw [to_fmap_def] >>
         fs [] >>
         rfs [key_ordered_to_fmap] >>
         simp [FCARD_FUPDATE, key_set_eq] >>
         `key_set cmp k ∉ FDOM (to_fmap cmp ly) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp l) ∧
          key_set cmp ky ∉ FDOM (to_fmap cmp r) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp r)`
                  by metis_tac [cmp_thms, key_set_cmp_thm] >>
         simp [FCARD_DEF] >>
         `DISJOINT (FDOM (to_fmap cmp ly) ∪ FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))`
                       by (rw [DISJOINT_UNION] >>
                           rw [DISJOINT_DEF, EXTENSION] >>
                           metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set]) >>
         rw [CARD_DISJOINT_UNION] >>
         imp_res_tac structure_size_to_fmap >>
         fs [GSYM FCARD_DEF] >>
         metis_tac [link_balanced_lem1, ADD_ASSOC])
     >- to_fmap_tac) >>
 Cases_on `sizeR * delta < sizeL` >>
 simp [] >>
 fs []
 >- (strip_tac >>
     fs [invariant_eq, link_def, key_ordered_def] >>
     inv_mp_tac balanceR_thm >>
     simp [] >>
     rw []
     >- (rfs [key_ordered_to_fmap, to_fmap_def] >>
         rw [] >>
         rw [key_set_cmp_thm] >>
         metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
     >- (imp_res_tac size_thm >>
         rw [to_fmap_def] >>
         fs [] >>
         rfs [key_ordered_to_fmap] >>
         simp [FUNION_FUPDATE_2, FCARD_FUPDATE, key_set_eq] >>
         `key_set cmp k ∉ FDOM (to_fmap cmp rz) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp l) ∧
          key_set cmp kz ∉ FDOM (to_fmap cmp l) ∧
          key_set cmp k ∉ FDOM (to_fmap cmp r)`
                  by metis_tac [cmp_thms, key_set_cmp_thm] >>
         simp [FCARD_DEF] >>
         `DISJOINT (FDOM (to_fmap cmp l) ∪ FDOM (to_fmap cmp r)) (FDOM (to_fmap cmp rz))`
                       by (rw [DISJOINT_UNION] >>
                           rw [DISJOINT_DEF, EXTENSION] >>
                           metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set]) >>
         `DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r))`
                       by (rw [DISJOINT_UNION] >>
                           rw [DISJOINT_DEF, EXTENSION] >>
                           metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set]) >>
         rw [CARD_DISJOINT_UNION] >>
         imp_res_tac structure_size_to_fmap >>
         fs [GSYM FCARD_DEF] >>
         metis_tac [link_balanced_lem2, ADD_ASSOC])
     >- to_fmap_tac)
 >- (simp [bin_def, size_def] >>
     rw [invariant_def, structure_size_def] >>
     fs [invariant_eq, size_def]
     >- metis_tac [link_balanced_lem3, structure_size_thm, ADD_ASSOC] >>
     to_fmap_tac)
QED

Triviality link2_thm:
  ∀l r.
    good_cmp cmp ∧
    invariant cmp l ∧
    invariant cmp r ∧
    key_ordered cmp k l Greater ∧
    key_ordered cmp k r Less ⇒
      invariant cmp (link2 l r) ∧
      to_fmap cmp (link2 l r) = FUNION (to_fmap cmp l) (to_fmap cmp r)
Proof
  ho_match_mp_tac link2_ind \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ gs [link2_def, to_fmap_def]
  \\ strip_tac \\ gs []
  \\ Cases_on ‘sizeL * delta < sizeR’ \\ gs []
  >- (
    gs [invariant_eq, link2_def, key_ordered_def]
    \\ inv_mp_tac balanceL_thm \\ gs [] \\ rw []
    >- (
      gs [key_ordered_to_fmap, to_fmap_def]
      \\ rw [] \\ gs [key_set_cmp_thm]
      \\ metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
    >- (
      imp_res_tac size_thm
      \\ gs [to_fmap_def]
      \\ gs [key_ordered_to_fmap]
      \\ simp [FCARD_FUPDATE]
      \\ ‘key_set cmp k ∉ FDOM (to_fmap cmp r) ∧
          key_set cmp kx ∉ FDOM (to_fmap cmp r)’
        by metis_tac [cmp_thms, key_set_cmp_thm]
      \\ gs [] \\ simp [FCARD_DEF]
      \\ ‘DISJOINT (FDOM (to_fmap cmp lx) ∪ FDOM (to_fmap cmp l))
                   (FDOM (to_fmap cmp r))’
        by (rw [DISJOINT_UNION]
            \\ rw [DISJOINT_DEF, EXTENSION]
            \\ metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
      \\ simp [CARD_DISJOINT_UNION]
      \\ imp_res_tac structure_size_to_fmap
      \\ fs [GSYM FCARD_DEF]
      \\ metis_tac [link2_balanced_lem, ADD_ASSOC])
    \\ to_fmap_tac)
  \\ Cases_on ‘sizeR * delta < sizeL’ \\ gs []
  >- (
    gs [invariant_eq, link2_def, key_ordered_def]
    \\ inv_mp_tac balanceR_thm
    \\ simp [] \\ rw []
    >- (
      gs [key_ordered_to_fmap, to_fmap_def]
      \\ rw [] \\ rw [key_set_cmp_thm]
      \\ metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
    \\ imp_res_tac size_thm
    \\ gs [to_fmap_def]
    \\ gs [key_ordered_to_fmap]
    \\ simp [FCARD_DEF]
    \\ ‘DISJOINT (FDOM (to_fmap cmp l))
                 (key_set cmp ky INSERT FDOM (to_fmap cmp r) ∪
                  FDOM (to_fmap cmp ry))’
      by (rw [DISJOINT_UNION]
          \\ rw [DISJOINT_DEF, EXTENSION]
          \\ metis_tac [cmp_thms, key_set_cmp_thm, to_fmap_key_set])
    \\ simp [CARD_DISJOINT_UNION, AC UNION_COMM UNION_ASSOC]
    \\ imp_res_tac structure_size_to_fmap
    \\ gs [GSYM FCARD_DEF, ADD1]
    \\ metis_tac [link2_balanced_lem2, ADD_ASSOC])
  \\ inv_mp_tac glue_thm \\ gs []
  \\ simp [to_fmap_def, balanced_def, size_def, LESS_OR_EQ, MIN_DEF]
  \\ gs [key_ordered_to_fmap, to_fmap_def]
  \\ metis_tac [key_set_cmp2_thm, to_fmap_key_set, key_set_cmp_thm, cmp_thms]
QED

Triviality filter_lt_help_thm:
!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterLt_help cmp bound t) ∧
  to_fmap cmp (filterLt_help cmp bound t) = restrict_domain cmp NONE (SOME bound) (to_fmap cmp t)
Proof
 Induct_on `t` >>
 simp [to_fmap_def, filterLt_help_def, restrict_domain_union, restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
 rpt gen_tac >>
 strip_tac >>
 Cases_on `cmp k bound` >>
 simp []
 >- (inv_mp_tac link_thm >>
     conj_asm1_tac >>
     rw [] >>
     fs [invariant_eq]
     >- (rfs [key_ordered_to_fmap] >>
         rw [restrict_domain_def]) >>
     rw [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
     to_fmap_tac)
 >- (fs [invariant_eq] >>
     rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
     to_fmap_tac)
 >- (first_x_assum inv_mp_tac >>
     fs [invariant_eq] >>
     rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
     to_fmap_tac)
QED

Triviality filterLt_thm:
!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterLt cmp bound t) ∧
  to_fmap cmp (filterLt cmp bound t) = restrict_domain cmp NONE bound (to_fmap cmp t)
Proof
 Cases_on `bound` >>
 simp [to_fmap_def, filterLt_def, restrict_domain_union, restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def] >>
 rw [] >>
 imp_res_tac filter_lt_help_thm
 >- (rw [FLOOKUP_EXT', FLOOKUP_DRESTRICT] >>
     rw [] >>
     fs [FLOOKUP_DEF] >>
     metis_tac [to_fmap_key_set]) >>
 rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def]
QED

Triviality filter_gt_help_thm:
!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterGt_help cmp bound t) ∧
  to_fmap cmp (filterGt_help cmp bound t) =
    restrict_domain cmp (SOME bound) NONE (to_fmap cmp t)
Proof
 Induct_on `t` >>
 simp [to_fmap_def, filterGt_help_def, restrict_domain_union,
       restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def]>>
 rpt gen_tac >>
 strip_tac >>
 Cases_on `cmp bound k` >>
 simp []
 >- (inv_mp_tac link_thm >>
     conj_asm1_tac >>
     rw [] >>
     fs [invariant_eq]
     >- (rfs [key_ordered_to_fmap] >>
         rw [restrict_domain_def]) >>
     rw [restrict_domain_def,restrict_set_def,option_cmp_def,option_cmp2_def] >>
     to_fmap_tac)
 >- (fs [invariant_eq] >>
     rw [restrict_domain_def,restrict_set_def,option_cmp2_def,option_cmp_def] >>
     to_fmap_tac)
 >- (first_x_assum inv_mp_tac >>
     fs [invariant_eq] >>
     rw [restrict_domain_def,restrict_set_def,option_cmp2_def,option_cmp_def] >>
     to_fmap_tac)
QED

Triviality filterGt_thm:
!cmp bound t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (filterGt cmp bound t) ∧
  to_fmap cmp (filterGt cmp bound t) =
   restrict_domain cmp bound NONE (to_fmap cmp t)
Proof
 Cases_on `bound` >>
 simp [to_fmap_def,filterGt_def,restrict_domain_union,restrict_domain_update] >>
 simp [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def]>>
 rw [] >>
 imp_res_tac filter_gt_help_thm
 >- (rw [FLOOKUP_EXT', FLOOKUP_DRESTRICT] >>
     rw [] >>
     fs [FLOOKUP_DEF] >>
     metis_tac [to_fmap_key_set]) >>
 rw [restrict_domain_def, restrict_set_def, option_cmp2_def, option_cmp_def]
QED

Triviality restrict_domain_partition:
!cmp x l h t1 t2.
  good_cmp cmp ∧
  x ∈ restrict_set cmp l h ∧
  restrict_domain cmp l (SOME x) t2 SUBMAP t1 ∧
  restrict_domain cmp (SOME x) h t1 SUBMAP t2 ∧
  key_set cmp x ∉ FDOM t1 ∧
  key_set cmp x ∉ FDOM t2
  ⇒
  FUNION (restrict_domain cmp l h t1) (restrict_domain cmp l h t2) =
    FUNION (restrict_domain cmp l (SOME x) t1)
           (restrict_domain cmp (SOME x) h t2)
Proof
 rw [restrict_domain_def, FLOOKUP_EXT'] >>
 every_case_tac >>
 rw [] >>
 fs [restrict_set_def] >>
 `h = NONE ∨ ?h'. h = SOME h'` by (Cases_on `h` >> simp[]) >>
 `l = NONE ∨ ?l'. l = SOME l'` by (Cases_on `l` >> simp[]) >>
 fs [option_cmp_def, option_cmp2_def, SUBMAP_DEF, EXTENSION, FDOM_DRESTRICT, FLOOKUP_DEF,
     DRESTRICT_DEF, FAPPLY_FUPDATE_THM] >>
 fmrw [] >>
 metis_tac [cmp_thms, EXTENSION, key_set_eq]
QED

Triviality restrict_domain_union_swap:
 good_cmp cmp
⇒
  a ⊌
  restrict_domain cmp blo (SOME kx) (to_fmap cmp r2) ⊌
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp t1')
  =
  a ⊌
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp t1') ⊌
  restrict_domain cmp blo (SOME kx) (to_fmap cmp r2)
Proof
 rw [restrict_domain_def] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 rw [restrict_set_def, FLOOKUP_EXT'] >>
 fmrw [] >>
 fs [option_cmp_def, option_cmp2_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [cmp_thms, key_set_eq]
QED

Triviality restrict_domain_extend:
  good_cmp cmp ∧
  invariant cmp (Bin s kx x t1 t1') ∧
  kx ∈ restrict_set cmp blo bhi
⇒
  restrict_domain cmp blo (SOME kx) (to_fmap cmp t1) =
  restrict_domain cmp blo bhi (to_fmap cmp t1) ∧
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp t1') =
  restrict_domain cmp blo bhi (to_fmap cmp t1')
Proof
 rw [invariant_eq, restrict_domain_def] >>
 rfs [key_ordered_to_fmap] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 rw [restrict_set_def, FLOOKUP_EXT'] >>
 fmrw [] >>
 fs [option_cmp_def, option_cmp2_def, restrict_set_def] >>
 every_case_tac >>
 rw [FLOOKUP_DEF] >>
 metis_tac [cmp_thms, key_set_eq, key_set_cmp_thm, to_fmap_key_set]
QED

Triviality restrict_domain_combine:
  good_cmp cmp ∧
  key_set cmp kx ≠ k ∧
  kx ∈ restrict_set cmp blo bhi
 ⇒
  FLOOKUP (restrict_domain cmp (SOME kx) bhi (to_fmap cmp r2) ⊌
           restrict_domain cmp blo (SOME kx) (to_fmap cmp r2)) k =
  FLOOKUP (restrict_domain cmp blo bhi (to_fmap cmp r2)) k
Proof
 fmrw [restrict_domain_def] >>
 every_case_tac >>
 rw [] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 fs [restrict_set_def, option_cmp2_def, option_cmp_def, FLOOKUP_DEF] >>
 metis_tac [key_set_eq, cmp_thms, to_fmap_key_set, key_set_cmp_thm]
QED

Definition bounded_all_def:
  (bounded_all cmp lk hk Tip ⇔ T) ∧
  (bounded_all cmp lk hk (Bin s k v t1 t2) ⇔
    k ∈ restrict_set cmp lk hk ∧
    bounded_all cmp lk hk t1 ∧
    bounded_all cmp lk hk t2)
End

Triviality bounded_all_shrink1:
 !t blo bhi.
   good_cmp cmp ∧
   bounded_all cmp blo bhi t ∧
   key_ordered cmp kx t Greater
  ⇒
   bounded_all cmp blo (SOME kx) t
Proof
 Induct_on `t` >>
 rw [bounded_all_def, key_ordered_def]
 >- (Cases_on `blo` >>
     fs [restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct]) >>
 metis_tac []
QED

Triviality bounded_all_shrink2:
  !t blo bhi.
     good_cmp cmp ∧
     bounded_all cmp blo bhi t ∧
     key_ordered cmp kx t Less
    ⇒
     bounded_all cmp (SOME kx) bhi t
Proof
 Induct_on `t` >>
 rw [bounded_all_def, key_ordered_def]
 >- (Cases_on `bhi` >>
     fs [restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct]) >>
 metis_tac []
QED

Triviality bounded_restrict_id:
!t.
  good_cmp cmp ∧
  bounded_all cmp blo bhi t
  ⇒
  restrict_domain cmp blo bhi (to_fmap cmp t) = to_fmap cmp t
Proof
 Induct_on ‘t’ >>
 rw [bounded_all_def, to_fmap_def, restrict_domain_union, restrict_domain_update] >>
 Cases_on `blo` >>
 Cases_on `bhi` >>
 fs [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def]
QED

Triviality restrict_domain_empty:
good_cmp cmp ⇒
  restrict_domain cmp blo (SOME kx)
    (restrict_domain cmp (SOME kx) bhi t) = FEMPTY ∧
  restrict_domain cmp (SOME kx) bhi
    (restrict_domain cmp blo (SOME kx) t) = FEMPTY
Proof
 Cases_on `blo` >>
 Cases_on `bhi` >>
 fmrw [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def, FLOOKUP_EXT'] >>
 metis_tac [good_cmp_def, comparison_distinct, key_set_eq]
QED

Triviality hedgeUnion_thm:
!cmp blo bhi t1 t2.
  good_cmp cmp ∧
  invariant cmp t1 ∧
  invariant cmp t2 ∧
  bounded_all cmp blo bhi t1 ∧
  bounded_root cmp blo bhi t2
  ⇒
  invariant cmp (hedgeUnion cmp blo bhi t1 t2) ∧
  to_fmap cmp (hedgeUnion cmp blo bhi t1 t2) =
     restrict_domain cmp blo bhi (to_fmap cmp t1 ⊌ to_fmap cmp t2)
Proof
 ho_match_mp_tac (fetch "-" "hedgeUnion_ind") >>
 rpt conj_tac >>
 simp [hedgeUnion_def] >>
 rpt conj_tac >>
 rpt gen_tac >>
 strip_tac
 >- rw [to_fmap_def, FUNION_FEMPTY_2, bounded_restrict_id]
 >- (inv_mp_tac link_thm >>
     simp [GSYM CONJ_ASSOC] >>
     inv_mp_tac filterGt_thm >>
     simp [] >>
     fs [invariant_eq] >>
     strip_tac >>
     inv_mp_tac filterLt_thm >>
     simp [] >>
     strip_tac >>
     conj_tac
     >- (rfs [key_ordered_to_fmap, restrict_domain_def] >>
         Cases_on `blo` >>
         fs [restrict_set_def, option_cmp_def, option_cmp2_def]) >>
     conj_tac
     >- (rfs [key_ordered_to_fmap, restrict_domain_def] >>
         Cases_on `bhi` >>
         fs [restrict_set_def, option_cmp_def, option_cmp2_def]) >>
     `restrict_domain cmp blo bhi FEMPTY = FEMPTY` by rw [restrict_domain_def]>>
     rw [to_fmap_def, restrict_domain_union, restrict_domain_update] >>
     fmrw [restrict_domain_def, FLOOKUP_EXT'] >>
     rw [] >>
     Cases_on `blo` >>
     Cases_on `bhi` >>
     fs [restrict_set_def, option_cmp_def, option_cmp2_def, bounded_root_def] >>
     fs [] >>
     rw [FLOOKUP_DEF] >>
     metis_tac [key_ordered_to_fmap, cmp_thms, to_fmap_key_set,key_set_cmp_thm])
 >- (inv_mp_tac insertR_thm >>
     imp_res_tac bounded_restrict_id >>
     rw [restrict_domain_union, to_fmap_def, restrict_domain_update] >>
     rw [restrict_domain_def, FLOOKUP_EXT'] >>
     fmrw [] >>
     every_case_tac >>
     fs [FLOOKUP_DEF, bounded_root_def]) >|
 [qabbrev_tac `r1 = Bin v39 v40 v41 v42 v43` >>
      qabbrev_tac `r2 = Bin v9 v10 v11 Tip r1`,
  qabbrev_tac `r1 = Bin v29 v30 v31 v32 v33` >>
      qabbrev_tac `r2 = Bin v9 v10 v11 r1 v13`] >>
(simp [bounded_all_def] >>
 strip_tac >>
 inv_mp_tac link_thm >>
 `invariant cmp t1'` by metis_tac [invariant_def] >>
 `invariant cmp t1` by metis_tac [invariant_def] >>
 simp [bounded_all_def, GSYM CONJ_ASSOC] >>
 FIRST_X_ASSUM inv_mp_tac >>
 simp [GSYM CONJ_ASSOC] >>
 inv_mp_tac trim_thm >>
 simp [bounded_all_def] >>
 strip_tac >>
 conj_tac
 >- (fs [invariant_eq] >>
     metis_tac [bounded_all_shrink1]) >>
 strip_tac >>
 FIRST_X_ASSUM inv_mp_tac >>
 simp [GSYM CONJ_ASSOC] >>
 inv_mp_tac trim_thm >>
 simp [bounded_all_def] >>
 strip_tac >>
 conj_tac
 >- (fs [invariant_eq] >>
     metis_tac [bounded_all_shrink2]) >>
 strip_tac >>
 qabbrev_tac `m1 = hedgeUnion cmp blo (SOME kx) t1 (trim cmp blo (SOME kx) r2)` >>
 qabbrev_tac `m2 = hedgeUnion cmp (SOME kx) bhi t1' (trim cmp (SOME kx) bhi r2)` >>
 conj_asm1_tac
 >- (rw [key_ordered_to_fmap, restrict_domain_union] >>
     Cases_on `blo` >>
     fs [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct, key_set_cmp_thm]) >>
 conj_asm1_tac
 >- (rw [key_ordered_to_fmap, restrict_domain_union] >>
     Cases_on `bhi` >>
     fs [restrict_domain_def, restrict_set_def, option_cmp_def, option_cmp2_def] >>
     metis_tac [good_cmp_def, comparison_distinct, key_set_cmp_thm]) >>
 rw [restrict_domain_union, restrict_domain_update] >>
 `key_set cmp kx ∉ FDOM (to_fmap cmp m1) ∧ key_set cmp kx ∉ FDOM (to_fmap cmp m2)`
             by metis_tac [key_ordered_to_fmap, cmp_thms, to_fmap_key_set, key_set_cmp_thm] >>
 `restrict_domain cmp blo (SOME kx) (to_fmap cmp m2) SUBMAP (to_fmap cmp m1) ∧
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp m1) SUBMAP (to_fmap cmp m2)`
              by (qunabbrev_tac `m1` >>
                  qunabbrev_tac `m2` >>
                  rw [restrict_domain_union, SUBMAP_DEF, restrict_domain_empty]) >>
 `restrict_domain cmp blo bhi (to_fmap cmp m1) ⊌
  restrict_domain cmp blo bhi (to_fmap cmp m2) =
  restrict_domain cmp blo (SOME kx) (to_fmap cmp m1) ⊌
  restrict_domain cmp (SOME kx) bhi (to_fmap cmp m2)`
              by metis_tac [restrict_domain_partition] >>
 simp [restrict_domain_union, restrict_domain_update, to_fmap_def] >>
 rw [restrict_domain_union_swap] >>
 imp_res_tac restrict_domain_extend >>
 rw [] >>
 simp [FLOOKUP_EXT'] >>
 rw [FLOOKUP_UPDATE] >>
 REWRITE_TAC [GSYM FUNION_ASSOC] >>
 ONCE_REWRITE_TAC [FLOOKUP_FUNION] >>
 every_case_tac >>
 ONCE_REWRITE_TAC [FLOOKUP_FUNION] >>
 every_case_tac >>
 metis_tac [restrict_domain_combine])
QED

Triviality bounded_all_NONE:   ∀cmp t. bounded_all cmp NONE NONE t
Proof
 Induct_on `t` >>
 rw [bounded_all_def, restrict_set_def, option_cmp_def, option_cmp2_def]
QED

val union_thm = Q.store_thm ("union_thm",
`!cmp blo bhi t1 t2.
  good_cmp cmp ∧
  invariant cmp t1 ∧
  invariant cmp t2
  ⇒
  invariant cmp (union cmp t1 t2) ∧
  to_fmap cmp (union cmp t1 t2) = (to_fmap cmp t1 ⊌ to_fmap cmp t2)`,
 Cases_on `t1` >>
 Cases_on `t2` >>
 simp [union_def, to_fmap_def] >>
 gen_tac >>
 strip_tac >>
 inv_mp_tac hedgeUnion_thm >>
 rw [bounded_all_NONE, bounded_root_def, restrict_set_def, option_cmp_def,
     restrict_domain_def, option_cmp2_def, to_fmap_def] >>
 rw [FLOOKUP_EXT'] >>
 fmrw [] >>
 every_case_tac >>
 fs [FLOOKUP_DEF, invariant_eq] >>
 rfs [key_ordered_to_fmap] >>
 metis_tac [cmp_thms, to_fmap_key_set]);

val lookup_union = Q.store_thm("lookup_union",
  `good_cmp cmp ∧ invariant cmp t1 ∧ invariant cmp t2 ⇒
   lookup cmp k (union cmp t1 t2) = case lookup cmp k t1 of
                                      NONE => lookup cmp k t2
                                    | SOME v => SOME v`,
  rw[lookup_thm,union_thm,FLOOKUP_FUNION]);

Triviality hedgeUnionWithKey_thm:
  ∀cmp f blo bhi t1 t2.
    good_cmp cmp ∧
    invariant cmp t1 ∧
    invariant cmp t2 ∧
    bounded_all cmp blo bhi t1 ∧
    bounded_root cmp blo bhi t2 ∧
    (∀k1 k2 x y. cmp k1 k2 = Equal ⇒ f k1 x y = f k2 x y)
  ⇒ invariant cmp (hedgeUnionWithKey cmp f blo bhi t1 t2) ∧
    to_fmap cmp (hedgeUnionWithKey cmp f blo bhi t1 t2) =
      restrict_domain cmp blo bhi
        (FMERGE_WITH_KEY (λks x y. f (CHOICE ks) x y) (to_fmap cmp t1) (to_fmap cmp t2))
Proof
  recInduct hedgeUnionWithKey_ind >> simp[hedgeUnionWithKey_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- rw[to_fmap_def, FUNION_FEMPTY_2, bounded_restrict_id]
  >- (
    inv_mp_tac link_thm >> simp[GSYM CONJ_ASSOC] >>
    inv_mp_tac filterGt_thm >> simp[] >> gvs[invariant_eq] >> strip_tac >>
    inv_mp_tac filterLt_thm >> simp[] >> strip_tac >> rpt conj_tac
    >- gvs[key_ordered_to_fmap, restrict_domain_def]
    >- gvs[key_ordered_to_fmap, restrict_domain_def] >>
    `restrict_domain cmp blo bhi FEMPTY = FEMPTY` by rw [restrict_domain_def] >>
    simp[to_fmap_def, restrict_domain_union, restrict_domain_update] >> strip_tac >>
    fmrw[restrict_domain_def, fmap_eq_flookup] >>
    Cases_on `blo` >> Cases_on `bhi` >>
    gvs[restrict_set_def, option_cmp_def, option_cmp2_def, bounded_root_def] >>
    rw[FLOOKUP_DEF] >>
    gvs[key_ordered_to_fmap] >> res_tac >> imp_res_tac to_fmap_key_set >>
    metis_tac[cmp_thms, key_set_cmp_thm]
    ) >>
  simp[bounded_all_def] >> strip_tac >>
  inv_mp_tac link_thm >> gvs[] >>
  `invariant cmp l` by metis_tac[invariant_def] >>
  `invariant cmp r` by metis_tac[invariant_def] >> gvs[] >>
  qpat_abbrev_tac `tree = Bin _ _ _ _ _` >>
  last_x_assum mp_tac >> impl_tac >> simp[]
  >- (
    inv_mp_tac trim_thm >> simp[] >> strip_tac >>
    irule bounded_all_shrink1 >> simp[PULL_EXISTS] >> goal_assum drule >>
    gvs[invariant_def]
    ) >>
  last_x_assum mp_tac >> impl_tac >> simp[]
  >- (
    inv_mp_tac trim_thm >> simp[] >> strip_tac >>
    irule bounded_all_shrink2 >> simp[PULL_EXISTS] >> goal_assum drule >>
    gvs[invariant_def]
    ) >>
  ntac 2 strip_tac >> simp[] >> conj_tac
  >- (
    gvs[key_ordered_to_fmap, restrict_domain_def, FMERGE_WITH_KEY_DEF] >>
    simp[PULL_EXISTS, restrict_set_def, option_cmp2_def, DISJ_EQ_IMP] >>
    rw[key_set_cmp_def, key_set_def] >> metis_tac[good_cmp_def]
    ) >>
  strip_tac >>
  drule lookup_thm >> disch_then $ qspecl_then [`kx`,`tree`] assume_tac >> gvs[] >>
  simp[to_fmap_def, restrict_domain_FMERGE_WITH_KEY,
       restrict_domain_union, restrict_domain_update] >>
  drule trim_thm >>
  disch_then $ qspecl_then [`tree`,`blo`,`SOME kx`] assume_tac >> gvs[] >>
  drule trim_thm >>
  disch_then $ qspecl_then [`tree`,`SOME kx`,`bhi`] assume_tac >> gvs[] >>
  ntac 15 $ pop_assum kall_tac >> gvs[invariant_eq] >>
  `restrict_domain cmp blo bhi (to_fmap cmp l) =
   restrict_domain cmp blo (SOME kx) (to_fmap cmp l)` by (
    fmrw[restrict_domain_def, fmap_eq_flookup] >>
    gvs[key_ordered_to_fmap, restrict_set_def, option_cmp2_def] >>
    every_case_tac >> gvs[] >>
    rw[FLOOKUP_DEF] >> CCONTR_TAC >> gvs[] >> res_tac
    >- (
      imp_res_tac key_set_cmp_thm >>
      first_x_assum $ qspec_then `x'` assume_tac >> gvs[] >>
      metis_tac[good_cmp_def]
      )
    >- (
      first_x_assum $ qspec_then `x'` assume_tac >>
      Cases_on `bhi` >> gvs[option_cmp2_def] >>
      metis_tac[good_cmp_def]
      )
    ) >>
  `restrict_domain cmp blo bhi (to_fmap cmp r) =
   restrict_domain cmp (SOME kx) bhi (to_fmap cmp r)` by (
    fmrw[restrict_domain_def, fmap_eq_flookup] >>
    gvs[key_ordered_to_fmap, restrict_set_def] >>
    every_case_tac >> gvs[] >>
    rw[FLOOKUP_DEF] >> CCONTR_TAC >> gvs[] >> res_tac
    >- (
      imp_res_tac key_set_cmp_thm >>
      first_x_assum $ qspec_then `x'` assume_tac >> gvs[]
      )
    >- (
      first_x_assum $ qspec_then `x'` assume_tac >>
      Cases_on `blo` >> gvs[option_cmp_def] >>
      metis_tac[good_cmp_def]
      )
    ) >>
  simp[] >>
  ntac 2 $ pop_assum kall_tac >>
  simp[FMERGE_WITH_KEY_FUPDATE] >>
  qmatch_goalsub_abbrev_tac `_ |+ (_, a) = _ |+ (_, b)` >>
  `a = b` by (
    fmrw[Abbr `a`, Abbr `b`, restrict_domain_def] >>
    CASE_TAC >> rw[] >> first_x_assum irule >>
    DEEP_INTRO_TAC CHOICE_INTRO >> simp[key_set_def] >>
    metis_tac[good_cmp_def]) >>
  pop_assum SUBST_ALL_TAC >> ntac 2 $ pop_assum kall_tac >>
  simp[FUPD11_SAME_UPDATE, GSYM fmap_domsub] >>
  rw[fmap_eq_flookup, DOMSUB_FLOOKUP_THM] >> IF_CASES_TAC >> gvs[] >>
  drule $ GSYM restrict_domain_combine >>
  disch_then $ drule_at Any >>
  disch_then $ qspecl_then [`tree`,`x`] assume_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `FLOOKUP (a ⊌ b)` >>
  `∀k. FLOOKUP a k = NONE ∨ FLOOKUP b k = NONE` by (
    rw[] >> Cases_on `FLOOKUP a k` >> Cases_on `FLOOKUP b k` >> gvs[] >>
    gvs[Abbr `a`, Abbr `b`, FLOOKUP_DEF] >>
    gvs[restrict_domain_def, restrict_set_def, option_cmp2_def] >>
    gvs[key_set_eq] >> imp_res_tac good_cmp_thm >> res_tac >> gvs[]) >>
  fmrw[FLOOKUP_FMERGE_WITH_KEY, Abbr `a`, Abbr `b`] >>
  qpat_x_assum `FLOOKUP _ _ = _` kall_tac >>
  first_x_assum $ qspec_then `x` assume_tac >> every_case_tac >> gvs[] >>
  gvs[restrict_domain_def, FLOOKUP_DRESTRICT, restrict_set_def,
      option_cmp2_def, key_set_eq] >>
  imp_res_tac good_cmp_thm >> res_tac >> gvs[]
QED

Theorem unionWithKey_thm:
  ∀cmp f t1 t2.
    good_cmp cmp ∧
    invariant cmp t1 ∧
    invariant cmp t2 ∧
    (∀k1 k2 x y. cmp k1 k2 = Equal ⇒ f k1 x y = f k2 x y)
  ⇒ invariant cmp (unionWithKey cmp f t1 t2) ∧
    to_fmap cmp (unionWithKey cmp f t1 t2) =
      FMERGE_WITH_KEY (λks x y. f (CHOICE ks) x y)
                      (to_fmap cmp t1)
                      (to_fmap cmp t2)
Proof
  Cases_on `t1` >> Cases_on `t2` >> simp[unionWithKey_def, to_fmap_def] >>
  ntac 2 gen_tac >> strip_tac >>
  inv_mp_tac hedgeUnionWithKey_thm >> simp[] >>
  rw[bounded_all_NONE, bounded_root_def, restrict_set_def, option_cmp_def,
     restrict_domain_def, option_cmp2_def, to_fmap_def] >>
  rw[fmap_eq_flookup, FLOOKUP_FMERGE_WITH_KEY, FLOOKUP_DRESTRICT] >>
  IF_CASES_TAC >> gvs[] >> simp[FLOOKUP_UPDATE, FLOOKUP_DEF] >>
  every_case_tac >> gvs[] >> imp_res_tac to_fmap_key_set >>
  rgs[]
QED

Theorem unionWith_thm:
  ∀cmp f t1 t2.
    good_cmp cmp ∧
    invariant cmp t1 ∧
    invariant cmp t2
  ⇒ invariant cmp (unionWith cmp f t1 t2) ∧
    to_fmap cmp (unionWith cmp f t1 t2) =
      FMERGE_WITH_KEY (λks x y. f x y) (to_fmap cmp t1) (to_fmap cmp t2)
Proof
  rpt gen_tac \\ strip_tac
  \\ simp [unionWith_def]
  \\ inv_mp_tac unionWithKey_thm \\ gs []
QED

Theorem lookup_unionWithKey:
  good_cmp cmp ∧ invariant cmp t1 ∧ invariant cmp t2 ∧
  (∀k1 k2 x y. cmp k1 k2 = Equal ⇒ f k1 x y = f k2 x y) ⇒
  lookup cmp k (unionWithKey cmp f t1 t2) =
    case lookup cmp k t1 of
    | NONE => lookup cmp k t2
    | SOME v1 =>
      case lookup cmp k t2 of
      | NONE => SOME v1
      | SOME v2 => SOME $ f k v1 v2
Proof
  rw[lookup_thm, unionWithKey_thm, FLOOKUP_FMERGE_WITH_KEY]
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
  \\ ‘key_set cmp k ≠ {}’
    by gs [EXTENSION, key_set_def, good_cmp_thm, SF SFY_ss]
  \\ drule_then assume_tac CHOICE_DEF
  \\ fs [key_set_def]
QED

Theorem lookup_unionWith:
  good_cmp cmp ∧ invariant cmp t1 ∧ invariant cmp t2 ⇒
  lookup cmp k (unionWith cmp f t1 t2) =
    case lookup cmp k t1 of
    | NONE => lookup cmp k t2
    | SOME v1 =>
      case lookup cmp k t2 of
      | NONE => SOME v1
      | SOME v2 => SOME $ f v1 v2
Proof
  strip_tac \\ simp [unionWith_def, lookup_unionWithKey]
QED

val EXT2 = Q.prove (
`!s1 s2. s1 = s2 ⇔ (!k v. (k,v) ∈ s1 ⇔ (k,v) ∈ s2)`,
 rw [EXTENSION] >>
 EQ_TAC >>
 rw [] >>
 PairCases_on `x` >>
 rw []);

val lift_key_def = Define `
lift_key cmp kvs = IMAGE (\(k,v). (key_set cmp k, v)) kvs`;

Triviality toAscList_helper:
∀cmp l t.
  good_cmp cmp ∧
  invariant cmp t ∧
  SORTED (λ(x,y) (x',y'). cmp x x' = Less) l ∧
  (∀k1 v1 k2 v2.
     MEM (k1,v1) l ∧ FLOOKUP (to_fmap cmp t) (key_set cmp k2) = SOME v2 ⇒
     cmp k2 k1 = Less)
  ⇒
  SORTED (λ(x,y) (x',y'). cmp x x' = Less)
         (foldrWithKey (λk x xs. (k,x)::xs) l t) ∧
  lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t)) =
    set (fmap_to_alist (to_fmap cmp t)) ∪ lift_key cmp (set l)
Proof
 Induct_on `t` >>
 simp [foldrWithKey_def, to_fmap_def] >>
 fs [invariant_eq, EXT2] >>
 rpt gen_tac >>
 strip_tac >>
 simp [FLOOKUP_UPDATE, FLOOKUP_FUNION, PULL_FORALL] >>
 rpt gen_tac >>
 first_x_assum (qspecl_then [`cmp`, `l`] mp_tac) >>
 first_x_assum
   (qspecl_then[‘cmp’,‘(k,v)::foldrWithKey (λk x xs. (k,x)::xs) l t'’] mp_tac)>>
 simp [] >>
 strip_tac >>
 strip_tac >>
 fs [FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
 ‘SORTED (λ(x,y) (x',y'). cmp x x' = Less)
         (foldrWithKey (λk x xs. (k,x)::xs) l t') ∧
  ∀k v.
     (k,v) ∈ lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t')) ⇔
     FLOOKUP (to_fmap cmp t') k = SOME v ∨ (k,v) ∈ lift_key cmp (set l)’
   by (first_x_assum match_mp_tac >>
       rw [] >>
       last_x_assum match_mp_tac >>
       rw []
       >- metis_tac [] >>
       qexists_tac `v1` >>
       rw [] >>
       qexists_tac `v2` >>
       rw [] >>
       every_case_tac >>
       fs [DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
       metis_tac []) >>
 ‘SORTED (λ(x,y) (x',y'). cmp x x' = Less)
         (foldrWithKey (λk x xs. (k,x)::xs)
            ((k,v)::foldrWithKey (λk x xs. (k,x)::xs) l t') t) ∧
  ∀k' v'.
    (k',v') ∈
     lift_key cmp
        (set (foldrWithKey (λk x xs. (k,x)::xs)
                           ((k,v)::foldrWithKey (λk x xs. (k,x)::xs) l t') t))
   ⇔
    FLOOKUP (to_fmap cmp t) k' = SOME v' ∨
    (k',v') ∈ lift_key cmp
                ((k,v) INSERT set (foldrWithKey (λk x xs. (k,x)::xs) l t'))’
   by (first_x_assum match_mp_tac >>
       simp [good_cmp_trans, SORTED_EQ, FORALL_PROD] >>
       rw []
       >- (‘(key_set cmp p_1, p_2) ∈
              lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t'))’
             by (fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >> metis_tac []) >>
           rfs [FLOOKUP_DEF] >>
           rfs [key_ordered_to_fmap]
           >- metis_tac [cmp_thms, key_set_cmp_thm] >>
           fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
           metis_tac [cmp_thms, key_set_eq])
       >- (rfs [key_ordered_to_fmap, FLOOKUP_DEF] >>
           metis_tac [cmp_thms, key_set_cmp_thm])
       >- (‘(key_set cmp k1, v1) ∈
              lift_key cmp (set (foldrWithKey (λk x xs. (k,x)::xs) l t'))’
             by (fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >> metis_tac []) >>
           rfs [FLOOKUP_DEF] >>
           rfs [key_ordered_to_fmap]
           >- metis_tac [cmp_thms, key_set_cmp_thm] >>
           fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
           metis_tac [cmp_thms, key_set_cmp_thm, key_set_eq])) >>
 simp [] >>
 eq_tac >>
 rw [] >>
 fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
 every_case_tac >>
 rw [] >>
 fs [lift_key_def, LAMBDA_PROD, EXISTS_PROD] >>
 metis_tac []
QED

val toAscList_thm = Q.store_thm ("toAscList_thm",
`!cmp t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  SORTED (\(x,y) (x',y'). cmp x x' = Less) (toAscList t) ∧
  lift_key cmp (set (toAscList t)) = set (fmap_to_alist (to_fmap cmp t))`,
 rpt gen_tac >>
 strip_tac >>
 qspecl_then [`cmp`, `[]`, `t`] mp_tac toAscList_helper >>
 simp [toAscList_def, lift_key_def]);

(* some useful specialisations of the above theorem *)

val MAP_FST_toAscList = Q.store_thm("MAP_FST_toAscList",
  `good_cmp cmp ∧ invariant cmp t ⇒
   SORTED (λx y. cmp x y = Less) (MAP FST (toAscList t)) ∧
   FDOM (to_fmap cmp t) = IMAGE (key_set cmp) (set (MAP FST (toAscList t)))`,
  rw[] \\ imp_res_tac toAscList_thm
  >- (
    qmatch_goalsub_abbrev_tac`SORTED R` \\
    imp_res_tac comparisonTheory.good_cmp_trans \\
    `transitive R` by (
      fs[relationTheory.transitive_def,FORALL_PROD,Abbr`R`] \\
      metis_tac[] ) \\
    rw[sorted_map] \\
    rw[Abbr`R`,relationTheory.inv_image_def,LAMBDA_PROD] ) \\
  fs[Once EXTENSION,lift_key_def,MEM_MAP,EXISTS_PROD,FORALL_PROD,FLOOKUP_DEF] \\
  metis_tac[]);

val MEM_toAscList = Q.store_thm("MEM_toAscList",
  `good_cmp cmp ∧ invariant cmp t ∧ MEM (k,v) (toAscList t) ⇒
   FLOOKUP (to_fmap cmp t) (key_set cmp k) = SOME v`,
  rw[] \\
  imp_res_tac toAscList_thm \\
  `(key_set cmp k,v) ∈ lift_key cmp (set (toAscList t))`
  by (simp_tac std_ss [lift_key_def] \\ simp[EXISTS_PROD] \\ metis_tac[])
  \\ rfs[]);

Theorem ALOOKUP_toAscList:
  good_cmp cmp /\ invariant cmp t /\ (!x y. cmp x y = Equal <=> x = y) ==>
  ALOOKUP (toAscList t) k = lookup cmp k t
Proof
  rw []
  \\ imp_res_tac toAscList_thm
  \\ Cases_on `lookup cmp k t`
  >- (
    Cases_on `ALOOKUP (toAscList t) k` \\ simp []
    \\ imp_res_tac ALOOKUP_MEM
    \\ imp_res_tac MEM_toAscList
    \\ rfs [lookup_thm]
  )
  >- (
    fs [lift_key_def, EXISTS_PROD, pred_setTheory.EXTENSION]
    \\ first_x_assum (qspec_then `(key_set cmp k, x)` mp_tac)
    \\ rfs [lookup_thm, key_set_eq]
    \\ metis_tac [comparisonTheory.good_cmp_Less_irrefl_trans,
        MAP_FST_toAscList, sortingTheory.SORTED_ALL_DISTINCT,
        ALOOKUP_ALL_DISTINCT_MEM]
  )
QED

val compare_good_cmp = Q.store_thm ("compare_good_cmp",
`!cmp1 cmp2. good_cmp cmp1 ∧ good_cmp cmp2 ⇒ good_cmp (compare cmp1 cmp2)`,
 rw [] >>
 imp_res_tac pair_cmp_good >>
 imp_res_tac list_cmp_good >>
 rpt (pop_assum mp_tac) >>
 REWRITE_TAC [good_cmp_def, compare_def] >>
 metis_tac []);

val compare_thm1 = Q.prove (
`!cmp1 cmp2 t1 t2.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  invariant cmp1 t1 ∧
  invariant cmp1 t2 ∧
  compare cmp1 cmp2 t1 t2 = Equal
  ⇒
  fmap_rel (\x y. cmp2 x y = Equal) (to_fmap cmp1 t1) (to_fmap cmp1 t2)`,
 rw [compare_def, fmap_rel_OPTREL_FLOOKUP, OPTREL_def] >>
 imp_res_tac toAscList_thm >>
 fs [lift_key_def, list_cmp_equal_list_rel, pair_cmp_def] >>
 fs [key_set_def, EXTENSION, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD] >>
 fs [LIST_REL_EL_EQN] >>
 pop_assum (mp_tac o GSYM) >>
 pop_assum (mp_tac o GSYM) >>
 rw [] >>
 Cases_on `FLOOKUP (to_fmap cmp1 t1) k` >>
 rw []
 >- (disj1_tac >>
     Cases_on `FLOOKUP (to_fmap cmp1 t2) k` >>
     fs []  >>
     rfs [] >>
     fs [MEM_EL] >>
     res_tac >>
     Cases_on `EL n (toAscList t1)` >>
     Cases_on `EL n (toAscList t2)` >>
     fs [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     first_x_assum (qspecl_then [`k`] mp_tac) >>
     strip_tac >>
     rfs [] >>
     pop_assum (qspecl_then [`r`, `q`] mp_tac) >>
     rw [] >>
     metis_tac [NOT_SOME_NONE, cmp_thms])
 >- (rfs [] >>
     fs [MEM_EL] >>
     rfs [] >>
     res_tac >>
     Cases_on `EL n (toAscList t1)` >>
     Cases_on `EL n (toAscList t2)` >>
     fs [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     MAP_EVERY qexists_tac [`r`, `r'`] >>
     rw []
     >- metis_tac [] >>
     qexists_tac `q'` >>
     rw [] >>
     metis_tac [cmp_thms]));
val _ = print "Proved compare_thm1";


val NONE_lem = Q.prove (
`x = NONE ⇔ ¬?y. x = SOME y`,
 Cases_on `x` >>
 rw []);

val pair_cmp_lem = Q.prove (
`!cmp1 cmp2. pair_cmp cmp1 cmp2 (x1,x2) (y1,y2) = Equal ⇔ cmp1 x1 y1 = Equal ∧ cmp2 x2 y2 = Equal`,
 rw [pair_cmp_def] >>
 every_case_tac);

val strict_sorted_unique = Q.prove (
`!cmp l x1 y1 x2 y2.
  good_cmp cmp ∧
  SORTED (λ(x,y) (x',y'). cmp x x' = Less) l ∧
  MEM (x1,y1) l ∧
  MEM (x2,y2) l ∧
  cmp x1 x2 = Equal
  ⇒
  x1 = x2 ∧ y1 = y2`,
 Induct_on `l` >>
 rw [] >>
 `transitive (λ(x,y) (x',y'). cmp x x' = Less)` by metis_tac [good_cmp_trans] >>
 fs [SORTED_EQ, LAMBDA_PROD, FORALL_PROD]
 >- metis_tac [cmp_thms]
 >- metis_tac [cmp_thms]
 >- metis_tac [cmp_thms]
 >- metis_tac [cmp_thms] >>
 Cases_on `h` >>
 fs [] >>
 res_tac);
val _ = print "Proved strict_sorted_unique\n"

val strict_sorted_eq_el = Q.prove (
`!cmp l m n.
  good_cmp cmp ∧
  SORTED (λ(x,y) (x',y'). cmp x x' = Less) l ∧
  cmp (FST (EL m l)) (FST (EL n l)) = Equal ∧
  m < LENGTH l ∧
  n < LENGTH l
  ⇒
  m = n`,
 Induct_on `l` >>
 rw [] >>
 `transitive (λ(x,y) (x',y'). cmp x x' = Less)` by metis_tac [good_cmp_trans] >>
 fs [SORTED_EQ, LAMBDA_PROD, FORALL_PROD] >>
 Cases_on `h` >>
 fs [] >>
 Cases_on `0 < n` >>
 Cases_on `0 < m` >>
 fs [rich_listTheory.EL_CONS] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 rw []
 >- (res_tac >>
     full_simp_tac (srw_ss()++ARITH_ss) [])
 >- (`PRE n < LENGTH l` by decide_tac >>
     `MEM (EL (PRE n) l) l` by metis_tac [MEM_EL] >>
     Cases_on `EL (PRE n) l` >>
     fs [] >>
     metis_tac [cmp_thms])
 >- (`PRE m < LENGTH l` by decide_tac >>
     `MEM (EL (PRE m) l) l` by metis_tac [MEM_EL] >>
     Cases_on `EL (PRE m) l` >>
     fs [] >>
     metis_tac [cmp_thms]));
val _ = print "Proved strict_sorted_eq_el\n";

val compare_lem2 = Q.prove (
`!cmp1 cmp2 n l1 l2.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  (∀k.
    (∀y p_1' y' p_1''.
       (k ≠ key_set cmp1 p_1' ∨ ¬MEM (p_1',y) l1) ∧
       (k ≠ key_set cmp1 p_1'' ∨ ¬MEM (p_1'',y') l2)) ∨
    ∃x y p_1' p_1''.
      (k = key_set cmp1 p_1' ∧ MEM (p_1',x) l1) ∧
      (k = key_set cmp1 p_1'' ∧ MEM (p_1'',y) l2) ∧ cmp2 x y = Equal) ∧
  SORTED (λ(x,y) (x',y'). cmp1 x x' = Less) l2 ∧
  SORTED (λ(x,y) (x',y'). cmp1 x x' = Less) l1 ∧
  n ≤ LENGTH l1 ∧
  n ≤ LENGTH l2 ∧
  LIST_REL (λ(p1,p2) (p1',p2'). pair_cmp cmp1 cmp2 (p1,p2) (p1',p2') = Equal)
    (TAKE n l1) (TAKE n l2) ∧
  n ≠ LENGTH l1
  ⇒
  n ≠ LENGTH l2 ∧
  (λ(p1,p2) (p1',p2'). pair_cmp cmp1 cmp2 (p1,p2) (p1',p2') = Equal)
    (EL n l1) (EL n l2)`,
 rpt GEN_TAC >>
 rpt DISCH_TAC >>
 fs [] >>
 `?kn1 vn1. EL n l1 = (kn1,vn1)` by metis_tac [pair_CASES] >>
 simp [] >>
 `?kn2 vn2. MEM (kn2,vn2) l2 ∧ cmp1 kn1 kn2 = Equal ∧ cmp2 vn1 vn2 = Equal`
        by (first_assum (qspecl_then [`key_set cmp1 kn1`] assume_tac) >>
            `MEM (EL n l1) l1` by metis_tac [PAIR, rich_listTheory.EL_MEM, LESS_OR_EQ] >>
            fs [] >>
            rfs [key_set_eq]
            >- metis_tac [PAIR, cmp_thms] >>
            `p_1' = kn1 ∧ x = vn1`
                       by (match_mp_tac strict_sorted_unique >>
                           rw [] >>
                           metis_tac [cmp_thms]) >>
            rw [] >>
            metis_tac []) >>
 fs [MEM_EL] >>
 `n' < n ∨ n = n' ∨ n < n'` by decide_tac >>
 fs []
 >- (fs [LIST_REL_EL_EQN] >>
     first_x_assum (qspecl_then [`n'`] mp_tac) >>
     simp [rich_listTheory.EL_TAKE] >>
     DISCH_TAC >>
     fs [] >>
     Cases_on `EL n' l1` >>
     Cases_on `EL n' l2` >>
     fs [pair_cmp_lem] >>
     `n' < LENGTH l1 ∧ n < LENGTH l1` by decide_tac >>
     imp_res_tac strict_sorted_eq_el >>
     `n' = n` by metis_tac [FST, PAIR, cmp_thms] >>
     fs [])
 >- (rw [pair_cmp_lem] >>
     Cases_on `EL n l2` >>
     rw [] >>
     metis_tac [])
 >- (`?kn3 vn3. EL n l2 = (kn3,vn3)` by metis_tac [pair_CASES] >>
     simp [] >>
     `?kn4 vn4. MEM (kn4,vn4) l1 ∧ cmp1 kn3 kn4 = Equal ∧ cmp2 vn3 vn4 = Equal`
        by (first_assum (qspecl_then [`key_set cmp1 kn3`] assume_tac) >>
            `n < LENGTH l2` by decide_tac >>
            `n < LENGTH l1` by decide_tac >>
            `MEM (EL n l2) l2` by metis_tac [PAIR, rich_listTheory.EL_MEM, LESS_OR_EQ] >>
            fs [] >>
            rfs [key_set_eq] >>
            `n < LENGTH l2` by decide_tac >>
            `n < LENGTH l1` by decide_tac
            >- metis_tac [PAIR, cmp_thms] >>
            rw [] >>
            `p_1'' = kn3 ∧ y = vn3`
                       by (match_mp_tac strict_sorted_unique >>
                           rw [] >>
                           metis_tac [rich_listTheory.EL_MEM, cmp_thms]) >>
            rw [] >>
            MAP_EVERY qexists_tac [`p_1'`, `x`] >>
            rw [rich_listTheory.EL_MEM] >>
            metis_tac [cmp_thms]) >>
     fs [MEM_EL] >>
     `n < n'' ∨ n = n'' ∨ n'' < n` by decide_tac >>
     fs [] >>
     `cmp1 kn3 kn2 = Less`
              by (`transitive (λ(x,y) (x',y'). cmp1 x x' = Less)` by metis_tac [good_cmp_trans] >>
                  `(λ(x,y) (x',y'). cmp1 x x' = Less) (EL n l2) (EL n' l2)`
                            by metis_tac [SORTED_EL_LESS] >>
                  rfs [] >>
                  Cases_on `EL n' l2` >>
                  fs [])
     >- (`cmp1 kn1 kn4 = Less`
                  by (`transitive (λ(x,y) (x',y'). cmp1 x x' = Less)` by metis_tac [good_cmp_trans] >>
                      `(λ(x,y) (x',y'). cmp1 x x' = Less) (EL n l1) (EL n'' l1)`
                                by metis_tac [SORTED_EL_LESS] >>
                      rfs [] >>
                      Cases_on `EL n'' l1` >>
                      fs []) >>
         metis_tac [cmp_thms])
     >- (rw [] >>
         rfs [] >>
         metis_tac [cmp_thms])
     >- (fs [LIST_REL_EL_EQN] >>
         first_x_assum (qspecl_then [`n''`] mp_tac) >>
         simp [rich_listTheory.EL_TAKE] >>
         DISCH_TAC >>
         fs [] >>
         Cases_on `EL n'' l1` >>
         Cases_on `EL n'' l2` >>
         fs [pair_cmp_lem] >>
         rfs [] >>
         `n < LENGTH l2` by decide_tac >>
         `cmp1 kn1 kn4 = Less`
                  by (`transitive (λ(x,y) (x',y'). cmp1 x x' = Less)` by metis_tac [good_cmp_trans] >>
                      `(λ(x,y) (x',y'). cmp1 x x' = Less) (EL n'' l2) (EL n l2)`
                                by metis_tac [SORTED_EL_LESS] >>
                      rfs [] >>
                      Cases_on `EL n'' l2` >>
                      fs [] >>
                      metis_tac [cmp_thms]) >>
         metis_tac [cmp_thms])));
val _ = print "Proved compare_lem2\n";

val compare_thm2 = Q.prove (
`!cmp1 cmp2 t1 t2.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  invariant cmp1 t1 ∧
  invariant cmp1 t2 ∧
  fmap_rel (\x y. cmp2 x y = Equal) (to_fmap cmp1 t1) (to_fmap cmp1 t2)
  ⇒
  compare cmp1 cmp2 t1 t2 = Equal`,
 rw [compare_def, fmap_rel_OPTREL_FLOOKUP, OPTREL_def, list_cmp_equal_list_rel] >>
 imp_res_tac toAscList_thm >>
 fs [EXTENSION] >>
 simp [] >>
 fs [lift_key_def, PULL_EXISTS, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD] >>
 pop_assum (mp_tac o GSYM) >>
 pop_assum (mp_tac o GSYM) >>
 DISCH_TAC >>
 DISCH_TAC >>
 fs [NONE_lem] >>
 ntac 3 (pop_assum (fn _ => all_tac)) >>
 pop_assum mp_tac >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 pop_assum mp_tac >>
 ntac 2 (pop_assum (fn _ => all_tac)) >>
 Q.SPEC_TAC (`toAscList t1`, `l1`) >>
 Q.SPEC_TAC (`toAscList t2`, `l2`) >>
 fs [PULL_FORALL, PULL_EXISTS] >>
 rw [] >>
 ONCE_REWRITE_TAC [list_rel_thm] >>
 gen_tac >>
 DISCH_TAC >>
 fs []
 >- (match_mp_tac compare_lem2 >>
     rw [])
 >- (`n ≠ LENGTH l1 ∧ (λ(p1,p2) (p1',p2'). pair_cmp cmp1 cmp2 (p1,p2) (p1',p2') = Equal) (EL n l2) (EL n l1)`
            by (match_mp_tac compare_lem2 >>
                rw []
                >- (first_x_assum (qspecl_then [`k`] mp_tac) >>
                    rw [] >>
                    metis_tac [good_cmp_def])
                >- (match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] (GEN_ALL EVERY2_sym)) >>
                    qexists_tac `(λ(p1,p2) (p1',p2'). pair_cmp cmp1 cmp2 (p1,p2) (p1',p2') = Equal)` >>
                    rw [] >>
                    PairCases_on `y'` >>
                    PairCases_on `x'` >>
                    fs [] >>
                    metis_tac [good_cmp_def, pair_cmp_good])) >>
     Cases_on `EL n l1` >>
     Cases_on `EL n l2` >>
     fs [] >>
     metis_tac [good_cmp_def, pair_cmp_good]));
val _ = print "Proved compare_thm2\n";

val compare_thm = Q.store_thm ("compare_thm",
`!cmp1 cmp2 t1 t2.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  invariant cmp1 t1 ∧
  invariant cmp1 t2
  ⇒
  (compare cmp1 cmp2 t1 t2 = Equal
   ⇔
   fmap_rel (\x y. cmp2 x y = Equal) (to_fmap cmp1 t1) (to_fmap cmp1 t2))`,
 metis_tac [compare_thm1, compare_thm2]);

Theorem mapWithKey_thm:
  ∀t.
    good_cmp cmp ∧
    invariant cmp t ∧
    (∀k1 k2 x y. cmp k1 k2 = Equal ⇒ f k1 x = f k2 x)
    ⇒
    invariant cmp (mapWithKey f t) ∧
    to_fmap cmp (mapWithKey f t) = FMAP_MAP2 (λ(ks,v). f (CHOICE ks) v)
                                             (to_fmap cmp t)
Proof
 Induct_on `t` >>
 simp [mapWithKey_def, to_fmap_def]
 >- rw [invariant_def, FMAP_MAP2_FEMPTY] >>
 rpt gen_tac >>
 strip_tac >>
 simp [invariant_def, GSYM CONJ_ASSOC] >>
 inv_to_front_tac ``invariant`` >>
 first_x_assum inv_mp_tac >>
 simp [] >>
 fs [invariant_eq] >>
 strip_tac >>
 imp_res_tac (GSYM structure_size_thm) >>
 imp_res_tac size_thm >>
 simp [FCARD_DEF] >>
 rw [FMAP_MAP2_THM]
 >- rfs [key_ordered_to_fmap, FMAP_MAP2_THM]
 >- rfs [key_ordered_to_fmap, FMAP_MAP2_THM]
 >- fs [FCARD_DEF, FMAP_MAP2_THM]
 >- (
  fmrw [FLOOKUP_EXT'] >>
  fmrw [FLOOKUP_FMAP_MAP2, DOMSUB_FLOOKUP_THM] >>
  every_case_tac >> fs [] >>
  ‘key_set cmp k ≠ {}’
    by (gs [EXTENSION, key_set_def]
        \\ fs [good_cmp_thm]
        \\ first_assum (irule_at Any)) >>
  drule_then assume_tac CHOICE_DEF >>
  fs [key_set_def])
QED

Theorem map_thm:
  ∀t.
    good_cmp cmp ∧
    invariant cmp t
    ⇒
    invariant cmp (map f t) ∧
    to_fmap cmp (map f t) = f o_f to_fmap cmp t
Proof
  rw [map_def, mapWithKey_thm, FMAP_MAP2_def, FLOOKUP_EXT, FUN_EQ_THM,
      FLOOKUP_FUN_FMAP, FLOOKUP_o_f, CaseEq "option", flookup_thm]
QED

val splitLookup_thm = Q.store_thm ("splitLookup_thm",
`!t lt v gt.
  good_cmp cmp ∧
  invariant cmp t ∧
  (lt,v,gt) = splitLookup cmp k t
  ⇒
  invariant cmp lt ∧
  invariant cmp gt ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp k) = v ∧
  key_ordered cmp k lt Greater ∧
  key_ordered cmp k gt Less ∧
  to_fmap cmp t =
    case v of
       | NONE => FUNION (to_fmap cmp lt) (to_fmap cmp gt)
       | SOME v => (FUNION (to_fmap cmp lt) (to_fmap cmp gt)) |+ (key_set cmp k, v)`,
 Induct_on `t` >>
 simp [splitLookup_def, to_fmap_def, key_ordered_to_fmap] >>
 rpt gen_tac >>
 strip_tac >>
 Cases_on `cmp k k'` >>
 fs []
 >- (`?lt v gt. splitLookup cmp k t = (lt,v,gt)` by metis_tac [pair_CASES] >>
     fs [] >>
     last_x_assum inv_mp_tac >>
     simp [] >>
     fs [invariant_eq] >>
     strip_tac >>
     inv_mp_tac link_thm >>
     simp [] >>
     conj_asm1_tac
     >- (rfs [key_ordered_to_fmap] >>
         rw [] >>
         first_x_assum match_mp_tac >>
         rw [] >>
         every_case_tac >>
         fs []) >>
     strip_tac >>
     Cases_on `v''` >>
     fs [] >>
     fmrw [] >>
     rfs [FLOOKUP_FUNION] >>
     every_case_tac >>
     fs [] >>
     TRY (match_mp_tac FUPDATE_COMMUTES) >>
     rfs [key_ordered_to_fmap, flookup_thm] >>
     res_tac >>
     metis_tac [cmp_thms, key_set_cmp_def, key_set_cmp_thm])
 >- (fs [invariant_eq] >>
     fmrw [key_set_eq] >>
     rfs [key_ordered_to_fmap] >>
     res_tac >>
     fs [key_set_cmp_def] >>
     fmrw [FLOOKUP_EXT'] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     rfs [key_set_eq] >>
     metis_tac [cmp_thms])
 >- (`?lt v gt. splitLookup cmp k t' = (lt,v,gt)` by metis_tac [pair_CASES] >>
     fs [] >>
     fs [invariant_eq] >>
     inv_mp_tac link_thm >>
     simp [] >>
     conj_asm1_tac
     >- (rfs [key_ordered_to_fmap] >>
         rw [] >>
         first_x_assum match_mp_tac >>
         rw [] >>
         every_case_tac >>
         fs []) >>
     strip_tac >>
     Cases_on `v''` >>
     fs [] >>
     fmrw [] >>
     rfs [FLOOKUP_FUNION] >>
     every_case_tac >>
     fs [] >>
     TRY (match_mp_tac FUPDATE_COMMUTES) >>
     rfs [key_ordered_to_fmap, flookup_thm] >>
     fs [key_ordered_to_fmap, flookup_thm] >>
     res_tac >>
     metis_tac [cmp_thms, key_set_cmp_def, key_set_cmp_thm]));

val submap'_thm = Q.prove (
`!cmp f t1 t2.
  good_cmp cmp ∧
  invariant cmp t1 ∧
  invariant cmp t2
  ⇒
  (submap' cmp f t1 t2 ⇔ !k v. lookup cmp k t1 = SOME v ⇒ ?v'. lookup cmp k t2 = SOME v' ∧ f v v')`,
 ho_match_mp_tac (fetch "-" "submap'_ind") >>
 rpt conj_tac
 >- rw [lookup_def, submap'_def]
 >- (rw [lookup_def, submap'_def, invariant_eq] >>
     qexists_tac `v11` >>
     qexists_tac `v12` >>
     every_case_tac >>
     fs [] >>
     metis_tac [cmp_thms]) >>
 rw [] >>
 qabbrev_tac `t = Bin v20 v21 v22 v23 v24` >>
 `?lt v gt. splitLookup cmp kx t = (lt,v,gt)` by metis_tac [pair_CASES] >>
 fs [] >>
 `invariant cmp lt ∧ invariant cmp gt ∧
  FLOOKUP (to_fmap cmp t) (key_set cmp kx) = v ∧
  key_ordered cmp kx lt Greater ∧ key_ordered cmp kx gt Less ∧
  to_fmap cmp t =
  case v of
    NONE => to_fmap cmp lt ⊌ to_fmap cmp gt
  | SOME v' => (to_fmap cmp lt ⊌ to_fmap cmp gt) |+ (key_set cmp kx,v')`
                 by metis_tac [splitLookup_thm] >>
 unabbrev_all_tac >>
 Cases_on `v` >>
 fs []
 >- (rw [submap'_def, lookup_def] >>
     qexists_tac `kx` >>
     qexists_tac `x` >>
     rw []
     >- metis_tac [cmp_thms] >>
     every_case_tac >>
     fs [] >>
     CCONTR_TAC >>
     fs [] >>
     imp_res_tac lookup_thm >>
     fs [lookup_def, to_fmap_def] >>
     metis_tac [cmp_thms, NOT_SOME_NONE])
 >- (simp [submap'_def] >>
     qabbrev_tac `t = Bin v20 v21 v22 v23 v24` >>
     pop_assum (fn _ => all_tac) >>
     fs [invariant_eq] >>
     rw [lookup_def] >>
     eq_tac >>
     simp []
     >- (rw [] >>
         imp_res_tac lookup_thm >>
         rw [FLOOKUP_UPDATE] >>
         rfs [key_set_eq] >>
         fs []
         >- (`cmp k kx = Equal` by metis_tac [cmp_thms] >>
             fs []) >>
         rw [FLOOKUP_FUNION] >>
         Cases_on `cmp k kx` >>
         fs [] >>
         res_tac
         >- (qexists_tac `v''` >>
             rw [])
         >- metis_tac [cmp_thms]
         >- (rfs [key_ordered_to_fmap] >>
             `FLOOKUP (to_fmap cmp lt) (key_set cmp k) = NONE`
                       by (fs [FLOOKUP_DEF] >>
                           CCONTR_TAC >>
                           fs [] >>
                           res_tac >>
                           fs [key_set_cmp_def, key_set_def] >>
                           metis_tac [cmp_thms]) >>
             rw [])) >>
     rw []
     >- (first_assum (qspecl_then [`kx`, `x`] assume_tac) >>
         every_case_tac >>
         fs []
         >- metis_tac [cmp_thms]
         >- (imp_res_tac lookup_thm >>
             fs [] >>
             rfs [] >>
             rw [])
         >- metis_tac [cmp_thms])
     >- (imp_res_tac lookup_thm >>
         fs [] >>
         rfs [FLOOKUP_UPDATE] >>
         rw [] >>
         last_assum (qspecl_then [`k`] assume_tac) >>
         Cases_on `cmp k kx` >>
         fs [] >>
         rfs [key_set_eq]
         >- (`cmp kx k ≠ Equal` by metis_tac [cmp_thms] >>
             fs [FLOOKUP_FUNION] >>
             Cases_on `FLOOKUP (to_fmap cmp lt) (key_set cmp k)` >>
             fs [FLOOKUP_DEF] >>
             rfs [key_ordered_to_fmap] >>
             res_tac >>
             fs [key_set_cmp_def, key_set_def] >>
             metis_tac [cmp_thms])
         >- (`cmp kx k = Equal` by metis_tac [cmp_thms] >>
             fs [FLOOKUP_DEF] >>
             rfs [key_ordered_to_fmap] >>
             res_tac >>
             fs [key_set_cmp_def, key_set_def] >>
             metis_tac [cmp_thms])
         >- (`cmp kx k ≠ Equal` by metis_tac [cmp_thms] >>
             fs [FLOOKUP_DEF] >>
             rfs [key_ordered_to_fmap] >>
             res_tac >>
             fs [key_set_cmp_def, key_set_def] >>
             metis_tac [cmp_thms]))
     >- (imp_res_tac lookup_thm >>
         fs [] >>
         rfs [FLOOKUP_UPDATE] >>
         rw [] >>
         last_assum (qspecl_then [`k`] assume_tac) >>
         Cases_on `cmp k kx` >>
         fs [] >>
         rfs [key_set_eq]
         >- (`cmp kx k ≠ Equal` by metis_tac [cmp_thms] >>
             fs [FLOOKUP_DEF] >>
             rfs [key_ordered_to_fmap] >>
             res_tac >>
             fs [key_set_cmp_def, key_set_def] >>
             metis_tac [cmp_thms])
         >- (`cmp kx k = Equal` by metis_tac [cmp_thms] >>
             fs [FLOOKUP_DEF] >>
             rfs [key_ordered_to_fmap] >>
             res_tac >>
             fs [key_set_cmp_def, key_set_def] >>
             metis_tac [cmp_thms])
         >- (`cmp kx k ≠ Equal` by metis_tac [cmp_thms] >>
             fs [FLOOKUP_FUNION] >>
             Cases_on `FLOOKUP (to_fmap cmp lt) (key_set cmp k)` >>
             fs [FLOOKUP_DEF] >>
             rfs [key_ordered_to_fmap] >>
             res_tac >>
             fs [key_set_cmp_def, key_set_def] >>
             metis_tac [cmp_thms]))));

val isSubmapOfBy_thm = Q.store_thm ("isSubmapOfBy_thm",
`!cmp f t1 t2.
  good_cmp cmp ∧
  invariant cmp t1 ∧
  invariant cmp t2
  ⇒
  (isSubmapOfBy cmp f t1 t2 ⇔ !k v. lookup cmp k t1 = SOME v ⇒ ?v'. lookup cmp k t2 = SOME v' ∧ f v v')`,
 rw [isSubmapOfBy_def] >>
 Cases_on `size t1 ≤ size t2` >>
 rw [submap'_thm] >>
 fs [NOT_LESS_EQUAL] >>
 imp_res_tac size_thm >>
 imp_res_tac lookup_thm >>
 fs [FCARD_DEF] >>
 `FINITE (FDOM (to_fmap cmp t1)) ∧ FINITE (FDOM (to_fmap cmp t2))` by rw [] >>
 imp_res_tac LESS_CARD_DIFF >>
 full_simp_tac std_ss [] >>
 `FINITE (FDOM (to_fmap cmp t1) DIFF FDOM (to_fmap cmp t2))` by rw [] >>
 imp_res_tac POS_CARD_HAS_MEM >>
 fs [] >>
 rw [FLOOKUP_DEF] >>
 imp_res_tac to_fmap_key_set >>
 rw [] >>
 qexists_tac `k` >>
 rw []);

val isSubmapOf_thm = Q.store_thm ("isSubmapOf_thm",
`!cmp t1 t2.
  good_cmp cmp ∧
  invariant cmp t1 ∧
  invariant cmp t2
  ⇒
  (isSubmapOf cmp t1 t2 ⇔ !k v. lookup cmp k t1 = SOME v ⇒ lookup cmp k t2 = SOME v)`,
 rw [isSubmapOf_def, isSubmapOfBy_thm]);

val fromList_thm = Q.store_thm ("fromList_thm",
`!cmp l.
  good_cmp cmp
  ⇒
  invariant cmp (fromList cmp l) ∧
  to_fmap cmp (fromList cmp l) = alist_to_fmap (MAP (\(k,v). (key_set cmp k, v)) l)`,
 Induct_on `l` >>
 simp [fromList_def, empty_thm] >>
 rpt gen_tac >>
 strip_tac >>
 PairCases_on `h` >>
 simp [] >>
 inv_mp_tac insert_thm >>
 strip_tac >>
 simp [] >>
 fs [fromList_def]);

(* ------------------------ Extra stuff, not from ghc ----------------- *)

val map_keys_def = Define `
map_keys cmp f t = fromList cmp (MAP (\(k,v). (f k, v)) (toAscList t))`;

val in_lift_key = Q.prove (
`!cmp k v l.
  good_cmp cmp ∧
  SORTED (λ(x,y:'a) (x',y':'a). cmp x x' = Less) l ∧
  transitive (λ(x,y:'a) (x',y':'a). cmp x x' = Less)
  ⇒
  ((k,v) ∈ lift_key cmp (set l) ⇔ ALOOKUP (MAP (λ(x,y). (key_set cmp x, y)) l) k = SOME v)`,
 Induct_on `l` >>
 fs [lift_key_def, key_set_def, LAMBDA_PROD, EXISTS_PROD, EXTENSION, FORALL_PROD] >>
 rw [] >>
 fs [] >>
 eq_tac >>
 rw [] >>
 fs [SORTED_EQ] >>
 res_tac >>
 fs [] >>
 metis_tac [cmp_thms]);

 (*
val alookup_unit_lem = Q.prove (
`!cmp1 cmp2 f k l x.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  resp_equiv2 cmp1 cmp2 f
  ⇒
  (ALOOKUP (MAP (\(k,v). (key_set cmp1 k, ())) l) (key_set cmp1 x') =
   ALOOKUP (MAP (\(k,v). (key_set cmp2 (f k), ())) l) (key_set cmp2 (f x')))`,

 Induct_on `l` >>
 rw [] >>
 PairCases_on `h` >>
 rw [] >>
 rfs [key_set_eq, resp_equiv2_def] >>
 >- (rfs [] >>
     fs [EXTENSION, key_set_def] >>
     match_mp_tac (METIS_PROVE [] ``F⇒x``) >>
     rw [] >>
     pop_assum mp_tac >>
     simp [] >>
     eq_tac >>
     rw [] >>
     fs [resp_equiv2_def]
     >- (qexists_tac `key_set cmp2 (f h0)` >>
         rw [key_set_def] >>
         metis_tac [cmp_thms])
     >- metis_tac [cmp_thms])
 >- (rfs [] >>
     rw [] >>
     fs [EXTENSION, key_set_def] >>
     Cases_on `x ∈ k` >>
     fs [resp_equiv2_def] >>
     first_x_assum (qspecl_then [`f x`] assume_tac) >>
     fs [] >>
     Cases_on `cmp2 (f h0) (f x) = Equal` >>
     fs []
metis_tac [cmp_thms]


 rfs [key_set_eq] >>
     `IMAGE f (key_set cmp1 h0) ⊆ key_set cmp2 (f h0)` by metis_tac [key_set_map] >>
     fs [SUBSET_DEF, EXTENSION] >>
     `x ∈ key_set cmp2 (f h0) ∧ ¬?x'.  x = f x' ∧ x' ∈ key_set cmp1 h0` by metis_tac []
     fs []

     fs [key_set_def, resp_equiv2_def, EXTENSION] >>
     rw [] >>
     rfs [] >>
     Cases_on `h1 = v` >>
     rw [] >>

     pop_assum mp_tac >>
     match_mp_tac (METIS_PROVE [] ``x ⇒ (~x ⇒ y)``) >>
     eq_tac >>
     rw []

     metis_tac [cmp_thms]
 >- (`IMAGE f k ≠ {}` by cheat >>
     imp_res_tac CHOICE_DEF >>
     fs [] >>
     fs [] >>

     rfs [key_set_eq] >>
     fs [key_set_def, resp_equiv2_def] >>
     metis_tac [cmp_thms])

 fs [resp_equiv2_def, key_set_def, EXTENSION] >>
 rfs []
 metis_tac []
 *)

val bigunion_key_sets = Q.prove (
`!cmp1.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  resp_equiv2 cmp1 cmp2 f
  ⇒
  BIGUNION (IMAGE (\x. key_set cmp2 (f x)) (key_set cmp1 x)) =
  key_set cmp2 (CHOICE (IMAGE f (key_set cmp1 x)))`,
 rw [EXTENSION] >>
 `IMAGE f (key_set cmp1 x) ≠ {}` by (rw [EXTENSION, key_set_def] >> metis_tac [cmp_thms]) >>
 imp_res_tac CHOICE_DEF >>
 fs [key_set_def] >>
 eq_tac >>
 rw [] >>
 rfs [resp_equiv2_def]
 >- metis_tac [cmp_thms] >>
 qexists_tac `key_set cmp2 (f x)` >>
 rw [key_set_def] >>
 metis_tac [cmp_thms]);

val image_lem = Q.prove (
`good_cmp cmp1
 ⇒
 IMAGE (λx. key_set cmp2 (f x)) (key_set cmp1 k'') =
 { key_set cmp2 (f x) | x | cmp1 x k'' = Equal }`,
 rw [EXTENSION,key_set_def] >>
 metis_tac [cmp_thms]);

 (*
val map_keys_thm = Q.store_thm ("map_keys_thm",
`!cmp1 cmp2 f t.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  invariant cmp1 t ∧
  resp_equiv2 cmp1 cmp2 f ∧
  equiv_inj cmp1 cmp2 f
  ⇒
  invariant cmp2 (map_keys cmp2 f t) ∧
  to_fmap cmp2 (map_keys cmp2 f t) = MAP_KEYS (BIGUNION o IMAGE (key_set cmp2 o f)) (to_fmap cmp1 t)`,

 simp [map_keys_def] >>
 rpt gen_tac >>
 DISCH_TAC >>
 inv_mp_tac fromList_thm >>
 rw [MAP_MAP_o, combinTheory.o_DEF] >>
 rw [FLOOKUP_EXT'] >>
 `SORTED (λ(x,y) (x',y'). cmp1 x x' = Less) (toAscList t) ∧
  lift_key cmp1 (set (toAscList t)) = set (fmap_to_alist (to_fmap cmp1 t))`
            by metis_tac [toAscList_thm] >>
 pop_assum mp_tac >>
 simp [EXTENSION, MEM_MAP, LAMBDA_PROD, EXISTS_PROD, FORALL_PROD] >>
 `transitive (λ(x,y:'c) (x',y':'c). cmp1 x x' = Less)` by metis_tac [good_cmp_trans] >>
 rw [in_lift_key] >>
 fs [] >>
 rw [FLOOKUP_DEF] >>
 `INJ (λx. BIGUNION (IMAGE (λx. key_set cmp2 (f x)) x)) (FDOM (to_fmap cmp1 t)) UNIV`
          by rw [INJ_DEF] >>
          imp_res_tac to_fmap_key_set
          rw [] >>
          CCONTR_TAC >>
          fs [equiv_inj_def] >>
          rfs [key_set_eq] >>
          `cmp2 (f k'') (f k') ≠ Equal` by metis_tac []
          rfs [image_lem]

          fs [EXTENSION]
          fs [PULL_EXISTS, PULL_FORALL]


          rfs [bigunion_key_sets]

              fs [resp_equiv2_def, equiv_inj_def]

              rw [key_set_def]
              fs [key_set_def]
              CCONTR_TAC
              Cases_on `cmp1 k' k'' = Equal` >>
              fs []
              `cmp2 (f k') (f k'') ≠ Equal` by metis_tac [cmp_thms]
metis_tac [cmp_thms]

 Cases_on `ALOOKUP (MAP (λ(p1,p2). (key_set cmp2 (f p1),())) (toAscList t)) k = NONE` >>
 fs []

 Cases_on `?x. k = key_set cmp2 x` >>
 fs []
 >- (Cases_on `?x'. x = f x'` >>
     fs []
     >- (first_x_assum (qspecl_then [`key_set cmp1 x'`] mp_tac) >>
         rw []

 rw [] >>


 fs [lift_key_def]

 Cases_on `FLOOKUP (MAP_KEYS (IMAGE f) (to_fmap cmp1 t)) k`
 >- (fs [ALOOKUP_NONE, MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
     CCONTR_TAC >>
     fs [] >>
     rw [] >>
     fs [lift_key_def, resp_equiv2_def, EXTENSION, LAMBDA_PROD,EXISTS_PROD, FORALL_PROD,
         PULL_FORALL, PULL_EXISTS]>>

     fs [PULL_EXISTS, PULL_FORALL, key_set_def, EXTENSION]

     first_x_assum (qspecl_then [`key_set cmp1 p_1'`, `p_2`] assume_tac) >>
     fs [FLOOKUP_DEF, MAP_KEYS_def] >>
     fs [EXTENSION, key_set_def] >>
     metis_tac [cmp_thms]

val key_set_map = Q.prove (
`!cmp1 cmp2 f k.
  resp_equiv2 cmp1 cmp2 f ⇒
  IMAGE f (key_set cmp1 k) SUBSET key_set cmp2 (f k)`,
 rw [key_set_def, SUBSET_DEF, resp_equiv2_def] >>
 metis_tac []);

`good_cmp cmp1 ∧ good_cmp cmp2 ∧ (!x y. cmp1 x y = Equal ⇒ x = y) /\ (!x y. cmp2 x y = Equal ⇒ x = y) ∧ (!x y. f x = f y ⇒ x = y) ⇒ resp_equiv2 cmp1 cmp2 f`
          rw [resp_equiv2_def] >>
          metis_tac [cmp_thms]


val flookup_lem = Q.prove (
`!cmp1 cmp2 m k v f.
  (FLOOKUP m k =
   FLOOKUP (MAP_KEYS (BIGUNION o IMAGE (λx. key_set cmp2 (f x))) m) (BIGUNION o IMAGE (λx. key_set cmp2 (f k))))`,

 rw [FLOOKUP_DEF, MAP_KEYS_def] >>
 eq_tac >>
 rw []


val map_keys_thm = Q.store_thm ("map_keys_thm",
`!cmp1 cmp2 f t.
  good_cmp cmp1 ∧
  good_cmp cmp2 ∧
  invariant cmp1 t ∧
  resp_equiv2 cmp1 cmp2 f
  ⇒
  invariant cmp2 (map_keys cmp2 f t) ∧
  to_fmap cmp2 (map_keys cmp2 f t) = MAP_KEYS (IMAGE f) (to_fmap cmp1 t)`,

 simp [map_keys_def] >>
 rpt gen_tac >>
 DISCH_TAC >>
 inv_mp_tac fromList_thm >>
 rw [MAP_MAP_o, combinTheory.o_DEF] >>
 rw [LAMBDA_PROD] >>
 rw [FLOOKUP_EXT'] >>
 `SORTED (λ(x,y) (x',y'). cmp1 x x' = Less) (toAscList t) ∧
  lift_key cmp1 (set (toAscList t)) = set (fmap_to_alist (to_fmap cmp1 t))`
            by metis_tac [toAscList_thm] >>
 pop_assum mp_tac >>
 simp [EXTENSION, MEM_MAP, LAMBDA_PROD, EXISTS_PROD, FORALL_PROD] >>
 `transitive (λ(x,y:'c) (x',y':'c). cmp1 x x' = Less)` by metis_tac [good_cmp_trans] >>
 rw [in_lift_key] >>
 fs []


 fs [lift_key_def]

 Cases_on `FLOOKUP (MAP_KEYS (IMAGE f) (to_fmap cmp1 t)) k`
 >- (rw [ALOOKUP_NONE, MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
     CCONTR_TAC >>
     fs [] >>
     rw [] >>
     fs [lift_key_def, resp_equiv2_def, EXTENSION, LAMBDA_PROD,EXISTS_PROD, FORALL_PROD,
         PULL_FORALL, PULL_EXISTS]>>

     fs [PULL_EXISTS, PULL_FORALL, key_set_def, EXTENSION]

     first_x_assum (qspecl_then [`key_set cmp1 p_1'`, `p_2`] assume_tac) >>
     fs [FLOOKUP_DEF, MAP_KEYS_def] >>
     fs [EXTENSION, key_set_def] >>
     metis_tac [cmp_thms]
     *)

val every_def = Define `
(every f Tip = T) ∧
(every f (Bin _ kx x l r) =
  if f kx x then
    if every f l then
      if every f r then T else F
    else F
  else F)`;

val every_thm = Q.store_thm ("every_thm",
`!f t cmp.
  good_cmp cmp ∧
  invariant cmp t ∧
  resp_equiv cmp f
  ⇒
  (every f t ⇔ (!k v. lookup cmp k t = SOME v ⇒ f k v))`,
 Induct_on `t` >>
 rw [every_def, lookup_def] >>
 fs [invariant_eq, resp_equiv_def] >>
 first_x_assum (qspecl_then [`f`, `cmp`] assume_tac) >>
 first_x_assum (qspecl_then [`f`, `cmp`] assume_tac) >>
 rfs [] >>
 eq_tac >>
 rw []
 >- (EVERY_CASE_TAC >>
     fs [] >>
     metis_tac [])
 >- (first_x_assum (qspecl_then [`k`] assume_tac) >>
     rfs [] >>
     EVERY_CASE_TAC >>
     fs [] >>
     metis_tac [cmp_thms])
 >- (first_x_assum (qspecl_then [`k'`] assume_tac) >>
     EVERY_CASE_TAC >>
     fs [] >>
     rfs [lookup_thm, flookup_thm] >>
     rfs [key_ordered_to_fmap] >>
     res_tac >>
     imp_res_tac key_set_cmp_thm >>
     metis_tac [cmp_thms])
 >- (first_x_assum (qspecl_then [`k'`] assume_tac) >>
     EVERY_CASE_TAC >>
     fs [] >>
     rfs [lookup_thm, flookup_thm] >>
     rfs [key_ordered_to_fmap] >>
     res_tac >>
     imp_res_tac key_set_cmp_thm >>
     metis_tac [cmp_thms]));

val exists_def = Define `
(exists f Tip = F) ∧
(exists f (Bin _ kx x l r) =
  if f kx x then
    T
  else if exists f l then
    T
  else if exists f r then
    T
  else
    F)`;

val exists_thm = Q.store_thm ("exists_thm",
`!f t cmp.
  good_cmp cmp ∧
  invariant cmp t ∧
  resp_equiv cmp f
  ⇒
  (exists f t ⇔ (?k v. lookup cmp k t = SOME v ∧ f k v))`,
 Induct_on `t` >>
 rw [exists_def, lookup_def] >>
 fs [invariant_eq, resp_equiv_def] >>
 first_x_assum (qspecl_then [`f`, `cmp`] assume_tac) >>
 first_x_assum (qspecl_then [`f`, `cmp`] assume_tac) >>
 rfs [] >>
 eq_tac >>
 rw []
 >- metis_tac [cmp_thms]
 >- (qexists_tac `k'` >>
     rw [] >>
     EVERY_CASE_TAC >>
     fs [] >>
     rfs [lookup_thm, flookup_thm] >>
     rfs [key_ordered_to_fmap] >>
     res_tac >>
     imp_res_tac key_set_cmp_thm >>
     metis_tac [cmp_thms])
 >- (qexists_tac `k'` >>
     rw [] >>
     EVERY_CASE_TAC >>
     fs [] >>
     rfs [lookup_thm, flookup_thm] >>
     rfs [key_ordered_to_fmap] >>
     res_tac >>
     imp_res_tac key_set_cmp_thm >>
     metis_tac [cmp_thms])
 >- (EVERY_CASE_TAC >>
     fs [] >>
     metis_tac []));

Theorem filterWithKey_thm:
  ∀f t cmp.
    good_cmp cmp ∧
    invariant cmp t ∧
    (∀k1 k2 x. cmp k1 k2 = Equal ⇒ f k1 x = f k2 x) ⇒
      invariant cmp (filterWithKey f t) ∧
      to_fmap cmp (filterWithKey f t) =
      FDIFF (to_fmap cmp t)
            {k |k,v| FLOOKUP (to_fmap cmp t) k = SOME v ∧ ¬f (CHOICE k) v}
Proof
  Induct_on ‘t’
  \\ simp [to_fmap_def, filterWithKey_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gs [invariant_eq]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ IF_CASES_TAC \\ gs []
  >- (
    qspecl_then [‘k’,‘v’,‘filterWithKey f t’,‘filterWithKey f t'’]
      mp_tac link_thm
    \\ impl_keep_tac \\ gs []
    >- gs [key_ordered_to_fmap]
    \\ strip_tac \\ gs []
    \\ rw [FLOOKUP_EXT']
    \\ simp [FLOOKUP_FDIFF, FLOOKUP_FUNION, FLOOKUP_UPDATE]
    \\ IF_CASES_TAC \\ gs []
    >- (
      qpat_x_assum ‘key_set _ _ = _’ (assume_tac o SYM) \\ gvs []
      \\ rw [IN_DEF, FORALL_PROD]
      \\ ‘key_set cmp k ≠ {}’
        by gs [EXTENSION, key_set_def, good_cmp_thm, SF SFY_ss]
      \\ drule_then assume_tac CHOICE_DEF
      \\ ‘f k v = f (CHOICE (key_set cmp k)) v’
        suffices_by rw []
      \\ first_x_assum irule
      \\ gs [key_set_def])
    \\ gs [IN_DEF, LAMBDA_PROD, EXISTS_PROD]
    \\ IF_CASES_TAC \\ gs []
    >- (
      rw [IS_SOME_EXISTS] \\ gs [flookup_thm, DISJOINT_ALT])
    \\ IF_CASES_TAC \\ gs []
    >- (
      CASE_TAC \\ gs [flookup_thm, DISJOINT_ALT])
    \\ IF_CASES_TAC \\ gs []
    \\ gs [CaseEq "option"])
  \\ qspecl_then [‘filterWithKey f t’,‘filterWithKey f t'’]
       mp_tac link2_thm
  \\ impl_keep_tac \\ gs []
  >- gs [key_ordered_to_fmap]
  \\ strip_tac \\ gs []
  \\ rw [FLOOKUP_EXT']
  \\ simp [FLOOKUP_FDIFF, FLOOKUP_FUNION, FLOOKUP_UPDATE]
  \\ IF_CASES_TAC \\ gs []
  >- (
    pop_assum mp_tac
    \\ rw [IN_DEF, LAMBDA_PROD, EXISTS_PROD, IS_SOME_EXISTS]
    \\ gs [flookup_thm, DISJOINT_ALT])
  \\ IF_CASES_TAC \\ gs []
  \\ ntac 2 (pop_assum mp_tac)
  \\ rw [IN_DEF, LAMBDA_PROD, EXISTS_PROD, IS_SOME_EXISTS]
  \\ gs [flookup_thm, DISJOINT_ALT]
  \\ gs [CaseEqs ["option", "bool"], flookup_thm]
  \\ CCONTR_TAC \\ gs []
  \\ ‘key_set cmp k ≠ {}’
    by gs [EXTENSION, key_set_def, good_cmp_thm, SF SFY_ss]
  \\ drule_then assume_tac CHOICE_DEF
  \\ fs [good_cmp_def, key_set_def]
  \\ metis_tac []
QED

Theorem every_filter:
  good_cmp cmp ∧
  invariant cmp t ∧
  (∀k1 k2 x. cmp k1 k2 = Equal ⇒ f k1 x = f k2 x) ⇒
    every f (filterWithKey f t)
Proof
  strip_tac
  \\ drule_all_then strip_assume_tac filterWithKey_thm
  \\ gs [GSYM resp_equiv_def]
  \\ drule_all_then strip_assume_tac every_thm \\ rw []
  \\ drule_all_then assume_tac lookup_thm
  \\ gs [FLOOKUP_FDIFF, IN_DEF, LAMBDA_PROD, EXISTS_PROD, resp_equiv_def]
  \\ ‘key_set cmp k ≠ {}’
    by gs [EXTENSION, key_set_def, good_cmp_thm, SF SFY_ss]
  \\ drule_then assume_tac CHOICE_DEF
  \\ ‘f k v = f (CHOICE (key_set cmp k)) v’
    suffices_by rw []
  \\ fs [key_set_def]
QED

Theorem filter_thm:
  ∀f t cmp.
    good_cmp cmp ∧
    invariant cmp t ⇒
      invariant cmp (filter f t) ∧
      to_fmap cmp (filter f t) =
      FDIFF (to_fmap cmp t) {k |k,v| FLOOKUP (to_fmap cmp t) k = SOME v ∧ ¬f v}
Proof
  simp [filter_def, filterWithKey_thm]
QED

val _ = export_theory ();
