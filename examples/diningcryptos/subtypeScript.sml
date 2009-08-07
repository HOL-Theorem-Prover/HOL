(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "subtype";

(* interactive mode
show_assums := true;
loadPath := union ["../ho_prover"] (!loadPath);
app load
  ["bossLib", "combinTheory", "pred_setTheory", "seqTheory", "subtypeUseful",
   "res_quanTheory", "ho_proverTools", "pairTheory"];
*)

(* open bossLib combinTheory pred_setTheory seqTheory subtypeUseful
     res_quanTheory ho_proverTools pairTheory;*)

open bossLib metisLib combinTheory pred_setTheory seqTheory subtypeUseful
     res_quanTheory pairTheory;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Auxiliary theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

val EQ_T_IMP = store_thm
  ("EQ_T_IMP",
   ``!x. x = T ==> x``,
   PROVE_TAC []);

val EQ_SUBSET_SUBSET = store_thm
  ("EQ_SUBSET_SUBSET",
   ``!(s : 'a -> bool) t. (s = t) ==> s SUBSET t /\ t SUBSET s``,
   RW_TAC std_ss [SUBSET_DEF, EXTENSION]);

val IN_EQ_UNIV_IMP = store_thm
  ("IN_EQ_UNIV_IMP",
   ``!s. (s = UNIV) ==> !v. (v : 'a) IN s``,
   RW_TAC std_ss [IN_UNIV]);

(* ------------------------------------------------------------------------- *)
(* bool theory subtypes.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Subtype definitions *)

val FUNSET_def = Define
  `FUNSET (P:'a->bool) (Q:'b->bool) = \f. !x. x IN P ==> f x IN Q`;

val DFUNSET_def = Define
  `DFUNSET (P:'a->bool) (Q:'a->'b->bool) = \f. !x. x IN P ==> f x IN Q x`;

(* home
val _ = overload_on
  ("->", ``FUNSET:('a->bool) -> ('b->bool) -> (('a->'b)->bool)``);
*)

(* work
*)
val _ = overload_on
  (GrammarSpecials.case_arrow_special,
   ``FUNSET : ('a->bool) -> ('b->bool) -> (('a->'b)->bool)``);

val _ = overload_on
  ("-->", ``DFUNSET : ('a->bool) -> ('a->'b->bool) -> (('a->'b)->bool)``);

val pair_def = Define
  `pair (X : 'a -> bool) (Y : 'b -> bool) = \ (x, y). x IN X /\ y IN Y`;

val IN_FUNSET = store_thm
  ("IN_FUNSET",
   ``!(f:'a->'b) P Q. f IN (P -> Q) = !x. x IN P ==> f x IN Q``,
   RW_TAC std_ss [SPECIFICATION, FUNSET_def]);

val IN_DFUNSET = store_thm
  ("IN_DFUNSET",
   ``!(f:'a->'b) (P:'a->bool) Q. f IN (P --> Q) = !x. x IN P ==> f x IN Q x``,
   RW_TAC std_ss [SPECIFICATION, DFUNSET_def]);

val IN_PAIR = store_thm
  ("IN_PAIR",
   ``!(x : 'a # 'b) X Y. x IN pair X Y = FST x IN X /\ SND x IN Y``,
   Cases
   ++ RW_TAC std_ss [pair_def, SPECIFICATION]);

val FUNSET_THM = store_thm
  ("FUNSET_THM",
   ``!s t (f:'a->'b) x. f IN (s -> t) /\ x IN s ==> f x IN t``,
    RW_TAC std_ss [IN_FUNSET] ++ PROVE_TAC []);

(* Warning: do not add the following as a simplification *)
val UNIV_FUNSET_UNIV = store_thm
  ("UNIV_FUNSET_UNIV",
   ``((UNIV : 'a -> bool) -> (UNIV : 'b -> bool)) = UNIV``,
   SET_EQ_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV]);

(* Simplifications *)

val FUNSET_DFUNSET = store_thm
  ("FUNSET_DFUNSET",
   ``!(x : 'a -> bool) (y : 'b -> bool). (x -> y) = (x --> K y)``,
   RW_TAC std_ss [SET_EQ, IN_FUNSET, IN_DFUNSET, K_DEF]);

val PAIR_UNIV = store_thm
  ("PAIR_UNIV",
   ``pair UNIV UNIV = (UNIV : 'a # 'b -> bool)``,
   RW_TAC std_ss [SET_EQ, IN_PAIR, IN_UNIV]);

val SUBSET_INTER = store_thm
  ("SUBSET_INTER",
   ``!(s : 'a -> bool) t u.
   s SUBSET (t INTER u) = s SUBSET t /\ s SUBSET u``,
   RW_TAC std_ss [SUBSET_DEF, IN_INTER]
   ++ PROVE_TAC []);

val K_SUBSET = store_thm
  ("K_SUBSET",
   ``!x y. K x SUBSET y = ~x \/ (UNIV SUBSET y)``,
   RW_TAC std_ss [K_DEF, SUBSET_DEF, IN_UNIV]
   ++ RW_TAC std_ss [SPECIFICATION]
   ++ PROVE_TAC []);
  
val SUBSET_K = store_thm
  ("SUBSET_K",
   ``!x y. x SUBSET K y = (x SUBSET EMPTY) \/ y``,
   RW_TAC std_ss [K_DEF, SUBSET_DEF, NOT_IN_EMPTY]
   ++ RW_TAC std_ss [SPECIFICATION]
   ++ PROVE_TAC []);

(* Judgements *)

val SUBSET_THM = store_thm
  ("SUBSET_THM",
   ``!(P : 'a -> bool) Q. P SUBSET Q ==> (!x. x IN P ==> x IN Q)``,
    RW_TAC std_ss [SUBSET_DEF]);

(* Subtypes *)

val DEFAULT_SUBTYPE = store_thm
  ("DEFAULT_SUBTYPE",
   ``!x. x IN UNIV``,
   RW_TAC std_ss [IN_UNIV]);

val COMB_SUBTYPE = store_thm
  ("COMB_SUBTYPE",
   ``!(f : 'a -> 'b) a x y. f IN (x --> y) /\ a IN x ==> f a IN y a``,
   RW_TAC std_ss [IN_DFUNSET]
   ++ PROVE_TAC []);

val ABS_SUBTYPE = store_thm
  ("ABS_SUBTYPE",
   ``!(f : 'a -> 'b) p. (!x. f x IN p x) ==> (\x. f x) IN (UNIV --> p)``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC std_ss [IN_DFUNSET]);

val COND_SUBTYPE = store_thm
  ("COND_SUBTYPE",
   ``!c (a:'a) b x.
       (c ==> a IN x) /\
       (~c ==> b IN x) ==>
       COND c a b IN x``,
   RW_TAC std_ss []);

val RES_ABSTRACT_SUBTYPE = store_thm
  ("RES_ABSTRACT_SUBTYPE",
   ``!p (f : 'a -> 'b) q.
       (!x. x IN p ==> (f x IN q x)) ==>
       RES_ABSTRACT p f IN (p --> q)``,
   RW_TAC std_ss [RES_FORALL, RES_ABSTRACT, IN_DFUNSET]);

val UNCURRY_SUBTYPE = store_thm
  ("UNCURRY_SUBTYPE",
   ``!(f : 'a -> 'b -> 'c) p.
       (!x y. f x y IN p x y) ==>
       (UNCURRY f IN (UNIV --> UNCURRY p))``,
    RW_TAC std_ss [IN_DFUNSET]
    ++ Cases_on `x`
    ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* The bool theory simplifier module.                                        *)
(* ------------------------------------------------------------------------- *)

(* Congruences *)

val comb_cong = store_thm
  ("comb_cong",
   ``!(f : 'a -> 'b) f' a a'. (f = f') /\ (a = a') ==> (f a = f' a')``,
   RW_TAC std_ss []);

val abs_cong = store_thm
  ("abs_cong",
   ``!(f : 'a -> 'b) f'. (!x. f x = f' x) ==> ((\x. f x) = f')``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC std_ss []);

val conj_cong = store_thm
  ("conj_cong",
   ``!a a' b b'.
       (b ==> (a = a')) /\
       (a' ==> (b = b')) ==>
       (a /\ b = a' /\ b')``,
   RW_TAC std_ss []
   ++ METIS_TAC []);

val disj_cong = store_thm
  ("disj_cong",
   ``!a a' b b'.
       (~b ==> (a = a')) /\
       (~a' ==> (b = b')) ==>
       (a \/ b = a' \/ b')``,
   RW_TAC std_ss []
   ++ METIS_TAC []);

val imp_cong = store_thm
  ("imp_cong",
   ``!a a' b b'.
       (a = a') /\
       (a' ==> (b = b')) ==>
       (a ==> b = a' ==> b')``,
   RW_TAC std_ss []
   ++ METIS_TAC []);

val cond_cong = store_thm
  ("cond_cong",
   ``!c c' (a:'a) a' b b'.
       (c = c') /\
       (c' ==> (a = a')) /\
       (~c' ==> (b = b')) ==>
       (COND c a b = COND c' a' b')``,
   RW_TAC std_ss []);

val res_forall_cong = store_thm
  ("res_forall_cong",
   ``!(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_FORALL p f = RES_FORALL p' f')``,
   RW_TAC std_ss [RES_FORALL]);

val res_exists_cong = store_thm
  ("res_exists_cong",
   ``!(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_EXISTS p f = RES_EXISTS p' f')``,
   RW_TAC std_ss [RES_EXISTS]
   ++ METIS_TAC []);

val res_select_cong = store_thm
  ("res_select_cong",
   ``!(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_SELECT p f = RES_SELECT p' f')``,
   RW_TAC std_ss [RES_SELECT]
   ++ SUFF_TAC `!x. x IN p /\ f x = x IN p /\ f' x` >> RW_TAC std_ss []
   ++ METIS_TAC []);

val res_abstract_cong = store_thm
  ("res_abstract_cong",
   ``!(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_ABSTRACT p f = RES_ABSTRACT p' f')``,
   RW_TAC std_ss [RES_ABSTRACT_EQUAL]);

val uncurry_cong = store_thm
  ("uncurry_cong",
   ``!(f : 'a -> 'b -> 'c) f'.
        (!x y. f x y = f' x y) ==>
        (UNCURRY f = UNCURRY f')``,
   FUN_EQ_TAC
   ++ RW_TAC std_ss []
   ++ Cases_on `x`
   ++ RW_TAC std_ss [UNCURRY_DEF]);

(* Rewrites *)

val PAIRED_BETA_THM = store_thm
  ("PAIRED_BETA_THM",
   ``!f z. UNCURRY f z = f (FST z) (SND z)``,
   STRIP_TAC
   ++ Cases
   ++ RW_TAC std_ss []);

val EMPTY_FUNSET = store_thm
  ("EMPTY_FUNSET",
   ``!s. ({} -> s) = (UNIV : ('a -> 'b) -> bool)``,
   RW_TAC std_ss [SET_EQ, IN_FUNSET, NOT_IN_EMPTY, IN_UNIV]);

val FUNSET_EMPTY = store_thm
  ("FUNSET_EMPTY",
   ``!s (f : 'a -> 'b). f IN (s -> {}) = (s = {})``,
   RW_TAC std_ss [IN_FUNSET, NOT_IN_EMPTY, SET_EQ]);

(* non-interactive mode
*)
val _ = export_theory ();
