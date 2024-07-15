open HolKernel Parse boolLib bossLib;

open combinTheory pred_setTheory hurdUtils res_quanTheory ho_proverTools
     pairTheory;

val _ = new_theory "subtype";
val _ = ParseExtras.temp_loose_equality()

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

val _ = add_infix("->", 250, HOLgrammars.RIGHT);

val _ = overload_on
  ("->", ``FUNSET:('a->bool) -> ('b->bool) -> (('a->'b)->bool)``);
Overload "-->" = ``DFUNSET : ('a->bool) -> ('a->'b->bool) -> (('a->'b)->bool)``;
val _ = set_fixity "-->" (Infixr 750);


val pair_def = Define
  `pair (X : 'a -> bool) (Y : 'b -> bool) = \ (x, y). x IN X /\ y IN Y`;

val IN_PAIR = store_thm
  ("IN_PAIR",
   ``!(x : 'a # 'b) X Y. x IN pair X Y = FST x IN X /\ SND x IN Y``,
   Cases
   ++ RW_TAC std_ss [pair_def, SPECIFICATION]);

(* Simplifications *)

val PAIR_UNIV = store_thm
  ("PAIR_UNIV",
   ``pair UNIV UNIV = (UNIV : 'a # 'b -> bool)``,
   RW_TAC std_ss [SET_EQ, IN_PAIR, IN_UNIV]);

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
   ++ ho_PROVE_TAC []);

val disj_cong = store_thm
  ("disj_cong",
   ``!a a' b b'.
       (~b ==> (a = a')) /\
       (~a' ==> (b = b')) ==>
       (a \/ b = a' \/ b')``,
   RW_TAC std_ss []
   ++ ho_PROVE_TAC []);

val imp_cong = store_thm
  ("imp_cong",
   ``!a a' b b'.
       (a = a') /\
       (a' ==> (b = b')) ==>
       (a ==> b = a' ==> b')``,
   RW_TAC std_ss []
   ++ ho_PROVE_TAC []);

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
   ++ ho_PROVE_TAC []);

val res_select_cong = store_thm
  ("res_select_cong",
   ``!(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_SELECT p f = RES_SELECT p' f')``,
   RW_TAC std_ss [RES_SELECT]
   ++ Q_TAC SUFF_TAC `!x. x IN p /\ f x = x IN p /\ f' x` >> RW_TAC std_ss []
   ++ ho_PROVE_TAC []);

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

(* non-interactive mode
*)
val _ = export_theory ();
