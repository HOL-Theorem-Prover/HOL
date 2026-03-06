Theory subtype
Ancestors
  combin pred_set res_quan pair
Libs
  hurdUtils ho_proverTools

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

Theorem EQ_T_IMP:
     !x. x = T ==> x
Proof
   PROVE_TAC []
QED

Theorem EQ_SUBSET_SUBSET:
     !(s : 'a -> bool) t. (s = t) ==> s SUBSET t /\ t SUBSET s
Proof
   RW_TAC std_ss [SUBSET_DEF, EXTENSION]
QED

Theorem IN_EQ_UNIV_IMP:
     !s. (s = UNIV) ==> !v. (v : 'a) IN s
Proof
   RW_TAC std_ss [IN_UNIV]
QED

(* ------------------------------------------------------------------------- *)
(* bool theory subtypes.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Subtype definitions *)

val _ = add_infix("->", 250, HOLgrammars.RIGHT);

val _ = overload_on
  ("->", ``FUNSET:('a->bool) -> ('b->bool) -> (('a->'b)->bool)``);
Overload "-->" = ``DFUNSET : ('a->bool) -> ('a->'b->bool) -> (('a->'b)->bool)``;
val _ = set_fixity "-->" (Infixr 750);


Definition pair_def:
   pair (X : 'a -> bool) (Y : 'b -> bool) = \ (x, y). x IN X /\ y IN Y
End

Theorem IN_PAIR:
     !(x : 'a # 'b) X Y. x IN pair X Y = FST x IN X /\ SND x IN Y
Proof
   Cases
   ++ RW_TAC std_ss [pair_def, SPECIFICATION]
QED

(* Simplifications *)

Theorem PAIR_UNIV:
     pair UNIV UNIV = (UNIV : 'a # 'b -> bool)
Proof
   RW_TAC std_ss [SET_EQ, IN_PAIR, IN_UNIV]
QED

(* Subtypes *)

Theorem DEFAULT_SUBTYPE:
     !x. x IN UNIV
Proof
   RW_TAC std_ss [IN_UNIV]
QED

Theorem COMB_SUBTYPE:
     !(f : 'a -> 'b) a x y. f IN (x --> y) /\ a IN x ==> f a IN y a
Proof
   RW_TAC std_ss [IN_DFUNSET]
   ++ PROVE_TAC []
QED

Theorem ABS_SUBTYPE:
     !(f : 'a -> 'b) p. (!x. f x IN p x) ==> (\x. f x) IN (UNIV --> p)
Proof
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC std_ss [IN_DFUNSET]
QED

Theorem COND_SUBTYPE:
     !c (a:'a) b x.
       (c ==> a IN x) /\
       (~c ==> b IN x) ==>
       COND c a b IN x
Proof
   RW_TAC std_ss []
QED

Theorem RES_ABSTRACT_SUBTYPE:
     !p (f : 'a -> 'b) q.
       (!x. x IN p ==> (f x IN q x)) ==>
       RES_ABSTRACT p f IN (p --> q)
Proof
   RW_TAC std_ss [RES_FORALL, RES_ABSTRACT, IN_DFUNSET]
QED

Theorem UNCURRY_SUBTYPE:
     !(f : 'a -> 'b -> 'c) p.
       (!x y. f x y IN p x y) ==>
       (UNCURRY f IN (UNIV --> UNCURRY p))
Proof
    RW_TAC std_ss [IN_DFUNSET]
    ++ Cases_on `x`
    ++ RW_TAC std_ss []
QED

(* ------------------------------------------------------------------------- *)
(* The bool theory simplifier module.                                        *)
(* ------------------------------------------------------------------------- *)

(* Congruences *)

Theorem comb_cong:
     !(f : 'a -> 'b) f' a a'. (f = f') /\ (a = a') ==> (f a = f' a')
Proof
   RW_TAC std_ss []
QED

Theorem abs_cong:
     !(f : 'a -> 'b) f'. (!x. f x = f' x) ==> ((\x. f x) = f')
Proof
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC std_ss []
QED

Theorem conj_cong:
     !a a' b b'.
       (b ==> (a = a')) /\
       (a' ==> (b = b')) ==>
       (a /\ b = a' /\ b')
Proof
   RW_TAC std_ss []
   ++ ho_PROVE_TAC []
QED

Theorem disj_cong:
     !a a' b b'.
       (~b ==> (a = a')) /\
       (~a' ==> (b = b')) ==>
       (a \/ b = a' \/ b')
Proof
   RW_TAC std_ss []
   ++ ho_PROVE_TAC []
QED

Theorem imp_cong:
     !a a' b b'.
       (a = a') /\
       (a' ==> (b = b')) ==>
       (a ==> b = a' ==> b')
Proof
   RW_TAC std_ss []
   ++ ho_PROVE_TAC []
QED

Theorem cond_cong:
     !c c' (a:'a) a' b b'.
       (c = c') /\
       (c' ==> (a = a')) /\
       (~c' ==> (b = b')) ==>
       (COND c a b = COND c' a' b')
Proof
   RW_TAC std_ss []
QED

Theorem res_forall_cong:
     !(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_FORALL p f = RES_FORALL p' f')
Proof
   RW_TAC std_ss [RES_FORALL]
QED

Theorem res_exists_cong:
     !(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_EXISTS p f = RES_EXISTS p' f')
Proof
   RW_TAC std_ss [RES_EXISTS]
   ++ ho_PROVE_TAC []
QED

Theorem res_select_cong:
     !(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_SELECT p f = RES_SELECT p' f')
Proof
   RW_TAC std_ss [RES_SELECT]
   ++ Q_TAC SUFF_TAC `!x. x IN p /\ f x = x IN p /\ f' x` >> RW_TAC std_ss []
   ++ ho_PROVE_TAC []
QED

Theorem res_abstract_cong:
     !(p : 'a -> bool) p' f f'.
       (p = p') /\
       (!x. x IN p' ==> (f x = f' x)) ==>
       (RES_ABSTRACT p f = RES_ABSTRACT p' f')
Proof
   RW_TAC std_ss [RES_ABSTRACT_EQUAL]
QED

Theorem uncurry_cong:
     !(f : 'a -> 'b -> 'c) f'.
        (!x y. f x y = f' x y) ==>
        (UNCURRY f = UNCURRY f')
Proof
   FUN_EQ_TAC
   ++ RW_TAC std_ss []
   ++ Cases_on `x`
   ++ RW_TAC std_ss [UNCURRY_DEF]
QED

(* Rewrites *)

Theorem PAIRED_BETA_THM:
     !f z. UNCURRY f z = f (FST z) (SND z)
Proof
   STRIP_TAC
   ++ Cases
   ++ RW_TAC std_ss []
QED

(* non-interactive mode
*)
