(* ===================================================================== *)
(* FILE          : utilsLibSupportScript.sml                             *)
(* DESCRIPTION   : Small theorems that utilsLib used to prove at load    *)
(*                 time.  Landed here so utilsLib.sml can import them    *)
(*                 rather than firing Tactical.prove during its own      *)
(*                 load.                                                  *)
(* ===================================================================== *)

Theory utilsLibSupport
Ancestors
  combin words integer_word bitstring pair
Libs
  HolKernel Parse boolLib bossLib

Theorem COND_UPDATE0:
  !b (s1 : 'a) s2.
    (if b then ((), s1) else ((), s2)) = ((), if b then s1 else s2)
Proof
  RW_TAC std_ss []
QED

Theorem COND_UPDATE1:
  !(f : ('a -> 'b) -> 'c -> 'd) b v1 v2 s1 s2.
    (if b then f (K v1) s1 else f (K v2) s2) =
    f (K (if b then v1 else v2)) (if b then s1 else s2)
Proof
  Cases_on `b` THEN REWRITE_TAC []
QED

Theorem COND_UPDATE2:
  (!b a x y (f : 'a -> 'b).
     (if b then (a =+ x) f else (a =+ y) f) =
     (a =+ if b then x else y) f) /\
  (!b a y (f : 'a -> 'b).
     (if b then f else (a =+ y) f) = (a =+ if b then f a else y) f) /\
  (!b a x (f : 'a -> 'b).
     (if b then (a =+ x) f else f) = (a =+ if b then x else f a) f)
Proof
  REPEAT CONJ_TAC
  THEN Cases
  THEN REWRITE_TAC [combinTheory.APPLY_UPDATE_ID]
QED

Theorem COND_UPDATE3:
  !b. (if b then T else F) = b
Proof
  Cases THEN REWRITE_TAC []
QED

Theorem literal_case_rand:
  !(f : 'a -> 'b) (x : 'c) y a b.
    f (literal_case (\v. if v = x then a else b) y) =
    literal_case (\v. if v = x then f a else f b) y
Proof
  SIMP_TAC std_ss [boolTheory.literal_case_DEF, boolTheory.COND_RAND]
QED

(* Cond-splitting tautologies used by utilsLib's split_cond machinery.
   utilsLib UNDISCHes each to get [antecedent] |- goal. *)

Theorem split_xt:
  !(b :bool) (x :'a) y. b ==> (if b then x else y) = x
Proof
  RW_TAC bool_ss []
QED

Theorem split_yt:
  !(b :bool) (x :'a) y. ~b ==> (if b then x else y) = y
Proof
  RW_TAC bool_ss []
QED

Theorem split_zt:
  !(b :bool) (x :'a) y. b ==> (if ~b then x else y) = y
Proof
  RW_TAC bool_ss []
QED

Theorem split_xl:
  !(b :bool) (x :'a) y (c :'b). b ==> ((if b then x else y), c) = (x, c)
Proof
  RW_TAC bool_ss []
QED

Theorem split_yl:
  !(b :bool) (x :'a) y (c :'b). ~b ==> ((if b then x else y), c) = (y, c)
Proof
  RW_TAC bool_ss []
QED

Theorem split_zl:
  !(b :bool) (x :'a) y (c :'b). b ==> ((if ~b then x else y), c) = (y, c)
Proof
  RW_TAC bool_ss []
QED

Theorem split_xr:
  !(b :bool) (c :'b) (x :'a) y. b ==> (c, (if b then x else y)) = (c, x)
Proof
  RW_TAC bool_ss []
QED

Theorem split_yr:
  !(b :bool) (c :'b) (x :'a) y. ~b ==> (c, (if b then x else y)) = (c, y)
Proof
  RW_TAC bool_ss []
QED

Theorem split_zr:
  !(b :bool) (c :'b) (x :'a) y. b ==> (c, (if ~b then x else y)) = (c, y)
Proof
  RW_TAC bool_ss []
QED

(* Two membership-elimination lemmas that stateLib.sml used to prove
   at load time. *)

Theorem EXPAND_lem:
  !(x:'a # 'b) y m (s :'c) (c :'d).
    ((!c d. (c, d) IN set (x :: y) ==> (m s c = d)) <=>
     (!c d. ((c, d) = x) ==> (m s c = d)) /\
     (!c d. ((c, d) IN set y) ==> (m s c = d)))
Proof
  SRW_TAC [] [] \\ metis_tac []
QED

Theorem EXPAND_lem2:
  !(x:'a # 'b) y m (s :'c) (c :'d).
    ((!c d. (c, d) IN x INSERT y ==> (m s c = d)) <=>
     (!c d. ((c, d) = x) ==> (m s c = d)) /\
     (!c d. ((c, d) IN y) ==> (m s c = d)))
Proof
  SRW_TAC [] [] \\ metis_tac []
QED
