open HolKernel Parse boolLib bossLib;

local open listTheory in end
(* the dependency on bossLib equates to an unnecessary dependency on
   listTheory *)

val _ = new_theory "readerMonad";

val BIND_def = Define‘
  BIND (M : 's -> 'a) (f: 'a -> 's -> 'b) s = f (M s) s
’;

val UNIT_def = Define‘
  UNIT (x:'a) s = x
’;

val MCOMPOSE_def = Define‘
  MCOMPOSE (f1 : 'a -> ('s -> 'b)) (f2 : 'b -> ('s -> 'c)) a = BIND (f1 a) f2
’;

Theorem BIND_UNITR[simp]: BIND m UNIT = m
Proof
  simp[FUN_EQ_THM, BIND_def, UNIT_def]
QED

Theorem BIND_UNITL[simp]: BIND (UNIT x) f = f x
Proof
  simp[FUN_EQ_THM, BIND_def, UNIT_def]
QED

Theorem MCOMPOSE_LEFT_ID[simp]: MCOMPOSE UNIT g = g
Proof
  simp[FUN_EQ_THM, UNIT_def, MCOMPOSE_def]
QED

Theorem MCOMPOSE_RIGHT_ID[simp]: MCOMPOSE f UNIT = f
Proof
  simp[FUN_EQ_THM, UNIT_def, MCOMPOSE_def]
QED

Theorem MCOMPOSE_ASSOC:
  MCOMPOSE f (MCOMPOSE g h) = MCOMPOSE (MCOMPOSE f g) h
Proof simp[MCOMPOSE_def, FUN_EQ_THM, BIND_def]
QED

val FMAP_def = Define‘
  FMAP (f : 'a -> 'b) (M1 : 's -> 'a) = f o M1
’;

Theorem FMAP_ID[simp]:
  (FMAP (\x. x) M = M) /\ (FMAP I M = M)
Proof simp[FMAP_def, FUN_EQ_THM]
QED

Theorem FMAP_o:
  FMAP (f o g) = FMAP f o FMAP g
Proof
  simp[FMAP_def, FUN_EQ_THM]
QED

Theorem FMAP_BIND:
  FMAP f M = BIND M (UNIT o f)
Proof simp[FMAP_def, UNIT_def, BIND_def, FUN_EQ_THM]
QED

(* aka the W combinator *)
val JOIN_def = Define‘
  JOIN (MM : 's -> ('s -> 'a)) s = MM s s
’;

Theorem BIND_JOIN:
  BIND M f = JOIN (FMAP f M)
Proof
  simp[FUN_EQ_THM, JOIN_def, FMAP_def, BIND_def]
QED

Theorem JOIN_BIND:
  JOIN M = BIND M I
Proof
  simp[FUN_EQ_THM, BIND_def, JOIN_def]
QED

val _ =
    monadsyntax.declare_monad (
      "reader",
      {
        bind = “readerMonad$BIND”, unit = “readerMonad$UNIT”,
        ignorebind = NONE, choice = NONE, guard = NONE, fail = NONE
      }
    )



val _ = export_theory();
