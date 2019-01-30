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

val BIND_UNITR = Q.store_thm(
  "BIND_UNITR[simp]",
  ‘BIND m UNIT = m’,
  simp[FUN_EQ_THM, BIND_def, UNIT_def]);

val BIND_UNITL = Q.store_thm(
  "BIND_UNITL[simp]",
  ‘BIND (UNIT x) f = f x’,
  simp[FUN_EQ_THM, BIND_def, UNIT_def]);

val MCOMPOSE_LEFT_ID = Q.store_thm(
  "MCOMPOSE_LEFT_ID[simp]",
  ‘MCOMPOSE UNIT g = g’,
  simp[FUN_EQ_THM, UNIT_def, MCOMPOSE_def]);

val MCOMPOSE_RIGHT_ID = Q.store_thm(
  "MCOMPOSE_RIGHT_ID[simp]",
  ‘MCOMPOSE f UNIT = f’,
  simp[FUN_EQ_THM, UNIT_def, MCOMPOSE_def]);

val MCOMPOSE_ASSOC = Q.store_thm(
  "MCOMPOSE_ASSOC",
  ‘MCOMPOSE f (MCOMPOSE g h) = MCOMPOSE (MCOMPOSE f g) h’,
  simp[MCOMPOSE_def, FUN_EQ_THM, BIND_def]);

val FMAP_def = Define‘
  FMAP (f : 'a -> 'b) (M1 : 's -> 'a) = f o M1
’;

val FMAP_ID = Q.store_thm(
  "FMAP_ID[simp]",
  ‘(FMAP (\x. x) M = M) /\ (FMAP I M = M)’,
  simp[FMAP_def, FUN_EQ_THM]);

val FMAP_o = Q.store_thm(
  "FMAP_o",
  ‘FMAP (f o g) = FMAP f o FMAP g’,
  simp[FMAP_def, FUN_EQ_THM]);

val FMAP_BIND = Q.store_thm(
  "FMAP_BIND",
  ‘FMAP f M = BIND M (UNIT o f)’,
  simp[FMAP_def, UNIT_def, BIND_def, FUN_EQ_THM]);

(* aka the W combinator *)
val JOIN_def = Define‘
  JOIN (MM : 's -> ('s -> 'a)) s = MM s s
’;

val BIND_JOIN = Q.store_thm(
  "BIND_JOIN",
  ‘BIND M f = JOIN (FMAP f M)’,
  simp[FUN_EQ_THM, JOIN_def, FMAP_def, BIND_def]);

val JOIN_BIND = Q.store_thm(
  "JOIN_BIND",
  ‘JOIN M = BIND M I’,
  simp[FUN_EQ_THM, BIND_def, JOIN_def]);

val _ =
    monadsyntax.declare_monad (
      "reader",
      {
        bind = “readerMonad$BIND”, unit = “readerMonad$UNIT”,
        ignorebind = NONE, choice = NONE, guard = NONE, fail = NONE
      }
    )



val _ = export_theory();
