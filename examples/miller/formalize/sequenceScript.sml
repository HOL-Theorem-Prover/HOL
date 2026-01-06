Theory sequence
Ancestors
  arithmetic extra_num combin
Libs
  hurdUtils

val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

Definition shd_def:   shd (f : num -> 'a) = f 0
End

Definition stl_def:   stl (f : num -> 'a) n = f (SUC n)
End

Definition scons_def:
   (scons (h : 'a) (t : num -> 'a) 0 = h) /\ (scons h t (SUC n) = t n)
End

Definition sdest_def:   sdest = \s. (shd s, stl s)
End

Definition sconst_def:   sconst = (K : 'a -> num -> 'a)
End

Definition stake_def:
   (stake 0 s = []) /\ (stake (SUC n) s = shd s :: stake n (stl s))
End

Definition sdrop_def:   (sdrop 0 = I) /\ (sdrop (SUC n) = sdrop n o stl)
End

Definition eventually_def:   eventually x y = ?n. sdrop n x = sdrop n y
End

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

Theorem STL_PARTIAL:
     !f. stl f = f o SUC
Proof
   FUN_EQ_TAC
   >> RW_TAC std_ss [stl_def, o_DEF]
QED

Theorem SCONS_SURJ:
     !x. ?h t. (x = scons h t)
Proof
   STRIP_TAC
   >> EXISTS_TAC ``shd x``
   >> EXISTS_TAC ``stl x``
   >> FUN_EQ_TAC
   >> Cases >- RW_TAC std_ss [scons_def, shd_def]
   >> RW_TAC std_ss [scons_def, stl_def]
QED

Theorem SHD_STL_ISO:
     !h t. ?x. (shd x = h) /\ (stl x = t)
Proof
   REPEAT STRIP_TAC
   >> Q.EXISTS_TAC `\x. num_CASE x h t`
   >> RW_TAC arith_ss [shd_def]
   >> MATCH_MP_TAC EQ_EXT
   >> Cases >- RW_TAC std_ss [stl_def]
   >> RW_TAC std_ss [stl_def]
QED

Theorem SHD_SCONS:
     !h t. shd (scons h t) = h
Proof
   RW_TAC arith_ss [shd_def, scons_def]
QED

Theorem STL_SCONS:
     !h t. stl (scons h t) = t
Proof
   Suff `!h t n. stl (scons h t) n = t n` >- PROVE_TAC [EQ_EXT]
   >> RW_TAC arith_ss [stl_def, scons_def]
QED

Theorem SHD_SCONST:
     !b. shd (sconst b) = b
Proof
   RW_TAC std_ss [sconst_def, K_DEF, shd_def]
QED

Theorem STL_SCONST:
     !b. stl (sconst b) = sconst b
Proof
   STRIP_TAC
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [sconst_def, K_DEF, stl_def]
QED

Theorem SCONS_SHD_STL:
     !x. scons (shd x) (stl x) = x
Proof
   STRIP_TAC
   >> FUN_EQ_TAC
   >> Cases >- RW_TAC std_ss [scons_def, shd_def]
   >> RW_TAC std_ss [scons_def, stl_def]
QED

Theorem FST_o_SDEST:
     FST o sdest = shd
Proof
   FUN_EQ_TAC
   >> RW_TAC std_ss [sdest_def, o_THM]
QED

Theorem SND_o_SDEST:
     SND o sdest = stl
Proof
   FUN_EQ_TAC
   >> RW_TAC std_ss [sdest_def, o_THM]
QED

Theorem SEQUENCE_DEFINE:
     !phd ptl. ?g.
       (!(x : 'a). shd (g x) = phd x) /\ (!(x : 'a). stl (g x) = g (ptl x))
Proof
   RW_TAC std_ss []
   >> Q.EXISTS_TAC `\x n. phd (FUNPOW ptl n x)`
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [shd_def, stl_def, FUNPOW]
QED

Theorem SCONS_EQ:
     !x xs y ys. (scons x xs = scons y ys) = (x = y) /\ (xs = ys)
Proof
   RW_TAC std_ss []
   >> REVERSE EQ_TAC >- PROVE_TAC []
   >> PROVE_TAC [SHD_SCONS, STL_SCONS]
QED

Theorem STL_o_SDROP:
     !n. stl o sdrop n = sdrop (SUC n)
Proof
   Induct >- RW_TAC bool_ss [sdrop_def, I_o_ID]
   >> RW_TAC bool_ss [sdrop_def, o_ASSOC]
QED

Theorem SDROP_ADD:
     !s x y. sdrop (x + y) s = sdrop x (sdrop y s)
Proof
   Induct_on `y` >- RW_TAC list_ss [sdrop_def, I_THM]
   >> RW_TAC std_ss [ADD_CLAUSES, sdrop_def, o_THM]
QED

Theorem SDROP_EQ_MONO:
   !m n x y. (sdrop m x = sdrop m y) /\ m <= n ==> (sdrop n x = sdrop n y)
Proof
   RW_TAC std_ss [LESS_EQ_EXISTS]
   >> rename [‘sdrop (m + p) x = sdrop (m + p) y’]
   >> Induct_on `p` >- RW_TAC arith_ss []
   >> RW_TAC std_ss [ADD_CLAUSES, GSYM STL_o_SDROP, o_THM]
QED

Theorem EVENTUALLY_REFL:
     !x. eventually x x
Proof
   RW_TAC std_ss [eventually_def]
QED

Theorem EVENTUALLY_SYM:
     !x y. eventually x y = eventually y x
Proof
   RW_TAC std_ss [eventually_def]
   >> PROVE_TAC []
QED

Theorem EVENTUALLY_TRANS:
     !x y z. eventually x y /\ eventually y z ==> eventually x z
Proof
   RW_TAC std_ss [eventually_def]
   >> Q.EXISTS_TAC `MAX n n'`
   >> PROVE_TAC [X_LE_MAX, LESS_EQ_REFL, SDROP_EQ_MONO]
QED

Theorem SEQUENCE_DEFINE_ALT:
     !phd ptl. ?g:'a->num->'b. !x. g x = scons (phd x) (g (ptl x))
Proof
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`phd`, `ptl`] SEQUENCE_DEFINE)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `g`
   >> RW_TAC std_ss []
   >> MP_TAC (Q.ISPEC `(g:'a->num->'b) x` SCONS_SURJ)
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
   >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
   >> RW_TAC std_ss [SCONS_EQ, SHD_SCONS, STL_SCONS]
QED

local
  val th =  prove
    (``?s. !h t x. s h t x = scons (h x) (s h t (t x))``,
     MP_TAC SEQUENCE_DEFINE_ALT
     >> RW_TAC std_ss [SKOLEM_THM])
in
  val siter_def = new_specification ("siter_def", ["siter"], th);
end;

Theorem SHD_SITER:
     !h t x. shd (siter h t x) = h x
Proof
   ONCE_REWRITE_TAC [siter_def]
   >> RW_TAC std_ss [SHD_SCONS]
QED

Theorem STL_SITER:
     !h t x. stl (siter h t x) = siter h t (t x)
Proof
   RW_TAC std_ss []
   >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [siter_def]))
   >> RW_TAC std_ss [STL_SCONS]
QED

