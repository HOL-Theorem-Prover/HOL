open HolKernel Parse boolLib;
val _ = new_theory "sequence";
val _ = ParseExtras.temp_loose_equality()

open bossLib arithmeticTheory extra_numTheory combinTheory hurdUtils;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val shd_def = Define `shd (f : num -> 'a) = f 0`;

val stl_def = Define `stl (f : num -> 'a) n = f (SUC n)`;

val scons_def = Define
  `(scons (h : 'a) (t : num -> 'a) 0 = h) /\ (scons h t (SUC n) = t n)`;

val sdest_def = Define `sdest = \s. (shd s, stl s)`;

val sconst_def = Define `sconst = (K : 'a -> num -> 'a)`;

val stake_def = Define
  `(stake 0 s = []) /\ (stake (SUC n) s = shd s :: stake n (stl s))`;

val sdrop_def = Define `(sdrop 0 = I) /\ (sdrop (SUC n) = sdrop n o stl)`;

val eventually_def = Define `eventually x y = ?n. sdrop n x = sdrop n y`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val STL_PARTIAL = store_thm
  ("STL_PARTIAL",
   ``!f. stl f = f o SUC``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [stl_def, o_DEF]);

val SCONS_SURJ = store_thm
  ("SCONS_SURJ",
   ``!x. ?h t. (x = scons h t)``,
   STRIP_TAC
   >> EXISTS_TAC ``shd x``
   >> EXISTS_TAC ``stl x``
   >> FUN_EQ_TAC
   >> Cases >- RW_TAC std_ss [scons_def, shd_def]
   >> RW_TAC std_ss [scons_def, stl_def]);

val SHD_STL_ISO = store_thm
  ("SHD_STL_ISO",
   ``!h t. ?x. (shd x = h) /\ (stl x = t)``,
   REPEAT STRIP_TAC
   >> Q.EXISTS_TAC `\x. num_CASE x h t`
   >> RW_TAC arith_ss [shd_def]
   >> MATCH_MP_TAC EQ_EXT
   >> Cases >- RW_TAC std_ss [stl_def]
   >> RW_TAC std_ss [stl_def]);

val SHD_SCONS = store_thm
  ("SHD_SCONS",
   ``!h t. shd (scons h t) = h``,
   RW_TAC arith_ss [shd_def, scons_def]);

val STL_SCONS = store_thm
  ("STL_SCONS",
   ``!h t. stl (scons h t) = t``,
   Suff `!h t n. stl (scons h t) n = t n` >- PROVE_TAC [EQ_EXT]
   >> RW_TAC arith_ss [stl_def, scons_def]);

val SHD_SCONST = store_thm
  ("SHD_SCONST",
   ``!b. shd (sconst b) = b``,
   RW_TAC std_ss [sconst_def, K_DEF, shd_def]);

val STL_SCONST = store_thm
  ("STL_SCONST",
   ``!b. stl (sconst b) = sconst b``,
   STRIP_TAC
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [sconst_def, K_DEF, stl_def]);

val SCONS_SHD_STL = store_thm
  ("SCONS_SHD_STL",
   ``!x. scons (shd x) (stl x) = x``,
   STRIP_TAC
   >> FUN_EQ_TAC
   >> Cases >- RW_TAC std_ss [scons_def, shd_def]
   >> RW_TAC std_ss [scons_def, stl_def]);

val FST_o_SDEST = store_thm
  ("FST_o_SDEST",
   ``FST o sdest = shd``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [sdest_def, o_THM]);

val SND_o_SDEST = store_thm
  ("SND_o_SDEST",
   ``SND o sdest = stl``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [sdest_def, o_THM]);

val SEQUENCE_DEFINE = store_thm
  ("SEQUENCE_DEFINE",
   ``!phd ptl. ?g.
       (!(x : 'a). shd (g x) = phd x) /\ (!(x : 'a). stl (g x) = g (ptl x))``,
   RW_TAC std_ss []
   >> Q.EXISTS_TAC `\x n. phd (FUNPOW ptl n x)`
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [shd_def, stl_def, FUNPOW]);

val SCONS_EQ = store_thm
  ("SCONS_EQ",
   ``!x xs y ys. (scons x xs = scons y ys) = (x = y) /\ (xs = ys)``,
   RW_TAC std_ss []
   >> REVERSE EQ_TAC >- PROVE_TAC []
   >> PROVE_TAC [SHD_SCONS, STL_SCONS]);

val STL_o_SDROP = store_thm
  ("STL_o_SDROP",
   ``!n. stl o sdrop n = sdrop (SUC n)``,
   Induct >- RW_TAC bool_ss [sdrop_def, I_o_ID]
   >> RW_TAC bool_ss [sdrop_def, o_ASSOC]);

val SDROP_ADD = store_thm
  ("SDROP_ADD",
   ``!s x y. sdrop (x + y) s = sdrop x (sdrop y s)``,
   Induct_on `y` >- RW_TAC list_ss [sdrop_def, I_THM]
   >> RW_TAC std_ss [ADD_CLAUSES, sdrop_def, o_THM]);

Theorem SDROP_EQ_MONO:
   !m n x y. (sdrop m x = sdrop m y) /\ m <= n ==> (sdrop n x = sdrop n y)
Proof
   RW_TAC std_ss [LESS_EQ_EXISTS]
   >> rename [‘sdrop (m + p) x = sdrop (m + p) y’]
   >> Induct_on `p` >- RW_TAC arith_ss []
   >> RW_TAC std_ss [ADD_CLAUSES, GSYM STL_o_SDROP, o_THM]
QED

val EVENTUALLY_REFL = store_thm
  ("EVENTUALLY_REFL",
   ``!x. eventually x x``,
   RW_TAC std_ss [eventually_def]);

val EVENTUALLY_SYM = store_thm
  ("EVENTUALLY_SYM",
   ``!x y. eventually x y = eventually y x``,
   RW_TAC std_ss [eventually_def]
   >> PROVE_TAC []);

val EVENTUALLY_TRANS = store_thm
  ("EVENTUALLY_TRANS",
   ``!x y z. eventually x y /\ eventually y z ==> eventually x z``,
   RW_TAC std_ss [eventually_def]
   >> Q.EXISTS_TAC `MAX n n'`
   >> PROVE_TAC [X_LE_MAX, LESS_EQ_REFL, SDROP_EQ_MONO]);

val SEQUENCE_DEFINE_ALT = store_thm
  ("SEQUENCE_DEFINE_ALT",
   ``!phd ptl. ?g:'a->num->'b. !x. g x = scons (phd x) (g (ptl x))``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`phd`, `ptl`] SEQUENCE_DEFINE)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `g`
   >> RW_TAC std_ss []
   >> MP_TAC (Q.ISPEC `(g:'a->num->'b) x` SCONS_SURJ)
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
   >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
   >> RW_TAC std_ss [SCONS_EQ, SHD_SCONS, STL_SCONS]);

local
  val th =  prove
    (``?s. !h t x. s h t x = scons (h x) (s h t (t x))``,
     MP_TAC SEQUENCE_DEFINE_ALT
     >> RW_TAC std_ss [SKOLEM_THM])
in
  val siter_def = new_specification ("siter_def", ["siter"], th);
end;

val SHD_SITER = store_thm
  ("SHD_SITER",
   ``!h t x. shd (siter h t x) = h x``,
   ONCE_REWRITE_TAC [siter_def]
   >> RW_TAC std_ss [SHD_SCONS]);

val STL_SITER = store_thm
  ("STL_SITER",
   ``!h t x. stl (siter h t x) = siter h t (t x)``,
   RW_TAC std_ss []
   >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [siter_def]))
   >> RW_TAC std_ss [STL_SCONS]);

val _ = export_theory ();
