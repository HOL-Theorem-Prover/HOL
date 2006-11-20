(* ========================================================================= *)
(* Create "expectationTheory" setting up the theory of expectations          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
val () = app load
  ["bossLib", "realLib", "metisLib", "posetTheory", "posrealLib"]
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib realLib;
open combinTheory arithmeticTheory realTheory seqTheory;
open posetTheory posrealTheory posrealLib;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "expectation"                                   *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "expectation";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;

(* ------------------------------------------------------------------------- *)
(* The HOL types we use to model expectation transformers                    *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("expect", Type `:'a -> posreal`);

val () = type_abbrev ("trans", Type `:'a expect -> 'a expect`);

(* ------------------------------------------------------------------------- *)
(* Expectations bounded by 1 are useful enough to justify defining expect1   *)
(* ------------------------------------------------------------------------- *)

val expect_def = Define `expect e = T`;

val expect1_def = Define `expect1 (e : 'a expect) = !s. e s <= 1`;

(* ------------------------------------------------------------------------- *)
(* Lifting boolean operators to expectations                                 *)
(* ------------------------------------------------------------------------- *)

val Zero_def = Define `(Zero : 'a expect) = \s. 0`;

val One_def = Define `(One : 'a expect) = \s. 1`;

val Magic_def = Define `(Magic : 'a expect) = \s. infty`;

val Compl_def = Define `Compl (e : 'a expect) = \s. 1 - e s`;

val Min_def = Define `Min (e : 'a expect) f = \s. min (e s) (f s)`;

val Max_def = Define `Max (e : 'a expect) f = \s. max (e s) (f s)`;

val Conj_def = Define `Conj (e : 'a expect) f = \s. (e s + f s) - 1`;

val Implies_def = Define `Implies (e : 'a expect) f = \s. 1 - (e s - f s)`;

val Leq_def = Define `Leq (e : 'a expect) f = !s. e s <= f s`;

val Geq_def = Define `Geq (e : 'a expect) f = Leq f e`;

val expect1_compl = store_thm
  ("expect1_compl",
   ``!e. expect1 e ==> expect1 (Compl e)``,
   RW_TAC std_ss
   [expect1_def, Compl_def, sub_decrease, posreal_of_num_not_infty]);

val compl_compl = store_thm
  ("compl_compl",
   ``!e. expect1 e ==> (Compl (Compl e) = e)``,
   RW_TAC std_ss [Compl_def, expect1_def]
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC sub_sub2
   ++ RW_TAC std_ss [posreal_of_num_def, preal_not_infty]);

val leq_refl = store_thm
  ("leq_refl",
   ``!e. Leq e e``,
   RW_TAC std_ss [Leq_def, le_refl]);

val leq_antisym = store_thm
  ("leq_antisym",
   ``!e f. Leq e f /\ Leq f e ==> (e = f)``,
   RW_TAC real_ss [Leq_def]
   ++ CONV_TAC FUN_EQ_CONV
   ++ PROVE_TAC [le_antisym]);

val leq_trans = store_thm
  ("leq_trans",
   ``!e f g. Leq e f /\ Leq f g ==> Leq e g``,
   RW_TAC real_ss [Leq_def]
   ++ PROVE_TAC [le_trans]);

val leq_compl = store_thm
  ("leq_compl",
   ``!e f. expect1 e /\ expect1 f ==> (Leq e (Compl f) = Leq f (Compl e))``,
   RW_TAC real_ss
   [Leq_def, Compl_def, le_sub_ladd, posreal_of_num_not_infty, expect1_def]
   ++ PROVE_TAC [add_comm]);

val leq_compl_2 = store_thm
  ("leq_compl_2",
   ``!e f. expect1 e /\ expect1 f ==> (Leq (Compl e) (Compl f) = Leq f e)``,
   PROVE_TAC [compl_compl, leq_compl, expect1_compl]);

val min_alt = store_thm
  ("min_alt",
   ``!e f s. Min e f s = min (e s) (f s)``,
   RW_TAC std_ss [Min_def]);

val refl_min = store_thm
  ("refl_min",
   ``!x. Min x x = x``,
   GEN_TAC
   ++ CONV_TAC FUN_EQ_CONV
   ++ RW_TAC std_ss [Min_def, min_refl]);

val leq_min = store_thm
  ("leq_min",
   ``!e f g. Leq e (Min f g) = Leq e f /\ Leq e g``,
   RW_TAC real_ss [Leq_def, Min_def, preal_min_def]
   ++ PROVE_TAC [le_trans, le_total]);

val leq_min1 = store_thm
  ("leq_min1",
   ``!x y. Leq (Min x y) x``,
   RW_TAC real_ss [Leq_def, Min_def, min_le1]);

val leq_min2 = store_thm
  ("leq_min2",
   ``!x y. Leq (Min x y) y``,
   RW_TAC real_ss [Leq_def, Min_def, min_le2]);

val min_leq2_imp = store_thm
  ("min_leq2_imp",
   ``!x1 x2 y1 y2. Leq x1 y1 /\ Leq x2 y2 ==> Leq (Min x1 x2) (Min y1 y2)``,
   RW_TAC std_ss [Leq_def, Min_def]
   ++ PROVE_TAC [min_le2_imp]);

val max_leq = store_thm
  ("max_leq",
   ``!e f g. Leq (Max f g) e = Leq f e /\ Leq g e``,
   RW_TAC real_ss [Leq_def, Max_def, preal_max_def]
   ++ PROVE_TAC [le_trans, le_total]);

val leq_max1 = store_thm
  ("leq_max1",
   ``!x y. Leq x (Max x y)``,
   RW_TAC real_ss [Leq_def, Max_def, le_max1]);

val leq_max2 = store_thm
  ("leq_max2",
   ``!x y. Leq y (Max x y)``,
   RW_TAC real_ss [Leq_def, Max_def, le_max2]);

val max_leq2_imp = store_thm
  ("max_leq2_imp",
   ``!x1 x2 y1 y2. Leq x1 y1 /\ Leq x2 y2 ==> Leq (Max x1 x2) (Max y1 y2)``,
   RW_TAC std_ss [Leq_def, Max_def]
   ++ PROVE_TAC [max_le2_imp]);

val expect1_basic = store_thm
  ("expect1_basic",
   ``expect1 Zero /\ expect1 One``,
   RW_TAC real_ss [expect1_def, Zero_def, One_def, le_refl, zero_le]);

val zero_leq = store_thm
  ("zero_leq",
   ``!e. Leq Zero e``,
   RW_TAC real_ss [Leq_def, Zero_def, zero_le]);

val leq_zero = store_thm
  ("leq_zero",
   ``!e. Leq e Zero = (e = Zero)``,
   RW_TAC real_ss [Leq_def, Zero_def]
   ++ CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ METIS_TAC [le_zero]);

val magic_alt = store_thm
  ("magic_alt",
   ``!s. Magic s = infty``,
   RW_TAC std_ss [Magic_def]);

val leq_magic = store_thm
  ("leq_magic",
   ``!e. Leq e Magic``,
   RW_TAC real_ss [Leq_def, Magic_def, le_infty]);

val magic_leq = store_thm
  ("magic_leq",
   ``!e. Leq Magic e = (e = Magic)``,
   RW_TAC real_ss [Leq_def, Magic_def, infty_le]
   ++ METIS_TAC []);

val expect1_leq_one = store_thm
  ("expect1_leq_one",
   ``!e. expect1 e ==> Leq e One``,
   RW_TAC real_ss [Leq_def, One_def, expect1_def]);

val expect1_min = store_thm
  ("expect1_min",
   ``!e f. expect1 e \/ expect1 f ==> expect1 (Min e f)``,
   RW_TAC std_ss [expect1_def, Min_def, min_le]
   ++ RW_TAC std_ss []);

val expect1_max = store_thm
  ("expect1_max",
   ``!e f. expect1 e /\ expect1 f ==> expect1 (Max e f)``,
   RW_TAC std_ss [expect1_def, Max_def, max_le]);

(* ------------------------------------------------------------------------- *)
(* More complicated operations on expectations                               *)
(* ------------------------------------------------------------------------- *)

val Lin_def = Define
  `Lin p (a : 'a expect) b s =
   let x = bound1 (p s) in x * a s + (1 - x) * b s`;

val Cond_def = Define
  `Cond c (a : 'a expect) b s = if c s then a s else b s`;

val lin_eta = store_thm
  ("lin_eta",
   ``!p a b.
       Lin p a b = \s. let x = bound1 (p s) in x * a s + (1 - x) * b s``,
   METIS_TAC [Lin_def]);

val lin_refl = store_thm
  ("lin_refl",
   ``!c a. Lin c a a = a``,
   RW_TAC std_ss [Lin_def,FUN_EQ_THM]
   ++ MATCH_MP_TAC le_antisym
   ++ METIS_TAC [bound1,min_refl,max_refl,lin_le_max,min_le_lin]);

val cond_eta = store_thm
  ("cond_eta",
   ``!c a b. Cond c a b = \s. if c s then a s else b s``,
   METIS_TAC [Cond_def]);

val cond_refl = store_thm
  ("cond_refl",
   ``!c a. Cond c a a = a``,
   RW_TAC std_ss [Cond_def,FUN_EQ_THM]);

val leq_cond_imp = store_thm
  ("leq_cond_imp",
   ``!c a b a' b'.
       Leq a a' /\ Leq b b' ==> Leq (Cond c a b) (Cond c a' b')``,
   RW_TAC std_ss [Leq_def,Cond_def]
   ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Fundamental properties of expectation transformers                        *)
(* ------------------------------------------------------------------------- *)

(* Feasibility is sometimes called strictness. It's related to strictness *)
(* in functional programming, where a language is strict if whenever an   *)
(* argument to a function diverges, then so does the function.            *)
val feasible_def = Define
  `feasible (trans : 'a trans) = (trans Zero = Zero)`;

(* Sublinearity ensures the range of expectations is convex *)
val sublinear_def = Define
  `sublinear (trans : 'a trans) =
   !r1 r2 c1 c2 c s.
     ~(c = infty) ==>
     c1 * trans r1 s + c2 * trans r2 s - c <=
     trans (\s'. c1 * r1 s' + c2 * r2 s' - c) s`;

(* We also study up-continuity, which we write directly as *)
(*   up_continuous (expect,Leq)                            *)
(* This ensures the range of expectations is closed (i.e., *)
(* contains all it's limit points).                        *)

(* ------------------------------------------------------------------------- *)
(* Useful consequences of these properties                                   *)
(* ------------------------------------------------------------------------- *)

val sublinear_alt = store_thm
  ("sublinear_alt",
   ``!trans.
       sublinear trans =
       (!c r s. ~(c = infty) ==> trans r s - c <= trans (\s'. r s' - c) s) /\
       (!c r s. c * trans r s <= trans (\s'. c * r s') s) /\
       !r1 r2 s. trans r1 s + trans r2 s <= trans (\s'. r1 s' + r2 s') s``,
   RW_TAC std_ss [sublinear_def]
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       << [Q.PAT_ASSUM `!r. P r` (MP_TAC o Q.SPECL [`r`, `r`, `1`, `0`, `c`])
           ++ RW_TAC posreal_ss [],
           Q.PAT_ASSUM `!r. P r` (MP_TAC o Q.SPECL [`r`, `r`, `c`, `0`, `0`])
           ++ RW_TAC posreal_ss [],
           Q.PAT_ASSUM `!r. P r` (MP_TAC o Q.SPECL [`r1`, `r2`, `1`, `1`, `0`])
           ++ RW_TAC posreal_ss []])
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC le_trans
   ++ Q.EXISTS_TAC `trans (\s'. c1 * r1 s' + c2 * r2 s') s - c`
   ++ REVERSE CONJ_TAC >> (FIRST_ASSUM HO_MATCH_MP_TAC ++ RW_TAC std_ss [])
   ++ MATCH_MP_TAC sub_mono
   ++ RW_TAC std_ss []
   ++ MATCH_MP_TAC le_trans
   ++ Q.EXISTS_TAC `trans (\s'. c1 * r1 s') s + trans (\s'. c2 * r2 s') s`
   ++ REVERSE CONJ_TAC >> FIRST_ASSUM HO_MATCH_ACCEPT_TAC
   ++ MATCH_MP_TAC le_add2
   ++ CONJ_TAC
   ++ FIRST_ASSUM HO_MATCH_ACCEPT_TAC);

val sublinear_zero = store_thm
  ("sublinear_zero",
   ``!t x. sublinear t ==> (t Zero x = 0) \/ (t Zero x = infty)``,
   RW_TAC std_ss [Zero_def, Magic_def, sublinear_def]
   ++ Q.PAT_ASSUM `!x. P x`
      (MP_TAC o Q.SPECL [`\s. 0`, `\s. 0`, `1`, `1`, `0`, `x`])
   ++ RW_TAC posreal_ss []);

val sublinear_expect1 = store_thm
  ("sublinear_expect1",
   ``!t r. feasible t /\ sublinear t /\ expect1 r ==> expect1 (t r)``,
   RW_TAC std_ss [sublinear_def]
   ++ RW_TAC std_ss [expect1_def]
   ++ Q.PAT_ASSUM `!r. P r` (MP_TAC o Q.SPECL [`r`, `Zero`, `1`, `0`, `1`, `s`])
   ++ RW_TAC posreal_ss []
   ++ POP_ASSUM MP_TAC
   ++ Know `t (\s'. r s' - 1) = Zero`
   >> (Suff `(\s'. r s' - 1) = Zero`
       >> (SIMP_TAC std_ss [] ++ PROVE_TAC [feasible_def])
       ++ CONV_TAC FUN_EQ_CONV
       ++ RW_TAC std_ss [Zero_def]
       ++ MATCH_MP_TAC le_imp_sub_zero
       ++ RW_TAC posreal_ss []
       ++ PROVE_TAC [expect1_def])
   ++ DISCH_THEN (fn th => RW_TAC posreal_ss [th, Zero_def])
   ++ MATCH_MP_TAC sub_zero_imp_le
   ++ RW_TAC posreal_ss []);

val sublinear_mono = store_thm
  ("sublinear_mono",
   ``!t r1 r2. sublinear t /\ Leq r1 r2 ==> Leq (t r1) (t r2)``,
   RW_TAC std_ss [Leq_def]
   ++ MATCH_MP_TAC le_trans
   ++ Q.EXISTS_TAC
      `t r1 s + t (\s'. if r1 s' = infty then 0 else r2 s' - r1 s') s`
   ++ RW_TAC posreal_ss []
   ++ Q.UNDISCH_TAC `sublinear t`
   ++ RW_TAC std_ss [sublinear_def]
   ++ Q.PAT_ASSUM `!r1 r2. P r1 r2`
      (MP_TAC o Q.SPECL
       [`r1`, `\s'. if r1 s' = infty then 0 else r2 s' - r1 s'`,
        `1`, `1`, `0`, `s`])
   ++ SIMP_TAC posreal_ss []
   ++ Suff `!s'. r1 s' + (if r1 s' = infty then 0 else r2 s' - r1 s') = r2 s'`
   >> RW_TAC (simpLib.++ (real_ss, boolSimps.ETA_ss)) []
   ++ RW_TAC posreal_ss [sub_add2]
   ++ METIS_TAC [infty_le]);

val sublinear_scale = store_thm
  ("sublinear_scale",
   ``!t r c s.
       sublinear t /\ ~(c = 0) /\ ~(c = infty) ==>
       (t (\s'. c * r s') s = c * t r s)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC le_antisym
   ++ POP_ASSUM MP_TAC
   ++ MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ (x ==> z) ==> (x ==> (y /\ z))``)
   ++ POP_ASSUM MP_TAC
   ++ MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ (x ==> z) ==> (x ==> (y /\ z))``)
   ++ Q.SPEC_TAC (`c`, `c`)
   ++ Q.SPEC_TAC (`r`, `r`)
   ++ CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
   ++ MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> y /\ x``)
   ++ CONJ_TAC
   >> (REPEAT GEN_TAC
       ++ Know `sublinear t` >> RW_TAC std_ss []
       ++ SIMP_TAC std_ss [sublinear_def]
       ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `Zero`, `c`, `0`, `0`, `s`])
       ++ RW_TAC posreal_ss [])
   ++ REPEAT STRIP_TAC
   ++ Q.PAT_ASSUM `!r. P r` (MP_TAC o Q.SPECL [`\s'. c * r s'`, `inv c`])
   ++ RW_TAC posreal_ss [mul_linv, GSYM mul_assoc]
   ++ Suff `c * (inv c * t (\s'. c * r s') s) <= c * t r s`
   >> RW_TAC posreal_ss [GSYM mul_assoc, mul_rinv]
   ++ MATCH_MP_TAC le_mul2
   ++ RW_TAC posreal_ss []
   ++ METIS_TAC [combinTheory.I_o_ID]);

val up_continuous_scale = store_thm
  ("up_continuous_scale",
   ``!t r c s.
       sublinear t /\ up_continuous (expect,Leq) t ==>
       (t (\s'. infty * r s') s = infty * t r s)``,
   RW_TAC std_ss [up_continuous_def]
   ++ MATCH_MP_TAC le_antisym
   ++ REVERSE CONJ_TAC
   >> (Q.UNDISCH_TAC `sublinear t`
       ++ SIMP_TAC std_ss [sublinear_def]
       ++ DISCH_THEN (MP_TAC o Q.SPECL [`r`, `Zero`, `infty`, `0`, `0`, `s`])
       ++ RW_TAC posreal_ss [])
   ++ Suff `Leq (t (\s. infty * r s)) (\s. infty * t r s)`
   >> RW_TAC std_ss [Leq_def]
   ++ POP_ASSUM
      (MP_TAC o
       Q.SPECL [`\e. ?n : num. e = \s. & (SUC n) * r s`, `\s. infty * r s`])
   ++ MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
   ++ CONJ_TAC
   >> (CONJ_TAC
       >> (RW_TAC posreal_ss [chain_def, expect_def, Leq_def]
           ++ BETA_TAC
           ++ Suff `& (SUC n) <= & (SUC n') \/ & (SUC n') <= & (SUC n)`
           >> METIS_TAC [le_rmul_imp, le_refl]
           ++ RW_TAC posreal_ss [])
       ++ RW_TAC posreal_ss [lub_def, expect_def, Leq_def]
       >> (BETA_TAC
           ++ MATCH_MP_TAC le_rmul_imp
           ++ RW_TAC posreal_ss [])
       ++ Cases_on `r s = 0` >> RW_TAC posreal_ss []
       ++ Cases_on `r s = infty`
       >> (RW_TAC posreal_ss [mul_linfty]
           ++ Q.PAT_ASSUM `!y. P y` (MP_TAC o Q.SPEC `\s. & (SUC 0) * r s`)
           ++ MATCH_MP_TAC (PROVE [] ``x /\ (y ==> z) ==> (x ==> y) ==> z``)
           ++ CONJ_TAC >> METIS_TAC []
           ++ RW_TAC posreal_ss [GSYM ONE]
           ++ METIS_TAC [infty_le])
       ++ Suff `infty * r s <= z s * inv (r s) * r s`
       >> RW_TAC posreal_ss [mul_linv, mul_assoc]
       ++ MATCH_MP_TAC le_rmul_imp
       ++ RW_TAC std_ss [GSYM sup_num, sup_le]
       ++ Suff `& n * r s * inv (r s) <= z s * inv (r s)`
       >> RW_TAC posreal_ss [mul_rinv, mul_assoc]
       ++ MATCH_MP_TAC le_rmul_imp
       ++ Cases_on `n` >> RW_TAC posreal_ss []
       ++ Q.PAT_ASSUM `!y. P y` (MP_TAC o Q.SPEC `\s. & (SUC n') * r s`)
       ++ METIS_TAC [])
   ++ RW_TAC std_ss [lub_def]
   ++ POP_ASSUM MATCH_MP_TAC
   ++ RW_TAC posreal_ss [expect_def, Leq_def]
   ++ RW_TAC posreal_ss [sublinear_scale]
   ++ MATCH_MP_TAC le_rmul_imp
   ++ RW_TAC posreal_ss []);

(* ------------------------------------------------------------------------- *)
(* Properties of conjunctivity                                               *)
(* ------------------------------------------------------------------------- *)

val conj_id = store_thm
  ("conj_id",
   ``!e. (Conj One e = e) /\ (Conj e One = e)``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC posreal_ss [Conj_def, One_def, Leq_def, add_sub, add_sub2]);

val conj_comm = store_thm
  ("conj_comm",
   ``!e f. Conj e f = Conj f e``,
   RW_TAC std_ss [Conj_def]
   ++ PROVE_TAC [add_comm]);

val conj_nonassoc = store_thm
  ("conj_nonassoc",
   ``?e f g. ~(Conj (Conj e f) g = Conj e (Conj f g))``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ Q.EXISTS_TAC `\s. 0`
   ++ Q.EXISTS_TAC `\s. 0`
   ++ Q.EXISTS_TAC `\s. 2`
   ++ RW_TAC posreal_ss [Conj_def]);

val conj_assoc = store_thm
  ("conj_assoc",
   ``!e f g.
       expect1 e /\ expect1 f /\ expect1 g ==>
       (Conj (Conj e f) g = Conj e (Conj f g))``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   ++ RW_TAC real_ss [Conj_def, expect1_def]
   ++ REPEAT (POP_ASSUM (MP_TAC o Q.SPEC `x`))
   ++ pcases_on `e x` >> RW_TAC posreal_ss []
   ++ pcases_on `f x` >> RW_TAC posreal_ss []
   ++ pcases_on `g x` >> RW_TAC posreal_ss []
   ++ ASM_SIMP_TAC posreal_ss
      [preal_add, posreal_of_num_def, preal_sub]
   ++ RW_TAC posreal_ss [preal_add_eq, preal_le_eq, preal_sub_eq, preal_inj_eq]
   ++ REPEAT CASE_TAC
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC);

val conj_implies_adjunct = store_thm
  ("conj_implies_adjunct",
   ``!e f g.
       expect1 e /\ expect1 f /\ expect1 g ==>
       (Leq (Conj e f) g = Leq e (Implies f g))``,
   RW_TAC std_ss [expect1_def, Leq_def, Conj_def, Implies_def, pos_def]
   ++ EQ_TAC
   ++ REPEAT STRIP_TAC
   ++ REPEAT (POP_ASSUM (MP_TAC o Q.SPEC `s`))
   ++ pcases_on `e s` >> RW_TAC posreal_ss []
   ++ pcases_on `f s` >> RW_TAC posreal_ss []
   ++ pcases_on `g s` >> RW_TAC posreal_ss []
   ++ ASM_SIMP_TAC posreal_ss
      [preal_add, posreal_of_num_def, preal_le_eq, preal_sub]
   ++ RW_TAC posreal_ss [preal_add_eq, preal_sub_eq, preal_inj_eq, preal_le_eq]
   ++ REPEAT CASE_TAC
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC);

val sublinear_conj = store_thm
  ("sublinear_conj",
   ``!t r1 r2. sublinear t ==> Leq (Conj (t r1) (t r2)) (t (Conj r1 r2))``,
   RW_TAC std_ss [Leq_def]
   ++ Know `sublinear t` >> RW_TAC std_ss []
   ++ SIMP_TAC std_ss [sublinear_def]
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`r1`, `r2`, `1`, `1`, `1`, `s`])
   ++ RW_TAC posreal_ss [Conj_def]);

(* ------------------------------------------------------------------------- *)
(* (expect,Leq) is a complete poset                                          *)
(* ------------------------------------------------------------------------- *)

val expect_poset = store_thm
  ("expect_poset",
   ``poset (expect,Leq)``,
   RW_TAC std_ss [poset_def, leq_refl, expect_def]
   ++ PROVE_TAC [leq_antisym, leq_trans]);

val expect_complete = store_thm
  ("expect_complete",
   ``complete (expect,Leq)``,
   MP_TAC (Q.SPECL [`(posreal,(<=))`, `\x. T`]
           (INST_TYPE [alpha |-> ``:posreal``, beta |-> alpha]
            complete_pointwise))
   ++ SIMP_TAC std_ss [posreal_complete]
   ++ RW_TAC std_ss
      [expect_def, GSYM Leq_def, pointwise_lift_def,
       function_def, complete_def, posreal_def, lub_def, glb_def]);

val expect_lt_lub = store_thm
  ("expect_lt_lub",
   ``!p x z s. lub (expect,Leq) p x /\ z s < x s ==> ?y. p y /\ z s < y s``,
   RW_TAC std_ss [lub_def, Leq_def, expect_def]
   ++ Suff `~!y. p y ==> y s <= z s` >> SIMP_TAC real_ss [preal_lt_def]
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `!z. (!y. P y z) ==> Q z` MP_TAC
   ++ ASM_SIMP_TAC std_ss []
   ++ Q.EXISTS_TAC `\e. if e = s then z s else x e`
   ++ CONJ_TAC >> (RW_TAC real_ss [] ++ RW_TAC real_ss [])
   ++ Q.EXISTS_TAC `s`
   ++ RW_TAC real_ss [GSYM preal_lt_def]);

val expect_monotonic_min = store_thm
  ("expect_monotonic_min",
   ``!t1 t2.
       monotonic (expect,Leq) t1 /\ monotonic (expect,Leq) t2 ==>
       monotonic (expect,Leq) (\e. Min (t1 e) (t2 e))``,
   RW_TAC real_ss [monotonic_def, expect_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPECL [`e`, `e'`]))
   ++ ASM_REWRITE_TAC []
   ++ METIS_TAC [min_leq2_imp]);

val expect_monotonic_max = store_thm
  ("expect_monotonic_max",
   ``!t1 t2.
       monotonic (expect,Leq) t1 /\ monotonic (expect,Leq) t2 ==>
       monotonic (expect,Leq) (\e. Max (t1 e) (t2 e))``,
   RW_TAC real_ss [monotonic_def, expect_def]
   ++ REPEAT (Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPECL [`e`, `e'`]))
   ++ ASM_REWRITE_TAC []
   ++ METIS_TAC [max_leq2_imp]);

(* ------------------------------------------------------------------------- *)
(* Fixed points of expectation transformers                                  *)
(* ------------------------------------------------------------------------- *)

val expect_lfp_exists = store_thm
  ("expect_lfp_exists",
   ``!phi. monotonic (expect,Leq) phi ==> ?g. lfp (expect,Leq) phi g``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC (INST_TYPE [alpha |-> ``:'a expect``] knaster_tarski_lfp)
   ++ RW_TAC std_ss [expect_poset, expect_complete]
   ++ RW_TAC std_ss [carrier_def, expect_def, function_def]);

val expect_lfp_def = new_specification
  ("expect_lfp_def", ["expect_lfp"],
   CONV_RULE (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)
   expect_lfp_exists);

val sublinear_lfp = store_thm
  ("sublinear_lfp",
   ``!phi. sublinear phi ==> lfp (expect,Leq) phi (expect_lfp phi)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC expect_lfp_def
   ++ SIMP_TAC std_ss [monotonic_def]
   ++ SIMP_TAC std_ss [expect_def]
   ++ PROVE_TAC [sublinear_mono]);

val expect_lfp_eq = store_thm
  ("expect_lfp_eq",
   ``!t e. (monotonic (expect, Leq) t) /\ 
	   (lfp (expect, Leq) t e) ==> 
	   (expect_lfp t = e)``,
   METIS_TAC [lfp_unique, expect_poset, expect_lfp_def]);

val expect_gfp_exists = store_thm
  ("expect_gfp_exists",
   ``!phi. monotonic (expect,Leq) phi ==> ?g. gfp (expect,Leq) phi g``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC (INST_TYPE [alpha |-> ``:'a expect``] knaster_tarski_gfp)
   ++ RW_TAC std_ss [expect_poset, expect_complete]
   ++ RW_TAC std_ss [carrier_def, expect_def, function_def]);

val expect_gfp_def = new_specification
  ("expect_gfp_def", ["expect_gfp"],
   CONV_RULE (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)
   expect_gfp_exists);

val sublinear_gfp = store_thm
  ("sublinear_gfp",
   ``!phi. sublinear phi ==> gfp (expect,Leq) phi (expect_gfp phi)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC expect_gfp_def
   ++ SIMP_TAC std_ss [monotonic_def]
   ++ SIMP_TAC std_ss [expect_def]
   ++ PROVE_TAC [sublinear_mono]);

val expect_gfp_eq = store_thm
  ("expect_gfp_eq",
   ``!t e. (monotonic (expect, Leq) t) /\ 
	   (gfp (expect, Leq) t e) ==> 
	   (expect_gfp t = e)``,
   METIS_TAC [gfp_unique, expect_poset, expect_gfp_def]);

(* ------------------------------------------------------------------------- *)
(* Refinement                                                                *)
(* ------------------------------------------------------------------------- *)

val refines_def = Define `refines t1 t2 = !r. Leq (t1 r) (t2 r)`;

val refines_refl = store_thm
  ("refines_refl",
   ``!t. refines t t``,
   METIS_TAC [refines_def, leq_refl]);

val refines_trans = store_thm
  ("refines_trans",
   ``!t1 t2 t3. refines t1 t2 /\ refines t2 t3 ==> refines t1 t3``,
   METIS_TAC [refines_def, leq_trans]);

val refines_zero = store_thm
  ("refines_zero",
   ``!t. refines (\r. Zero) t``,
   RW_TAC std_ss [refines_def, zero_leq]);

val refines_lfp = store_thm
  ("refines_lfp",
   ``!t1 t2.
        monotonic (expect,Leq) t1 /\ monotonic (expect,Leq) t2 /\
        refines t1 t2 ==> Leq (expect_lfp t1) (expect_lfp t2)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `t1` expect_lfp_def)
   ++ MP_TAC (Q.SPEC `t2` expect_lfp_def)
   ++ RW_TAC std_ss [lfp_def]
   ++ FIRST_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `refines X Y` MP_TAC
   ++ SIMP_TAC std_ss [refines_def]
   ++ DISCH_THEN (MP_TAC o Q.SPEC `expect_lfp t2`)
   ++ ASM_SIMP_TAC std_ss []);

val refines_gfp = store_thm
  ("refines_gfp",
   ``!t1 t2.
        monotonic (expect,Leq) t1 /\ monotonic (expect,Leq) t2 /\
        refines t1 t2 ==> Leq (expect_gfp t1) (expect_gfp t2)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `t1` expect_gfp_def)
   ++ MP_TAC (Q.SPEC `t2` expect_gfp_def)
   ++ RW_TAC std_ss [gfp_def]
   ++ FIRST_ASSUM MATCH_MP_TAC
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `refines X Y` MP_TAC
   ++ SIMP_TAC std_ss [refines_def]
   ++ DISCH_THEN (MP_TAC o Q.SPEC `expect_gfp t1`)
   ++ ASM_SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* The healthiness condition.                                                *)
(*                                                                           *)
(* This is the right property to study, because the set of healthy           *)
(* expectation transformers is precisely the set of expectation              *)
(* transformers that arise from relations in the operational model.          *)
(* ------------------------------------------------------------------------- *)

val healthy_def = Define
  `healthy trans =
   feasible trans /\ sublinear trans /\ up_continuous (expect,Leq) trans`;

(* ------------------------------------------------------------------------- *)
(* Continuity does not follow from feasibility and sublinearity.             *)
(*                                                                           *)
(* This follows from the following 'program':                                *)
(*                                                                           *)
(*   Demon { Assign "v" n | n is a natural number }                          *)
(*                                                                           *)
(* Of course, this can't be made into a real program because the syntax      *)
(* doesn't support infinite demonic choice.                                  *)
(* ------------------------------------------------------------------------- *)

val continuity_not_redundant = store_thm
  ("continuity_not_redundant",
   ``?t : num trans.
       feasible t /\ sublinear t /\ ~up_continuous (expect,Leq) t``,
   Q.EXISTS_TAC `\e s. inf (\r. ?n. e n = r)`
   ++ RW_TAC real_ss [feasible_def, sublinear_def, up_continuous_def]
   << [CONV_TAC FUN_EQ_CONV
       ++ RW_TAC std_ss [Zero_def, GSYM le_zero, inf_le]
       ++ POP_ASSUM MATCH_MP_TAC
       ++ RW_TAC std_ss [le_refl],
       RW_TAC std_ss [le_inf]
       ++ MATCH_MP_TAC sub_mono
       ++ RW_TAC real_ss []
       ++ MATCH_MP_TAC le_add2
       ++ CONJ_TAC
       ++ MATCH_MP_TAC le_lmul_imp
       ++ MATCH_MP_TAC inf_le_imp
       ++ BETA_TAC
       ++ PROVE_TAC [],
       Q.EXISTS_TAC `\p. ?n. p = \m. if m < n then 1 else 0`
       ++ Q.EXISTS_TAC `One`
       ++ REWRITE_TAC [GSYM CONJ_ASSOC]
       ++ CONJ_TAC
       >> (RW_TAC real_ss [chain_def, Leq_def, expect_def]
           ++ MATCH_MP_TAC (PROVE [] ``(~x ==> y) ==> x \/ y``)
           ++ RW_TAC std_ss []
           ++ RW_TAC real_ss [le_refl, zero_le]
           ++ Q.PAT_ASSUM `~(x <= y)` MP_TAC
           ++ RW_TAC real_ss [le_refl, zero_le])
       ++ CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)
       ++ SIMP_TAC real_ss [expect_def, Leq_def, lub_def, One_def, CONJ_ASSOC]
       ++ CONJ_TAC
       >> (RW_TAC std_ss [] >> METIS_TAC [zero_le, le_refl]
           ++ POP_ASSUM (MP_TAC o Q.SPEC `\m. if m < SUC s then 1 else 0`)
           ++ MATCH_MP_TAC (PROVE [] ``(y ==> z) /\ x ==> (x ==> y) ==> z``)
           ++ BETA_TAC
           ++ CONJ_TAC >> PROVE_TAC [prim_recTheory.LESS_SUC_REFL]
           ++ Q.EXISTS_TAC `SUC s`
           ++ RW_TAC real_ss [])
       ++ DISJ2_TAC
       ++ Q.EXISTS_TAC `Zero`
       ++ RW_TAC real_ss [Zero_def]
       >> (RW_TAC std_ss []
           ++ MATCH_MP_TAC inf_le_imp
           ++ RW_TAC std_ss []
           ++ METIS_TAC [le_refl, prim_recTheory.LESS_REFL])
       ++ RW_TAC std_ss [inf_le, posreal_of_num_not_infty, GSYM le_zero]
       ++ Q.EXISTS_TAC `1 / 2`
       ++ RW_TAC std_ss [GSYM preal_lt_def, half_between]]);

(* ------------------------------------------------------------------------- *)
(* Healthy transformers automatically inherit all the useful consequences of *)
(* feasibility, sublinearity and continuity.                                 *)
(* ------------------------------------------------------------------------- *)

val healthy_feasible = store_thm
  ("healthy_feasible",
   ``!phi. healthy phi ==> feasible phi``,
   RW_TAC std_ss [healthy_def]);

val healthy_sublinear = store_thm
  ("healthy_sublinear",
   ``!phi. healthy phi ==> sublinear phi``,
   RW_TAC std_ss [healthy_def]);

val healthy_up_continuous = store_thm
  ("healthy_up_continuous",
   ``!phi. healthy phi ==> up_continuous (expect,Leq) phi``,
   RW_TAC std_ss [healthy_def]);

val healthy_expect1 = store_thm
  ("healthy_expect1",
   ``!t r. healthy t /\ expect1 r ==> expect1 (t r)``,
   METIS_TAC [healthy_def, sublinear_expect1]);

val healthy_mono = store_thm
  ("healthy_mono",
   ``!t r1 r2. healthy t /\ Leq r1 r2 ==> Leq (t r1) (t r2)``,
   METIS_TAC [healthy_def, sublinear_mono]);

val healthy_scale = store_thm
  ("healthy_scale",
   ``!t r c s. healthy t ==> (t (\s'. c * r s') s = c * t r s)``,
   RW_TAC std_ss [healthy_def]
   ++ pcases3_on `c`
   << [RW_TAC posreal_ss []
       ++ Know `t Zero = Zero` >> METIS_TAC [feasible_def]
       ++ RW_TAC posreal_ss [Zero_def],
       METIS_TAC [up_continuous_scale],
       METIS_TAC [sublinear_scale, preal_not_infty]]);

val healthy_conj = store_thm
  ("healthy_conj",
   ``!t r1 r2. healthy t ==> Leq (Conj (t r1) (t r2)) (t (Conj r1 r2))``,
   METIS_TAC [healthy_def, sublinear_conj]);

val healthy_lfp = store_thm
  ("healthy_lfp",
   ``!phi. healthy phi ==> lfp (expect,Leq) phi (expect_lfp phi)``,
   METIS_TAC [healthy_sublinear, sublinear_lfp]);

val healthy_gfp = store_thm
  ("healthy_gfp",
   ``!phi. healthy phi ==> gfp (expect,Leq) phi (expect_gfp phi)``,
   METIS_TAC [healthy_sublinear, sublinear_gfp]);

val healthy_zero = store_thm
  ("healthy_zero",
   ``!t. healthy t ==> (t Zero = Zero)``,
   PROVE_TAC [healthy_feasible, feasible_def]);

val healthy_bounded = store_thm
  ("healthy_bounded",
   ``!t r c s. healthy t /\ (!s. r s <= c) ==> t r s <= c``,
   RW_TAC posreal_ss []
   ++ Cases_on `c = infty` >> RW_TAC posreal_ss []
   ++ Know `sublinear t` >> METIS_TAC [healthy_sublinear]
   ++ SIMP_TAC std_ss [sublinear_alt]
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`c`, `r`, `s`] o CONJUNCT1)
   ++ ASM_SIMP_TAC posreal_ss [sub_le_eq]
   ++ Suff `t (\s'. r s' - c) = Zero` >> RW_TAC posreal_ss [Zero_def]
   ++ Know `feasible t` >> METIS_TAC [healthy_feasible]
   ++ SIMP_TAC std_ss [feasible_def]
   ++ Suff `(\s'. r s' - c) = Zero` >> RW_TAC posreal_ss []
   ++ RW_TAC posreal_ss [FUN_EQ_THM, Zero_def]
   ++ MATCH_MP_TAC le_imp_sub_zero
   ++ RW_TAC posreal_ss []);

val healthy_sub = store_thm
  ("healthy_sub",
   ``!t r1 r2 c.
        healthy t /\ ~(c = infty) /\ (!s. r2 s <= c) /\ (!s. r2 s <= r1 s) ==>
        Leq (t (\s. r1 s - r2 s)) (\s. t r1 s - t r2 s)``,
   RW_TAC std_ss [Leq_def]
   ++ Know `!s. ~(r2 s = infty)` >> METIS_TAC [infty_le]
   ++ STRIP_TAC
   ++ Know `!s. t r2 s <= c` >> METIS_TAC [healthy_bounded]
   ++ STRIP_TAC
   ++ Know `!s. ~(t r2 s = infty)` >> METIS_TAC [infty_le]
   ++ STRIP_TAC
   ++ MATCH_MP_TAC le_sub_imp
   ++ RW_TAC posreal_ss []
   ++ Know `sublinear t` >> METIS_TAC [healthy_sublinear]
   ++ SIMP_TAC std_ss [sublinear_def]
   ++ DISCH_THEN (MP_TAC o Q.SPECL[`\s. r1 s - r2 s`, `r2`, `1`, `1`, `0`, `s`])
   ++ ASM_SIMP_TAC posreal_ss [sub_add]
   ++ CONV_TAC (DEPTH_CONV ETA_CONV)
   ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Relational semantics                                                      *)
(* ------------------------------------------------------------------------- *)

(* Prelude: basic measure theory a la examples/miller. *)
(* In time, needs its own theory. For now, just a stub. *)

val () = type_abbrev
  ("measure_space", Type `:(('a -> bool) -> bool) # (('a -> bool) -> posreal)`);

val measure_space_def = Define `measure_space (m : 'a measure_space) = T`;

val measurable_def = Define `measurable ((e,_) : 'a measure_space) = e`;

val measure_def = Define `measure ((_,mu) : 'a measure_space) = mu`;

val integrate_def = Define
  `integrate (m : 'a measure_space) (e : 'a expect) = 0p`;

val subprobability_def = Define
  `subprobability p = measure_space p /\ measure p UNIV <= 1`;

(* Relational semantics in terms of the measure theory above *)

val rel_def = Define
  `rel (r : 'a -> 'a measure_space -> bool) = !s p. r s p ==> subprobability p`;

val wp_rel_def = Define
  `wp_rel (r : 'a -> 'a measure_space -> bool) =
   \e s. inf {x | ?p. r s p /\ (integrate p e = x)}`;

val healthy_rel_def = Define `healthy_rel t = ?r. rel r /\ (t = wp_rel r)`;

(* What we'd really like to prove is that this definition of a healthy *)
(* transformer in terms of relations is the same as the previous *)
(* definition in terms of feasibility, sublinearity and up-continuity. *)

(*
val healthy_rel = prove
  (``!t. healthy_rel t = healthy t``,
   DESIRABLE_TAC);
*)

(* ----- Creates a standard expectation from a condition ------------------- *)

val bool_exp_def = Define
   `bool_exp g = (\s. if g s then (1:posreal) else 0)`;

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
