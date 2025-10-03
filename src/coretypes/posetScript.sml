(* ========================================================================= *)
(* Create "posetTheory" for reasoning about arbitrary partial orders.        *)
(* Originally created by Joe Hurd to support the pGCL formalization.         *)
(* ========================================================================= *)
Theory poset[bare]
Ancestors
  pair
Libs
  HolKernel Parse boolLib pairLib BasicProvers metisLib simpLib


(* ------------------------------------------------------------------------- *)
(* Start a new theory called "poset"                                         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

val Know = Q_TAC KNOW_TAC;

val bool_ss = boolSimps.bool_ss;
val pair_cases_tac = MATCH_ACCEPT_TAC ABS_PAIR_THM;

fun UNPRIME_CONV tmp =
  let
    val (vp,b) = dest_abs tmp
    val (sp,ty) = dest_var vp
    val v = mk_var (unprime sp, ty)
    val tm = mk_abs (v, subst [vp |-> v] b)
  in
    ALPHA tmp tm
  end;

(* ------------------------------------------------------------------------- *)
(* Functions from one predicate to another                                   *)
(* NOTE: this is actually pred_setTheory.FUNSET                              *)
(* ------------------------------------------------------------------------- *)

val function_def = new_definition
  ("function_def",
   ``function a b (f : 'a -> 'b) = !x. a x ==> b (f x)``);

Theorem function_in:
    function s s t /\ s x ==> s (t x)
Proof
   RW_TAC (srw_ss()) [function_def]
QED

(* ------------------------------------------------------------------------- *)
(* A HOL type of partial orders                                              *)
(* ------------------------------------------------------------------------- *)

Type poset[pp] = “:('a -> bool) # ('a -> 'a -> bool)”

(* ------------------------------------------------------------------------- *)
(* Definition of partially-ordered sets                                      *)
(* ------------------------------------------------------------------------- *)

val poset_def = new_definition
  ("poset_def",
   ``poset ((s,r) : 'a poset) <=>
     (?x. s x) /\
     (!x. s x ==> r x x) /\
     (!x y. s x /\ s y /\ r x y /\ r y x ==> (x = y)) /\
     (!x y z. s x /\ s y /\ s z /\ r x y /\ r y z ==> r x z)``);

val carrier_def = new_definition
  ("carrier_def",
   ``carrier ((s,r) : 'a poset) = s``);

val relation_def = new_definition
  ("relation_def",
   ``relation ((s,r) : 'a poset) = r``);

val _ = export_rewrites ["carrier_def", "relation_def"];

val top_def = new_definition
  ("top_def",
   ``top ((s,r) : 'a poset) x <=> s x /\ !y. s y ==> r y x``);

val bottom_def = new_definition
  ("bottom_def",
   ``bottom ((s,r) : 'a poset) x <=> s x /\ !y. s y ==> r x y``);

val chain_def = new_definition
  ("chain_def",
   ``chain ((s,r) : 'a poset) c <=>
     !x y. s x /\ s y /\ c x /\ c y ==> r x y \/ r y x``);

val lub_def = new_definition
  ("lub_def",
   ``lub ((s,r) : 'a poset) p x <=>
     s x /\ (!y. s y /\ p y ==> r y x) /\
     !z. s z /\ (!y. s y /\ p y ==> r y z) ==> r x z``);

val glb_def = new_definition
  ("glb_def",
   ``glb ((s,r) : 'a poset) p x <=>
     s x /\ (!y. s y /\ p y ==> r x y) /\
     !z. s z /\ (!y. s y /\ p y ==> r z y) ==> r z x``);

val complete_def = new_definition
  ("complete_def",
   ``complete (p : 'a poset) = !c. (?x. lub p c x) /\ (?x. glb p c x)``);

Theorem poset_nonempty:
     !s r. poset (s,r) ==> ?x. s x
Proof
   RW_TAC bool_ss [poset_def]
QED

Theorem poset_refl:
     !s r x. poset (s,r) /\ s x ==> r x x
Proof
   RW_TAC bool_ss [poset_def]
QED

Theorem poset_antisym:
     !s r x y.
       poset (s,r) /\ s x /\ s y /\ r x y /\ r y x ==> (x = y)
Proof
   RW_TAC bool_ss [poset_def]
QED

Theorem poset_trans:
     !s r x y z.
       poset (s,r) /\ s x /\ s y /\ s z /\ r x y /\ r y z ==> r x z
Proof
   RW_TAC bool_ss [poset_def] >> RES_TAC
QED

Theorem lub_pred:
     !s r p x. lub (s,r) (\j. s j /\ p j) x = lub (s,r) p x
Proof
   RW_TAC bool_ss [lub_def]
   >> PROVE_TAC []
QED

Theorem glb_pred:
     !s r p x. glb (s,r) (\j. s j /\ p j) x = glb (s,r) p x
Proof
   RW_TAC bool_ss [glb_def]
   >> PROVE_TAC []
QED

Theorem complete_up:
     !p c. complete p ==> ?x. lub p c x
Proof
   PROVE_TAC [complete_def]
QED

Theorem complete_down:
     !p c. complete p ==> ?x. glb p c x
Proof
   PROVE_TAC [complete_def]
QED

Theorem complete_top:
     !p : 'a poset. poset p /\ complete p ==> ?x. top p x
Proof
   GEN_TAC
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> STRIP_TAC
   >> RW_TAC bool_ss [complete_def]
   >> Q.PAT_X_ASSUM `!p. X p` (MP_TAC o Q.SPEC `\x. T`)
   >> RW_TAC bool_ss [lub_def]
   >> Q.EXISTS_TAC `x`
   >> RW_TAC bool_ss [top_def]
QED

Theorem complete_bottom:
     !p : 'a poset. poset p /\ complete p ==> ?x. bottom p x
Proof
   GEN_TAC
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> STRIP_TAC
   >> RW_TAC bool_ss [complete_def]
   >> Q.PAT_X_ASSUM `!p. X p` (MP_TAC o Q.SPEC `\x. T`)
   >> RW_TAC bool_ss [glb_def]
   >> Q.EXISTS_TAC `x'`
   >> RW_TAC bool_ss [bottom_def]
QED

(* ------------------------------------------------------------------------- *)
(* Pointwise lifting of posets                                               *)
(* ------------------------------------------------------------------------- *)

val pointwise_lift_def = new_definition
  ("pointwise_lift_def",
   ``pointwise_lift (t : 'a -> bool) ((s,r) : 'b poset) =
     (function t s, \f g. !x. t x ==> r (f x) (g x))``);

Theorem complete_pointwise:
     !p t. complete p ==> complete (pointwise_lift t p)
Proof
   GEN_TAC
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> STRIP_TAC
   >> RW_TAC bool_ss [complete_def, pointwise_lift_def] >|
   [Know
    `!y.
       t y ==>
       ?l. lub (s,r) (\z. ?f. (!x. t x ==> s (f x)) /\ c f /\ (f y = z)) l`
    >- RW_TAC bool_ss []
    >> DISCH_THEN
       (MP_TAC o CONV_RULE (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV))
    >> RW_TAC bool_ss [lub_def, function_def]
    >> Q.EXISTS_TAC `l`
    >> CONJ_TAC >- METIS_TAC []
    >> CONJ_TAC >- METIS_TAC []
    >> CONV_TAC (DEPTH_CONV UNPRIME_CONV)
    >> RW_TAC bool_ss []
    >> Q.PAT_X_ASSUM `!y. t y ==> P y /\ Q y /\ R y` (MP_TAC o Q.SPEC `x`)
    >> RW_TAC bool_ss []
    >> POP_ASSUM MATCH_MP_TAC
    >> CONJ_TAC >- METIS_TAC []
    >> RW_TAC bool_ss []
    >> Q.PAT_X_ASSUM `!y. P y ==> !x. Q x y` (MP_TAC o Q.SPEC `f`)
    >> MATCH_MP_TAC (PROVE [] ``(y ==> z) /\ x ==> ((x ==> y) ==> z)``)
    >> CONJ_TAC >- METIS_TAC []
    >> METIS_TAC [],
    Know
    `!y.
       t y ==>
       ?l. glb (s,r) (\z. ?f. (!x. t x ==> s (f x)) /\ c f /\ (f y = z)) l`
    >- RW_TAC bool_ss []
    >> DISCH_THEN
       (MP_TAC o CONV_RULE (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV))
    >> RW_TAC bool_ss [glb_def, function_def]
    >> Q.EXISTS_TAC `l`
    >> CONJ_TAC >- METIS_TAC []
    >> CONJ_TAC >- METIS_TAC []
    >> CONV_TAC (DEPTH_CONV UNPRIME_CONV)
    >> RW_TAC bool_ss []
    >> Q.PAT_X_ASSUM `!y. t y ==> P y /\ Q y /\ R y` (MP_TAC o Q.SPEC `x`)
    >> RW_TAC bool_ss []
    >> POP_ASSUM MATCH_MP_TAC
    >> CONJ_TAC >- METIS_TAC []
    >> RW_TAC bool_ss []
    >> Q.PAT_X_ASSUM `!y. P y ==> !x. Q x y` (MP_TAC o Q.SPEC `f'`)
    >> MATCH_MP_TAC (PROVE [] ``(y ==> z) /\ x ==> ((x ==> y) ==> z)``)
    >> CONJ_TAC >- METIS_TAC []
    >> METIS_TAC []]
QED

(*
val lub_pointwise_push = store_thm
  ("lub_pointwise_push",
   ``!p t c l x.
       poset p /\ t x /\ lub (pointwise_lift t p) c l ==>
       lub p
       (\y. ?f. (carrier (pointwise_lift t p) f /\ c f) /\ (y = f x)) (l x)``,
   GEN_TAC
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> STRIP_TAC
   >> RW_TAC bool_ss [lub_def, pointwise_lift_def, carrier_def]
   >> METIS_TAC []
*)

(* ------------------------------------------------------------------------- *)
(* Functions acting on posets.                                               *)
(* ------------------------------------------------------------------------- *)

val monotonic_def = new_definition
  ("monotonic_def",
   ``monotonic ((s,r) : 'a poset) f =
     !x y. s x /\ s y /\ r x y ==> r (f x) (f y)``);

val up_continuous_def = new_definition
  ("up_continuous_def",
   ``up_continuous ((s,r) : 'a poset) f =
     !c x.
       chain (s,r) c /\ lub (s,r) c x ==>
       lub (s,r) (\y. ?z. (s z /\ c z) /\ (y = f z)) (f x)``);

val down_continuous_def = new_definition
  ("down_continuous_def",
   ``down_continuous ((s,r) : 'a poset) f =
     !c x.
       chain (s,r) c /\ glb (s,r) c x ==>
       glb (s,r) (\y. ?z. (s z /\ c z) /\ (y = f z)) (f x)``);

val continuous_def = new_definition
  ("continuous_def",
   “continuous (p : 'a poset) f <=> up_continuous p f /\ down_continuous p f”);


Theorem monotonic_comp:
     monotonic (s,r) f /\ monotonic (s,r) g /\ function s s g
     ==> monotonic (s,r) (f o g)
Proof
   RW_TAC (srw_ss()) [monotonic_def, function_def]
QED

(* ------------------------------------------------------------------------- *)
(* Least and greatest fixed points.                                          *)
(* ------------------------------------------------------------------------- *)

val lfp_def = new_definition
  ("lfp_def",
   ``lfp ((s,r) : 'a poset) f x <=>
     s x /\ (f x = x) /\ !y. s y /\ r (f y) y ==> r x y``);

val gfp_def = new_definition
  ("gfp_def",
   ``gfp ((s,r) : 'a poset) f x <=>
     s x /\ (f x = x) /\ !y. s y /\ r y (f y) ==> r y x``);

Theorem lfp_unique:
     !p f x x'.
        poset p /\ lfp p f x /\ lfp p f x' ==>
        (x = x')
Proof
   GEN_TAC
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> STRIP_TAC
   >> RW_TAC bool_ss [poset_def, lfp_def]
QED

Theorem gfp_unique:
     !p f x x'.
        poset p /\ gfp p f x /\ gfp p f x' ==>
        (x = x')
Proof
   GEN_TAC
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> STRIP_TAC
   >> RW_TAC bool_ss [poset_def, gfp_def]
QED

Theorem lfp_induct:
    lfp (s,r) b lfix /\ s x /\ r (b x) x
    ==> r lfix x
Proof
   RW_TAC bool_ss [lfp_def]
QED

Theorem gfp_coinduct:
    gfp (s,r) b gfix /\ s x /\ r x (b x)
   ==> r x gfix
Proof
   RW_TAC bool_ss [gfp_def]
QED

Theorem glb_unique:
  poset (s,r) /\
  glb (s,r) P x /\ glb (s,r) P y
  ==> x = y
Proof
  RW_TAC bool_ss [glb_def] >>
  drule_then irule poset_antisym >> RW_TAC bool_ss[]
QED

Theorem lub_unique:
  poset (s,r) /\
  lub (s,r) P x /\ lub (s,r) P y
  ==> x = y
Proof
  RW_TAC bool_ss [lub_def] >>
  drule_then irule poset_antisym >> RW_TAC bool_ss[]
QED

(* ------------------------------------------------------------------------- *)
(* The Knaster-Tarski theorem                                                *)
(* ------------------------------------------------------------------------- *)

Theorem knaster_tarski_lfp:
     !p f.
       poset p /\ complete p /\ function (carrier p) (carrier p) f /\
       monotonic p f ==> ?x. lfp p f x
Proof
   RW_TAC bool_ss []
   >> Know `?x. top p x` >- PROVE_TAC [complete_top]
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> RW_TAC bool_ss []
   >> FULL_SIMP_TAC bool_ss [function_def, carrier_def]
   >> Q.UNDISCH_TAC `complete (s,r)`
   >> SIMP_TAC bool_ss [complete_def]
   >> DISCH_THEN (MP_TAC o CONJUNCT2 o Q.SPEC `\x : 'a. r ((f x) : 'a) x`)
   >> DISCH_THEN (Q.X_CHOOSE_THEN `k` ASSUME_TAC)
   >> Q.EXISTS_TAC `k`
   >> Know `s k /\ s (f k)` >- PROVE_TAC [glb_def]
   >> STRIP_TAC
   >> ASM_SIMP_TAC bool_ss [lfp_def]
   >> MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   >> REPEAT STRIP_TAC
   >- (Q.PAT_X_ASSUM `glb X Y Z` MP_TAC >> ASM_SIMP_TAC bool_ss [glb_def])
   >> MATCH_MP_TAC poset_antisym
   >> Q.EXISTS_TAC `s`
   >> Q.EXISTS_TAC `r`
   >> ASM_SIMP_TAC bool_ss []
   >> MATCH_MP_TAC (PROVE [] ``x /\ (x ==> y) ==> x /\ y``)
   >> CONJ_TAC
   >| [Q.PAT_X_ASSUM `glb X Y Z` MP_TAC
       >> ASM_SIMP_TAC bool_ss [glb_def]
       >> DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)
       >> RW_TAC bool_ss []
       >> MATCH_MP_TAC poset_trans
       >> Q.EXISTS_TAC `s`
       >> METIS_TAC [monotonic_def],
       STRIP_TAC
       >> Q.PAT_X_ASSUM `glb X Y Z` MP_TAC
       >> ASM_SIMP_TAC bool_ss [glb_def]
       >> DISCH_THEN MATCH_MP_TAC
       >> Know `s (f (f k))` >- PROVE_TAC []
       >> RW_TAC bool_ss []
       >> Q.PAT_X_ASSUM `monotonic X Y`
          (MATCH_MP_TAC o REWRITE_RULE [monotonic_def])
       >> PROVE_TAC []]
QED

Theorem knaster_tarski_gfp:
     !p f.
       poset p /\ complete p /\ function (carrier p) (carrier p) f /\
       monotonic p f ==> ?x. gfp p f x
Proof
   RW_TAC bool_ss []
   >> Know `?x. bottom p x` >- PROVE_TAC [complete_bottom]
   >> Know `?s r. p = (s,r)` >- pair_cases_tac
   >> RW_TAC bool_ss []
   >> FULL_SIMP_TAC bool_ss [function_def, carrier_def]
   >> Q.UNDISCH_TAC `complete (s,r)`
   >> SIMP_TAC bool_ss [complete_def]
   >> DISCH_THEN (MP_TAC o CONJUNCT1 o Q.SPEC `\x : 'a. r x ((f x) : 'a)`)
   >> DISCH_THEN (Q.X_CHOOSE_THEN `k` ASSUME_TAC)
   >> Q.EXISTS_TAC `k`
   >> Know `s k /\ s (f k)` >- PROVE_TAC [lub_def]
   >> STRIP_TAC
   >> ASM_SIMP_TAC bool_ss [gfp_def]
   >> MATCH_MP_TAC (PROVE [] ``(x ==> y) /\ x ==> x /\ y``)
   >> REPEAT STRIP_TAC
   >- (Q.PAT_X_ASSUM `lub X Y Z` MP_TAC >> ASM_SIMP_TAC bool_ss [lub_def])
   >> MATCH_MP_TAC poset_antisym
   >> Q.EXISTS_TAC `s`
   >> Q.EXISTS_TAC `r`
   >> ASM_SIMP_TAC bool_ss []
   >> MATCH_MP_TAC (PROVE [] ``y /\ (y ==> x) ==> x /\ y``)
   >> CONJ_TAC
   >| [Q.PAT_X_ASSUM `lub X Y Z` MP_TAC
       >> ASM_SIMP_TAC bool_ss [lub_def]
       >> DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)
       >> RW_TAC bool_ss []
       >> MATCH_MP_TAC poset_trans
       >> Q.EXISTS_TAC `s`
       >> METIS_TAC [monotonic_def],
       STRIP_TAC
       >> Q.PAT_X_ASSUM `lub X Y Z` MP_TAC
       >> ASM_SIMP_TAC bool_ss [lub_def]
       >> DISCH_THEN MATCH_MP_TAC
       >> Know `s (f (f k))` >- PROVE_TAC []
       >> RW_TAC bool_ss []
       >> Q.PAT_X_ASSUM `monotonic X Y`
          (MATCH_MP_TAC o REWRITE_RULE [monotonic_def])
       >> PROVE_TAC []]
QED

Theorem knaster_tarski:
     !p f.
       poset p /\ complete p /\ function (carrier p) (carrier p) f /\
       monotonic p f ==> (?x. lfp p f x) /\ (?x. gfp p f x)
Proof
   PROVE_TAC [knaster_tarski_lfp, knaster_tarski_gfp]
QED
