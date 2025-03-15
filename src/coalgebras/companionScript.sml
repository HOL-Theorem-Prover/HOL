(*
  This development is based on Damien Pous' "Coinduction All the Way Up,
  including the derivation of parameterized coinduction
*)
open HolKernel Parse boolLib bossLib;
open pred_setTheory fixedPointTheory;
open posetTheory;

val _ = new_theory "companion";

Theorem glb_unique:
  poset (s,r) /\
  glb (s,r) P x /\ glb (s,r) P y
  ==> x = y
Proof
  rw[glb_def] >>
  drule_then irule poset_antisym >> simp[]
QED

Theorem lub_unique:
  poset (s,r) /\
  lub (s,r) P x /\ lub (s,r) P y
  ==> x = y
Proof
  rw[lub_def] >>
  drule_then irule poset_antisym >> simp[]
QED

Theorem lub_is_gfp:
  poset (s,r) /\ function s s f /\ monotonic (s,r) f /\
  lub (s,r) { x | r x (f x) } l
  ==> gfp (s,r) f l
Proof
  rw[lub_def, gfp_def, monotonic_def, function_def] >>
  subgoal ‘r l (f l)’ >-
   (first_x_assum irule >> rw[] >>
    drule_then irule poset_trans >>
    first_assum $ irule_at Any >> rw[]) >>
  drule_then irule poset_antisym >> rw[]
QED

(* core *)

Definition lift_rel:
  lift_rel (s,r) f g = !x. s x ==> r (f x) (g x)
End

(* f (b x) steps to f x *)
Definition compatible_def:
  compatible (s,r) b f = (function s s f /\ monotonic (s,r) f /\
                          lift_rel (s,r) (f o b) (b o f))
End

Theorem compatible_self:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b
  ==> compatible (s,r) b b
Proof
  rw[poset_def, compatible_def, function_def, lift_rel]
QED

Theorem compatible_id:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b
  ==> compatible (s,r) b I
Proof
  rw[compatible_def, monotonic_def, poset_def, function_def, lift_rel]
QED

(* this technique is 'complete' for valid deductions *)
Theorem compatible_const_gfp:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  gfp (s,r) b fp
  ==> compatible (s,r) b (K fp)
Proof
  rw[compatible_def, gfp_def, poset_def, monotonic_def,
     function_def, lift_rel]
QED

(* λX. BIGUNION {f X | f | compatible b f} *)
Definition companion_def:
  companion (s,r) b t = (function s s t /\
     !x. lub (s,r) { f x | f | compatible (s,r) b f } (t x))
End

Theorem compatible_below_companion:
  poset (s,r) /\
  compatible (s,r) b f /\ companion (s,r) b t
  ==> lift_rel (s,r) f t
Proof
  rw[companion_def, lift_rel] >>
  ‘function s s f’ by fs[compatible_def] >>
  gvs[lub_def, PULL_EXISTS, function_def]
QED

(* f x <= f y <= t y is upper bound, compatible f must be mono *)
Theorem companion_mono:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t ==> monotonic (s,r) t
Proof
  rw[companion_def, lub_def, PULL_EXISTS] >>
  drule_all_then strip_assume_tac compatible_self >>
  rw[monotonic_def] >>
  first_assum $ qspec_then ‘x’ strip_assume_tac >>
  pop_assum match_mp_tac >> rw[] >>
  (* establish fx < ty *)
  last_x_assum $ qspec_then ‘y’ strip_assume_tac >> pop_assum kall_tac >>
  drule_then irule poset_trans >>
  rw[function_def] >>
  metis_tac[compatible_def, monotonic_def, function_def]
QED

Theorem compatible_companion:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t ==> compatible (s,r) b t
Proof
  rw[compatible_def]
  >- (fs[companion_def])
  >- (metis_tac[companion_mono]) >>
  rw[lift_rel] >>
  gvs[companion_def, lub_def, PULL_EXISTS] >>
  first_assum $ qspec_then ‘b x’ strip_assume_tac >>
  pop_assum irule >>
  rw[function_in] >>
  fs[compatible_def] >>
  drule_then irule poset_trans >>
  rw[function_in] >>
  gvs[function_def, monotonic_def, lift_rel] >>
  metis_tac[]
QED

Theorem compatible_compose:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  compatible (s,r) b f /\ compatible (s,r) b g
  ==> compatible (s,r) b (f o g)
Proof
  rw[compatible_def, lift_rel] >-
   (fs[function_def]) >-
   (fs[function_in, monotonic_def]) >>
  ‘r (f (g (b x))) (f (b (g x)))’ by metis_tac[monotonic_def, function_in] >>
  drule_then irule poset_trans >> rw[function_in] >>
  metis_tac[function_in]
QED

Theorem companion_expansive:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t /\
  s x ==> r x (t x)
Proof
  strip_tac >>
  ‘lift_rel (s,r) I t’ suffices_by rw[lift_rel] >>
  ho_match_mp_tac compatible_below_companion >>
  rw[function_def, compatible_companion] >>
  rw[GSYM combinTheory.I_EQ_IDABS, compatible_id]
QED

Theorem companion_idem:
  poset (s,r) /\ function s s b /\ monotonic (s,r) b /\
  companion (s,r) b t /\
  s x ==> t (t x) = t x
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then irule poset_antisym >>
  rw[function_in] >-
   (‘lift_rel (s,r) (t o t) t’ suffices_by rw[lift_rel] >>
    ho_match_mp_tac compatible_below_companion >>
    rw[function_def, GSYM combinTheory.o_DEF] >>
    irule compatible_compose >>
    rw[compatible_companion]) >-
   (metis_tac[companion_def, function_def, companion_expansive])
QED

Theorem companion_bot_gfp:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  bottom (s,r) bot /\ gfp (s,r) b gfix /\
  companion (s,r) b t
  ==> t bot = gfix
Proof
  rw[] >>
  drule_then irule poset_antisym >> rw[]
  >- (fs[companion_def, function_in, bottom_def])
  >- (fs[gfp_def])
  (* t0 <= tb0 <= bt0 *)
  >- (match_mp_tac gfp_coinduct >>
      ‘function s s t’ by fs[companion_def] >>
      fs[function_in, bottom_def] >>
      drule_then match_mp_tac poset_trans >>
      qexists_tac ‘t (b bot)’ >>
      rw[bottom_def, function_in]
      >- (irule (iffLR monotonic_def) >> metis_tac[companion_mono, function_def]) >>
      ‘compatible (s,r) b t’ suffices_by fs[compatible_def, lift_rel] >>
      irule compatible_companion >> rw[])
  >- (drule_all compatible_const_gfp >> strip_tac >>
      fs[companion_def, lub_def] >>
      first_x_assum $ qspec_then ‘bot’ strip_assume_tac >>
      first_x_assum irule >>
      fs[gfp_def] >>
      qexists_tac ‘K gfix’ >> rw[function_def])
QED

(* any post fixpoint is below the greatest fixpoint *)
Theorem companion_coinduct:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t /\
  gfp (s,r) b gfix /\
  s x /\ r x ((b o t) x) ==> r x gfix
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘t x’ >> rw[function_in]
  >- (fs[gfp_def])
  >- (ho_match_mp_tac companion_expansive >> rw[]) >>
  match_mp_tac gfp_coinduct >>
  rw[function_in] >>
  drule_all compatible_companion >> strip_tac >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘t (b (t x))’ >>
  reverse (rw[function_in])
  >- (fs[compatible_def, lift_rel] >>
      metis_tac[companion_idem, function_def]) >>
  metis_tac[monotonic_def, companion_mono, function_in]
QED

(* bt is a sound enhancement *)
Theorem enhanced_gfp:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  gfp (s,r) b gfix /\
  companion (s,r) b t /\ gfp (s,r) (b o t) efix
  ==> efix = gfix
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then irule poset_antisym >> rw[]
  >- (fs[gfp_def])
  >- (fs[gfp_def])
  >- (drule_then match_mp_tac companion_coinduct >>
      qexistsl_tac [‘t’,‘b’] >>
      fs[gfp_def, poset_def]) >>
  irule gfp_coinduct >>
  qexistsl_tac [‘(b o t)’, ‘s’] >>
  fs[gfp_def] >>
  metis_tac[monotonic_def, function_def, companion_expansive]
QED

(*
 * parameterized formalization following the cawu paper with 2nd order lattice
 *)

Theorem param_coind_init:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  bottom (s,r) bot /\ gfp (s,r) b gfix /\
  companion (s,r) b t
  ==> r x (t bot) ==> r x gfix
Proof
  metis_tac[companion_bot_gfp]
QED

Theorem param_coind_done:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t
  ==> s x /\ s y /\ r y x ==> r y (t x)
Proof
  rw[] >>
  ‘function s s t’ by fs[companion_def] >>
  drule_then match_mp_tac poset_trans >>
  qexists_tac ‘x’ >> rw[function_in] >>
  metis_tac[companion_expansive]
QED

Theorem param_coind_upto_f:
  poset (s,r) /\ monotonic (s,r) b /\ function s s b /\
  companion (s,r) b t
  ==> function s s f /\ (!x. r (f x) (t x))
  ==> s x /\ s y /\ r y (f (t x))
  ==> r y (t x)
Proof
  rw[] >>
  drule_then match_mp_tac poset_trans >>
  first_x_assum $ irule_at Any >>
  ‘function s s t’ by fs[companion_def] >>
  simp[function_in] >>
  metis_tac[companion_idem]
QED

Definition endo_def:
  endo (s,r) f = (monotonic (s,r) f /\ !x. if s x then s (f x) else f x = @y. ~(s y))
End

Definition endo_lift_def:
  endo_lift (s,r) = (endo (s,r) , lift_rel (s,r))
End

Theorem endo_in:
  endo (s,r) t /\ s x ==> s (t x)
Proof
  rw[endo_def] >> metis_tac[]
QED

(* this is one reason why we need choose instead of ARB (which can be in s) *)
Theorem endo_comp:
  endo (s,r) f /\ endo (s,r) g ==> endo (s,r) (f o g)
Proof
  rw[endo_def] >-
   (metis_tac[monotonic_comp, function_def]) >>
  rw[] >> metis_tac[]
QED

Theorem endo_poset:
  poset (s,r) ==> poset (endo_lift (s,r))
Proof
  rw[poset_def, endo_lift_def, lift_rel, endo_def]
  >- (qexists_tac ‘λx. if s x then x else @y. ~s y’ >> rw[monotonic_def])
  >- (metis_tac[])
  >- (rw[FUN_EQ_THM] >> metis_tac[])
  >- (metis_tac[])
QED

Definition B_join_def:
  B_join (s,r) b B =
  (function (endo (s,r)) (endo (s,r)) B /\ monotonic (endo_lift (s,r)) B /\
   !g x. lub (s,r) { f x | f | endo (s,r) f /\ lift_rel (s,r) (f o b) (b o g) }
             (B g x))
End

Theorem compatible_B_functional_postfix:
  poset (s,r) /\ endo (s,r) b /\
  B_join (s,r) b B /\
  endo (s,r) f ==>
  (lift_rel (s,r) f (B f) <=> lift_rel (s,r) (f o b) (b o f))
Proof
  reverse (rw[B_join_def, EQ_IMP_THM]) >-
   (fs[lub_def, lift_rel] >> metis_tac[endo_in]) >>
  (* look pointwise since the predicate is pointwise *)
  subgoal ‘lift_rel (s,r) (B f o b) (b o f)’ >-
   (fs[lub_def] >> rw[lift_rel] >>
    first_x_assum $ qspecl_then [‘f’, ‘b x’] strip_assume_tac >>
    first_x_assum irule >> rw[SF SFY_ss, endo_in] >>
    fs[lift_rel]) >>
  fs[lift_rel] >> rw[endo_in] >>
  drule_then irule poset_trans >> rw[SF SFY_ss, endo_in] >>
  fs[endo_lift_def] >>
  metis_tac[endo_in, monotonic_def, function_def]
QED

Theorem endo_function:
  endo (s,r) f ==> function s s f
Proof
  metis_tac[endo_def, function_def]
QED

Theorem B_greatest_fixpoint_is_companion:
  poset (s,r) /\ endo (s,r) b /\
  endo (s,r) t /\ companion (s,r) b t /\
  B_join (s,r) b B
  ==> gfp (endo_lift (s,r)) B t
Proof
  rw[EQ_IMP_THM] >>
  drule endo_poset >> rw[] >>
  fs[endo_lift_def] >>
  qabbrev_tac ‘t' = (λx. if s x then t x else @y. ~s y)’ >>
  subgoal ‘lub (endo (s,r),lift_rel (s,r)) {f | lift_rel (s,r) f (B f)} t'’ >-
   (‘endo (s,r) t'’
      by fs[Abbr ‘t'’, endo_def, monotonic_def, companion_def, function_def] >>
    ‘compatible (s,r) b t’ by
      metis_tac[compatible_companion, function_def, endo_def] >>
     fs[companion_def, lub_def] >> rw[] >-
     (rw[lift_rel] >>
      last_x_assum $ qspec_then ‘x’ strip_assume_tac >>
      fs[Abbr ‘t'’] >>
      first_x_assum irule >> rw[SF SFY_ss, endo_in] >>
      qexists_tac ‘y’ >> rw[compatible_def] >-
       (metis_tac[endo_in, function_def]) >-
       (fs[endo_def]) >>
      metis_tac[compatible_B_functional_postfix]) >>
    pop_assum irule >> rw[] >>
    ‘lift_rel (s,r) (t' o b) (b o t')’
      suffices_by metis_tac[compatible_B_functional_postfix] >>
    fs[compatible_def, lift_rel, Abbr ‘t'’] >>
    rw[] >>
    metis_tac[endo_in]) >>
  subgoal ‘lift_rel (s,r) (t' o b) (b o t')’ >-
   (drule_then irule (iffLR compatible_B_functional_postfix) >>
    fs[lub_def] >>
    qexists_tac ‘B’ >> rw[] >>
    first_x_assum irule >>
    reverse conj_tac >- (fs[B_join_def, function_def, endo_lift_def]) >>
    rw[] >>
    fs[B_join_def, endo_lift_def] >>
    ‘lift_rel (s,r) y t'’ by metis_tac[] >>
    drule_then irule poset_trans >>
    fs[function_def] >>
    qexists_tac ‘B y’ >> rw[] >>
    ‘monotonic (endo (s,r),lift_rel (s,r)) B’ by fs[endo_def] >>
    fs[monotonic_def]) >>
  subgoal ‘compatible (s,r) b t’ >-
   (drule_then irule compatible_companion >>
    fs[endo_def, function_def] >> metis_tac[]) >>
  drule_all compatible_B_functional_postfix >> rw[] >>
  (* argument: gfp B = lub of postfix points = lub of compat functions *)
  irule lub_is_gfp >> rw[] >-
   (metis_tac[endo_def, function_def, B_join_def, endo_lift_def]) >-
   (fs[B_join_def, endo_lift_def, endo_def]) >>
  ‘t = t'’ suffices_by metis_tac[] >>
  drule_then irule poset_antisym >>
  fs[B_join_def, companion_def, lub_def] >>
  rw[] >-
   (last_x_assum $ drule_then irule >> fs[compatible_def]) >>
  rw[lift_rel] >>
  last_x_assum $ qspec_then ‘x’ strip_assume_tac >>
  first_x_assum irule >>
  rw[SF SFY_ss, endo_in] >>
  qexists_tac ‘t'’ >>
  fs[compatible_def, SF SFY_ss, endo_function, endo_def]
QED

Theorem t_below_Tf:
  poset (s,r) /\ endo (s,r) b /\
  endo (s,r) t /\ companion (s,r) b t /\
  B_join (s,r) b B /\
  bottom (endo_lift (s,r)) bot /\
  companion (endo_lift (s,r)) B T' /\
  endo (s,r) f
  ==> lift_rel (s,r) t (T' f)
Proof
  rw[] >>
  drule endo_poset >>
  drule_all B_greatest_fixpoint_is_companion >> rw[] >>
  fs[endo_lift_def] >>
  subgoal ‘T' bot = t’ >-
   (irule companion_bot_gfp >>
    qexistsl_tac [‘B’, ‘lift_rel (s,r)’, ‘endo (s,r)’] >>
    fs[SRULE [endo_lift_def] endo_poset, B_join_def, endo_lift_def]) >>
  subgoal ‘monotonic (endo (s,r),lift_rel (s,r)) T'’ >-
   (irule companion_mono >> fs[function_def] >>
    qexists_tac ‘B’ >> fs[B_join_def, endo_lift_def, function_def]) >>
  fs[monotonic_def] >>
  metis_tac[bottom_def]
QED

Theorem lift_rel_comp:
  poset (s,r) /\
  function s s g /\ function s s f /\ function s s f' /\ function s s g' /\
  monotonic (s,r) f /\ monotonic (s,r) f' /\
  lift_rel (s,r) f f' /\ lift_rel (s,r) g g'
  ==> lift_rel (s,r) (f o g) (f' o g')
Proof
  rw[lift_rel, function_def] >>
  drule_then irule poset_trans >> rw[] >>
  metis_tac[monotonic_def, poset_trans]
QED

Theorem Bf_compatible_f:
  poset (s,r) /\ endo (s,r) b /\ endo (s,r) f /\
  B_join (s,r) b B
  ==> lift_rel (s,r) (B f o b) (b o f)
Proof
  rw[B_join_def, endo_lift_def, lift_rel, lub_def] >>
  first_x_assum $ qspecl_then [‘f’, ‘b x’] strip_assume_tac >>
  pop_assum irule >> pop_assum kall_tac >> rw[] >>
  metis_tac[endo_in]
QED

Theorem doubling_compatible_B:
  poset (s,r) /\ endo (s,r) b /\
  B_join (s,r) b B
  ==> compatible (endo_lift (s,r)) B (λf. f o f)
Proof
  rw[compatible_def, endo_lift_def] >-
   (rw[function_def, endo_def] >-
     (irule monotonic_comp >> metis_tac[function_def]) >- (metis_tac[])) >-
   (fs[monotonic_def, B_join_def, endo_lift_def] >> rw[] >>
    metis_tac[lift_rel_comp, endo_def, function_def]) >>
  rw[lift_rel] >>
  rename1 ‘r (B f (B f y)) _’ >>
  drule_all Bf_compatible_f >> rw[] >>
  fs[lift_rel, B_join_def, endo_lift_def, lub_def] >> rw[] >>
  first_x_assum $ qspecl_then [‘f o f’, ‘y’] strip_assume_tac >>
  first_x_assum irule >> pop_assum kall_tac >> rw[] >-
   (metis_tac[function_def, endo_def]) >>
  qexists_tac ‘B f o B f’ >> rw[] >-
   (metis_tac[function_def, endo_comp]) >>
  drule_then irule poset_trans >> rw[] >-
   (metis_tac[endo_in, function_in]) >- (metis_tac[endo_in]) >>
  qexists_tac ‘B f (b (f x))’ >> rw[] >- (metis_tac[endo_in, function_in]) >-
   (‘monotonic (s,r) (B f)’ by metis_tac[function_def, endo_def] >>
    fs[monotonic_def] >> metis_tac[endo_def, function_def]) >>
  metis_tac[endo_def, function_def]
QED

Theorem Tf_idem:
  poset (s,r) /\ endo (s,r) b /\
  B_join (s,r) b B /\
  endo (s,r) t /\ companion (s,r) b t /\
  companion (endo_lift (s,r)) B T' /\
  bottom (endo_lift (s,r)) bot /\
  endo (s,r) f
  ==> T' f o T' f = T' f
Proof
  rw[endo_lift_def] >>
  drule endo_poset >> rw[] >>
  irule poset_antisym >>
  qexistsl_tac [‘lift_rel (s,r)’, ‘endo (s,r)’] >> rw[] >-
   (metis_tac[companion_def, function_def, endo_comp, endo_def]) >-
   (metis_tac[companion_def, function_def, endo_comp, endo_def]) >-
   (fs[endo_lift_def])
  >- (irule poset_trans >>
      qexistsl_tac [‘endo (s,r)’, ‘T' (T' f)’] >>
      fs[B_join_def, endo_lift_def, function_def] >>
      rw[] >-
       (metis_tac[endo_comp, companion_def, function_def]) >-
       (metis_tac[companion_def, function_def]) >-
       (metis_tac[companion_def, function_def]) >-
       (‘lift_rel (endo (s,r),lift_rel (s,r)) ((λf. f o f) o T') (T' o T')’
          suffices_by fs[lift_rel] >>
        irule lift_rel_comp >> fs[] >>
        ‘function (endo (s,r)) (endo (s,r)) T'’ by metis_tac[companion_def] >>
        rw[] >-
         (rw[monotonic_def] >>
          irule lift_rel_comp >> metis_tac[endo_def, function_def]) >-
         (irule companion_mono >> metis_tac[function_def]) >-
         (rw[function_def, endo_comp]) >-
         (irule compatible_below_companion >> rw[] >>
          qexists_tac ‘B’ >> rw[GSYM endo_lift_def] >>
          irule doubling_compatible_B >>
          rw[B_join_def, endo_lift_def] >> metis_tac[function_def]) >-
         (rw[lift_rel] >> metis_tac[poset_refl, endo_in, function_def])) >-
       (‘T' (T' f) = T' f’
          suffices_by metis_tac[poset_refl, companion_def, function_def] >>
        irule companion_idem >>
        qexistsl_tac [‘B’, ‘lift_rel (s,r)’, ‘endo (s,r)’] >>
        metis_tac[function_def, endo_def])) >>
  (* Tf o id <= Tf o t <= Tf o Tf *)
  ‘lift_rel (s,r) (T' f o I) (T' f o T' f)’ suffices_by rw[] >>
  irule lift_rel_comp >>
  ‘function s s (T' f)’ by metis_tac[function_def, companion_def, endo_def] >>
  ‘monotonic (s,r) (T' f)’ by metis_tac[function_def, companion_def, endo_def] >>
  rw[] >-
   (fs[function_def]) >-
   (rw[lift_rel] >> metis_tac[poset_refl, companion_def, function_def, endo_def]) >-
   (drule_all (SRULE [endo_lift_def] t_below_Tf) >>
    rw[lift_rel] >>
    drule_then irule poset_trans >> rw[] >-
     (metis_tac[companion_def, function_def, endo_def]) >>
    qexists_tac ‘t x’ >> rw[SF SFY_ss, endo_in] >>
    drule_then irule companion_expansive >>
    metis_tac[function_def, endo_def])
QED

(* only needs finite lubs aside from t, B and T, completeness is just convenient *)
(*    maybe somehow B_join and the higher companion forces the boundedness? *)
(*  *)
Theorem param_coind:
  complete (s,r) /\ complete (endo_lift (s,r)) /\
  poset (s,r) /\ endo (s,r) b /\
  companion (s,r) b t /\ endo (s,r) t /\
  B_join (s,r) b B /\ companion (endo_lift (s,r)) B T' /\
  gfp (s,r) b gfix /\
  s x /\ s y /\
  lub (s,r) { x; y } xy
  ==> r y (b (t xy)) ==> r y (t x)
Proof
  rw[] >>
  ‘monotonic (s,r) t’ by metis_tac[companion_mono, lub_def, endo_def] >>
  ‘monotonic (s,r) b’ by metis_tac[function_def, endo_def] >>
  ‘?bot. lub (s,r) {} bot’ by metis_tac[complete_def] >>
  reverse (subgoal ‘lift_rel (s,r)
                    (λz. if s z then (if r x z then y else bot) else @y. ~s y)
                    t’) >-
   (fs[lift_rel] >>
    pop_assum $ qspec_then ‘x’ strip_assume_tac >>
    Cases_on ‘r x x’ >> metis_tac[poset_refl]) >>
  qmatch_goalsub_abbrev_tac ‘lift_rel _ f _’ >>
  subgoal ‘endo (s,r) f’ >-
   (rw[endo_def, Abbr ‘f’] >-
     (rw[monotonic_def] >>
      Cases_on ‘r x z’ >-
       (metis_tac[poset_refl, poset_trans]) >>
      fs[lub_def] >> metis_tac[]) >>
    Cases_on ‘r x z’ >> fs[lub_def] >> metis_tac[]) >>
  drule_all B_greatest_fixpoint_is_companion >>
  rw[endo_lift_def] >>
  irule companion_coinduct >>
  qexistsl_tac [‘B’, ‘endo (s,r)’, ‘T'’] >> rw[] >-
   (* begin indent *)
   (metis_tac[endo_poset, endo_lift_def]) >-
   (‘?fxl. lub (s,r) { f x ; x } fxl’ by metis_tac[complete_def] >>
    subgoal ‘xy = fxl’ >-
     (drule_then irule lub_unique >>
      ‘y = f x’ by metis_tac[Abbr ‘f’, poset_refl] >> fs[] >>
      ‘{x; f x} = {f x; x}’ by rw[SET_EQ_SUBSET, SUBSET_DEF] >>
      fs[] >> metis_tac[]) >>
    drule_then strip_assume_tac (iffLR B_join_def) >>
    fs[endo_lift_def] >>
    rw[lift_rel] >>
    last_x_assum $ qspecl_then [‘T' f’, ‘x'’] strip_assume_tac >>
    pop_assum mp_tac >>
    rw[lub_def] >>
    first_x_assum irule >> pop_assum kall_tac >>
    conj_tac >- (fs[Abbr ‘f’] >> Cases_on ‘r x x'’ >> fs[lub_def]) >>
    qexists_tac ‘f’ >> rw[] >> ntac 2 (pop_assum kall_tac) >>
    rw[lift_rel] >>
    reverse (Cases_on ‘r x (b x')’) >-
     (reverse (rw[Abbr ‘f’, endo_in]) >- (metis_tac[endo_in]) >>
      fs[lub_def] >>
      ‘s (T' (λz. if s z then if r x z then y else bot else @y. ~s y) x')’
        suffices_by metis_tac[endo_in] >>
      fs[companion_def] >>
      metis_tac[function_def, endo_in]) >>
    subgoal ‘f (b x') = y’ >- (fs[Abbr ‘f’] >> metis_tac[endo_in]) >>
    rfs[] >> pop_assum kall_tac >>
    drule_then irule poset_trans >>
    ‘s (b (T' f x'))’ by metis_tac[endo_in, companion_def, function_def] >>
    rw[] >>
    qexists_tac ‘b (t fxl)’ >> rw[endo_in] >- (metis_tac[lub_def, endo_in]) >>
    drule_then irule poset_trans >> rw[] >- (metis_tac[lub_def, endo_in]) >>
    ‘?fbxl. lub (s,r) { f (b x') ; b x' } fbxl’ by metis_tac[complete_def] >>
    qexists_tac ‘b (t fbxl)’ >> rw[] >-
     (* split *)
     (metis_tac[endo_in, lub_def]) >-
     (‘r (t fxl) (t fbxl)’ suffices_by metis_tac[monotonic_def, lub_def,
                                                 endo_def, endo_in] >>
      ‘r fxl fbxl’ suffices_by metis_tac[companion_mono, monotonic_def, lub_def,
                                         function_def, endo_def] >>
      fs[lub_def] >>
      last_x_assum irule >> rw[] >-
       (‘r (b x') fbxl’ by metis_tac[endo_in] >>
        drule_then irule poset_trans >>
        pop_assum $ irule_at Any >>
        metis_tac[endo_in]) >-
       (‘y = f x’ by metis_tac[Abbr ‘f’, poset_refl] >> fs[] >>
        ‘r (f (b x')) fbxl’ by metis_tac[endo_in] >>
        ‘monotonic (s,r) f’ by fs[endo_def] >>
        metis_tac[monotonic_def, poset_trans, endo_in])) >>
    subgoal ‘?fbl. !X. lub (s,r) { f (b X) ; b X } (fbl X)’ >-
     (rw[GSYM SKOLEM_THM] >> metis_tac[complete_def]) >>
    ‘fbxl = fbl x'’ by metis_tac[lub_unique] >> fs[] >>
    ‘r (t (fbl x')) (T' f x')’ suffices_by metis_tac[monotonic_def, lub_def,
                                                     endo_def, endo_in] >>
    ‘lift_rel (s,r) (t o fbl) (T' f)’ suffices_by
      metis_tac[combinTheory.o_DEF, lift_rel] >>
    subgoal ‘bottom (endo_lift (s,r)) (λx. if s x then bot else @y. ~s y)’ >-
     (rw[bottom_def, endo_lift_def] >-
       (rw[endo_def, monotonic_def] >-
          (metis_tac[poset_refl, lub_def]) >-
          (metis_tac[lub_def])) >-
        (rw[lift_rel, lub_def] >>
         fs[lub_def] >> metis_tac[endo_def])) >>
    subgoal ‘T' f o T' f = T' f’ >-
     (drule_then irule Tf_idem >> rw[] >- (metis_tac[]) >>
      qexistsl_tac [‘B’, ‘b’, ‘t’] >> rw[endo_lift_def]) >>
    ‘lift_rel (s,r) (t o fbl) (T' f o T' f)’ suffices_by metis_tac[] >>
    subgoal ‘lift_rel (s,r) t (T' f)’ >-
     (drule_then irule t_below_Tf >> rw[] >- (metis_tac[]) >>
      qexistsl_tac [‘B’, ‘b’] >> rw[endo_lift_def]) >>
    irule lift_rel_comp >> rw[] >-
     (metis_tac[endo_def, companion_def, function_def]) >-
     (metis_tac[endo_def, function_def]) >-
     (metis_tac[endo_def, companion_def, function_def]) >-
     (metis_tac[function_def, lub_def]) >-
     (metis_tac[endo_def, companion_def, function_def]) >-
     (‘!X. s (fbl X) /\ (!y. s y /\ (y = f (b X) \/ y = b X) ==> r y (fbl X)) /\
           !z. s z /\ (!y. s y /\ (y = f (b X) \/ y = b X) ==> r y z) ==>
               r (fbl X) z’ by fs[lub_def] >>
      rw[lift_rel] >>
      ‘r (t x'') (T' f x'')’ by fs[lift_rel] >>
      first_x_assum $ qspec_then ‘x''’ strip_assume_tac >>
      first_x_assum irule >> pop_assum kall_tac >>
      rw[] >-
       (metis_tac[companion_def, function_def, endo_def]) >-
       (‘lift_rel (s,r) (f o b) (T' f o T' f)’
          suffices_by metis_tac[lift_rel, combinTheory.o_DEF] >>
        irule lift_rel_comp >> rw[SF SFY_ss, endo_function] >-
         (fs[endo_def]) >-
         (metis_tac[companion_def, function_def, endo_def]) >-
         (metis_tac[companion_def, function_def, endo_def]) >-
         (metis_tac[companion_def, function_def, endo_def]) >-
         (irule companion_expansive >>
          qexistsl_tac [‘B’, ‘endo (s,r)’] >> rw[] >>
          metis_tac[endo_poset, endo_lift_def]) >-
         (rw[lift_rel] >>
          drule_then irule poset_trans >>
          rw[SF SFY_ss, endo_in, endo_function] >-
           (metis_tac[companion_def, function_def, endo_def]) >>
          rename1 ‘_ /\ r (b a) _ /\ _’ >>
          qexists_tac ‘t a’ >> rw[SF SFY_ss, endo_in] >-
           (‘lift_rel (s,r) b t’ suffices_by rw[lift_rel] >>
            drule_then irule compatible_below_companion >>
            metis_tac[compatible_self, function_def, endo_def, lift_rel]) >>
          rfs[lift_rel])) >-
       (drule_then irule poset_trans >> rw[] >-
         (metis_tac[companion_def, function_def, endo_def]) >>
        qexists_tac ‘t x''’ >> rw[] >- (metis_tac[companion_def, function_def]) >>
        metis_tac[compatible_below_companion, compatible_self,
                  function_def, endo_def, lift_rel]))) >-
   (fs[B_join_def, endo_def, endo_lift_def]) >-
   (fs[endo_lift_def]) >-
   (fs[B_join_def, endo_lift_def])
QED

(* set helpers *)

Definition set_compatible_def:
  set_compatible b f = (monotone f /\ !X. f (b X) SUBSET b (f X))
End

Theorem set_compatible:
  set_compatible b f ==> compatible (UNIV,$SUBSET) b f
Proof
  rw[set_compatible_def, compatible_def, lift_rel, function_def]
QED

Theorem set_compatible_self:
  monotone b ==> set_compatible b b
Proof
  rw[set_compatible_def, monotone_def]
QED

Theorem set_compatible_id:
  monotone b ==> set_compatible b I
Proof
  rw[set_compatible_def, monotone_def]
QED

Theorem set_compatible_compose:
  monotone b ==>
  set_compatible b f /\ set_compatible b g
  ==> set_compatible b (f o g)
Proof
  rw[monotone_def, set_compatible_def] >>
  metis_tac[SUBSET_DEF]
QED

Definition set_companion_def:
  set_companion b X = BIGUNION { f X | f | set_compatible b f }
End

Theorem set_companion:
  companion (UNIV,$SUBSET) b (set_companion b)
Proof
  rw[companion_def, set_companion_def, function_def] >>
  rw[lub_def, compatible_def, set_compatible_def, lift_rel, function_def] >>
  fs[SUBSET_DEF, BIGUNION, IN_DEF] >>
  metis_tac[]
QED

Theorem set_companion_compatible:
  monotone b ==> set_compatible b (set_companion b)
Proof
  rw[] >>
  subgoal ‘compatible (UNIV,$SUBSET) b (set_companion b)’ >-
   (irule compatible_companion >>
    rw[set_companion, function_def]) >>
  fs[compatible_def, lift_rel, set_compatible_def]
QED

Theorem set_companion_coinduct:
  monotone b /\
  X SUBSET (b o set_companion b) X
  ==> X SUBSET gfp b
Proof
  rw[] >>
  irule companion_coinduct >>
  qexistsl_tac [‘b’, ‘UNIV’, ‘set_companion b’] >>
  rw[function_def, gfp_poset_gfp, set_companion]
QED

Theorem set_compatible_enhance:
  monotone b /\ set_compatible b f /\
  Y SUBSET f X
  ==> Y SUBSET set_companion b X
Proof
  rw[] >>
  drule_then irule SUBSET_TRANS >>
  irule (SRULE [lift_rel] compatible_below_companion) >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[set_compatible, set_companion]
QED

Theorem set_gfp_sub_companion:
  monotone b ==> gfp b SUBSET set_companion b x
Proof
  rw[] >>
  irule set_compatible_enhance >> rw[] >>
  qexists_tac ‘K (gfp b)’ >> rw[] >>
  rw[set_compatible_def, monotone_def, gfp_greatest_fixedpoint]
QED

(* to prove X is in a coinductive set from b, consider t0 *)
Theorem set_param_coind_init:
  monotone b /\
  X SUBSET set_companion b {}
  ==> X SUBSET gfp b
Proof
  rw[] >>
  drule_at_then Any irule param_coind_init >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[bottom_def, set_companion, function_def, gfp_poset_gfp]
QED

(* pull f out of tX *)
Theorem set_param_coind_upto_f:
  monotone b /\
  (!X. f X SUBSET set_companion b X) /\
  Y SUBSET f (set_companion b X)
  ==> Y SUBSET set_companion b X
Proof
  rw[] >>
  drule_at_then Any irule param_coind_upto_f >> rw[] >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[set_companion, function_def]
QED

(* conclude: X is a safe deduction from Y *)
Theorem set_param_coind_done:
  monotone b /\
  Y SUBSET X ==> Y SUBSET set_companion b X
Proof
  rw[] >>
  irule param_coind_done >> rw[] >>
  qexistsl_tac [‘b’, ‘UNIV’] >>
  rw[set_companion, function_def]
QED

Definition set_B_def:
  set_B b = λg X. BIGUNION { f X | f | monotone f /\ !Y. f (b Y) SUBSET b (g Y) }
End

Definition higher_monotone:
  higher_monotone fn = !f g. monotone f /\ monotone g /\
                             (!X. f X SUBSET g X) ==> (!X. (fn f) X SUBSET (fn g) X)
End

Definition higher_compat_def:
  higher_compat fn b =
  ((!f. monotone f ==> monotone (fn f)) /\ higher_monotone fn /\
   !f X. monotone f ==> (fn (set_B b f)) X SUBSET (set_B b (fn f)) X)
End

Definition set_T_def:
  set_T b = λf X. BIGUNION { (fn f) X | fn | monotone (fn f) /\ higher_compat fn b }
End

Theorem set_higher_complete:
  complete (endo_lift (univ(:'a -> bool),$SUBSET))
Proof
  rw[complete_def, endo_lift_def] >-
   (qexists_tac ‘λX. BIGUNION { f X | f | monotone f /\ c f }’ >>
    rw[lub_def] >-
     (rw[endo_def, monotone_def] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      qexists_tac ‘f X'’ >> rw[] >> metis_tac[SUBSET_DEF]) >-
     (fs[endo_def, lift_rel, BIGUNION, Once SUBSET_DEF] >> metis_tac[]) >>
    fs[lift_rel, endo_def] >> rw[] >>
    irule (iffRL BIGUNION_SUBSET) >> rw[] >> metis_tac[]) >>
  (qexists_tac ‘λX. BIGINTER { f X | f | monotone f /\ c f }’ >>
   rw[glb_def] >-
    (rw[endo_def, monotone_def] >>
     rw[SUBSET_BIGINTER] >>
     rw[BIGINTER, Once SUBSET_DEF] >>
     metis_tac[SUBSET_DEF]) >-
    (fs[endo_def, lift_rel, BIGINTER, Once SUBSET_DEF] >> metis_tac[]) >>
   fs[lift_rel, endo_def] >> rw[] >>
   irule (iffRL SUBSET_BIGINTER) >> rw[] >> metis_tac[])
QED

(* do a deduction step, Y must step to itself or reach X
 * proof: functionals on sets form a complete lattice under pointwise inclusion
 * B is monotone with that ordering, and it can be defined via lub = BIGUNION
 * hence B has a greatest fixpoint and we can instantiate *)
Theorem set_param_coind:
  monotone b
  ==> Y SUBSET b (set_companion b (X UNION Y))
  ==> Y SUBSET set_companion b X
Proof
  rw[] >>
  drule_at_then Any irule param_coind >>
  qexistsl_tac [‘set_B b’, ‘set_T b’, ‘gfp b’, ‘UNIV’] >>
  rw[endo_def, set_companion, gfp_poset_gfp, set_higher_complete] >-
   (metis_tac[set_companion_compatible, set_compatible_def]) >-
   (rw[B_join_def, set_B_def, endo_lift_def, endo_def, function_def] >-
     (rw[monotone_def, lift_rel] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      qexists_tac ‘f X''’ >> rw[] >>
      metis_tac[SUBSET_DEF, SUBSET_TRANS]) >-
     (rw[monotonic_def, lift_rel] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      qexists_tac ‘f X'’ >> rw[] >>
      metis_tac[SUBSET_TRANS, monotone_def]) >-
     (rw[lub_def, lift_rel] >-
       (rw[BIGUNION, Once SUBSET_DEF] >> metis_tac[]) >>
      rw[BIGUNION_SUBSET])) >-
   (rw[companion_def, endo_lift_def, set_B_def, set_T_def] >-
     (rw[function_def, endo_def, monotone_def] >>
      rw[BIGUNION_SUBSET] >>
      rw[BIGUNION, Once SUBSET_DEF] >>
      metis_tac[SUBSET_DEF]) >>
    rw[lub_def, endo_def, lift_rel]
    >- (rw[monotone_def, BIGUNION_SUBSET] >>
        rw[BIGUNION, Once SUBSET_DEF] >>
        metis_tac[SUBSET_DEF])
    >- (rw[BIGUNION, Once SUBSET_DEF] >>
        pop_assum $ irule_at Any >>
        qexists_tac ‘f'’ >> rw[] >>
        rw[higher_compat_def, higher_monotone] >-
         (fs[compatible_def, function_def, endo_def, monotonic_def, lift_rel]) >>
        fs[GSYM set_B_def] >>
        fs[compatible_def, lift_rel, endo_def, monotonic_def])
    >- (rw[BIGUNION_SUBSET] >>
        first_x_assum irule >> rw[] >>
        qexists_tac ‘fn’ >> rw[compatible_def] >-
         (rw[function_def, endo_def] >>
          fs[higher_compat_def, higher_monotone]) >-
         (fs[higher_compat_def, higher_monotone] >>
          rw[monotonic_def, lift_rel, endo_def]) >-
         (rw[GSYM set_B_def] >>
          rw[lift_rel] >>
          fs[higher_compat_def, endo_def]))) >-
   (rw[lub_def] >> rw[SUBSET_UNION])
QED

val _ = export_theory();
