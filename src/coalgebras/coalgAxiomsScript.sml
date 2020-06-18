open HolKernel Parse boolLib bossLib;

open relationTheory pairTheory pred_setTheory combinTheory
open mp_then

(* Abstract development of existence of final co-algebras, using new_type,
   new_constant and axioms to emulate a locale. If this can be carried out
   generically, the concrete approach for any given instance should be clear.
 *)


(* Mostly based on Rutten (TCS, 2000):
      "Universal coalgebra: a theory of systems",
   but with use of relators and choice of axioms from
   Blanchette et al (ITP, 2014):
      "Truly Modular (Co)datatypes for Isabelle/HOL"
 *)

val _ = new_theory "coalgAxioms";

val _ = hide "S"

Definition restr_def:
  restr f s = \x. if x IN s then f x else ARB
End

Theorem restr_applies:
  x IN A ==> (restr f A x = f x)
Proof
  simp[restr_def]
QED

Theorem IN_UNCURRY[simp]:
  (a,b) IN UNCURRY R <=> R a b
Proof
  simp[IN_DEF]
QED
Definition Delta_def[simp]:
  Delta V a b <=>  a = b /\ a IN V
End
Overload "Δ" = “Delta”                                                 (* UOK *)
Definition Gr_def[simp]:
  Gr h A a b <=> a IN A /\ b = h a
End

Theorem Gr_Id[simp]:
  Gr (\x. x) A = Delta A /\
  Gr (restr (\x. x) A) A = Delta A
Proof
  csimp[FUN_EQ_THM, restr_applies] >> metis_tac[]
QED

Definition span_def[simp]:
  span A f g b d <=> ?a. a IN A /\ b = f a /\ d = g a
End

Definition kernel_def[simp]:
  kernel A f x y <=> x IN A /\ y IN A /\ f x = f y
End

Theorem kernel_graph:
  kernel A f = inv (Gr f A) O Gr f A
Proof
  simp[FUN_EQ_THM, O_DEF]
QED


Definition RIMAGE_def:
  RIMAGE f A R x y <=>
  ?x0 y0. x = f x0 /\ y = f y0 /\ R x0 y0 /\ x0 IN A /\ y0 IN A
End

Definition RINV_IMAGE_def:
  RINV_IMAGE f A R x y <=> x IN A /\ y IN A /\ R (f x) (f y)
End

Theorem RIMAGE_Gr:
  RIMAGE f A R = Gr f A O R O inv (Gr f A)
Proof
  dsimp[FUN_EQ_THM, O_DEF, IN_DEF, PULL_EXISTS, RIMAGE_def] >>
  metis_tac[]
QED

Theorem Delta_IMAGE:
  Delta (IMAGE f A) = RIMAGE f A (Delta A)
Proof
  simp[FUN_EQ_THM, PULL_EXISTS, RIMAGE_def] >> metis_tac[]
QED

Theorem RINV_IMAGE_Gr:
  RINV_IMAGE f A R = inv (Gr f A) O R O Gr f A
Proof
  dsimp[FUN_EQ_THM, O_DEF, RINV_IMAGE_def] >> metis_tac[]
QED

val IRULE = goal_assum o resolve_then.resolve_then resolve_then.Any mp_tac

val _ = new_type("F", 1)
val _ = new_constant("mapF", “:('a -> 'b) -> 'a F -> 'b F”)
val _ = new_constant("setF", “:'a F -> 'a set”)

val mapID = new_axiom("mapID", “mapF (\x. x) = (\a. a)”)
val mapO = new_axiom ("mapO", “mapF f o mapF g = mapF (f o g)”)
Theorem mapO' = SIMP_RULE (srw_ss()) [FUN_EQ_THM] mapO
val set_map = new_axiom ("set_map", “setF o mapF f = IMAGE f o setF ”)
Theorem set_map' = SIMP_RULE (srw_ss()) [Once FUN_EQ_THM, EXTENSION] set_map
val map_CONG = new_axiom (
  "map_CONG",
  “!f g y. (!x. x IN setF y ==> f x = g x) ==> mapF f y = mapF g y”)

val _ = add_rule{block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 fixity = Suffix 2100, paren_style = OnlyIfNecessary,
                 pp_elements = [TOK "ᴾ"], term_name = "UNCURRY"}       (* UOK *)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 fixity = Suffix 2100, paren_style = OnlyIfNecessary,
                 pp_elements = [TOK "⟨",TM,TOK"⟩"], term_name = "restr"}(* UOK*)

Definition relF_def:
  relF R x y <=> ?z. setF z SUBSET UNCURRY R /\ mapF FST z = x /\ mapF SND z = y
End

val relO = new_axiom ("relO", “relF R O relF S RSUBSET relF (R O S)”)

Theorem relO_EQ :
  relF R O relF S = relF (R O S)
Proof
  irule RSUBSET_ANTISYM >> simp[relO] >>
  simp[relF_def, FUN_EQ_THM, RSUBSET, O_DEF, SUBSET_DEF, FORALL_PROD] >>
  rw[PULL_EXISTS] >>
  fs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  map_every qexists_tac [‘mapF (\ (a,b). (a, f a b)) z’,
                         ‘mapF (\ (a,b). (f a b, b)) z’] >>
  simp[mapO', o_UNCURRY_R, o_ABS_R, set_map', EXISTS_PROD, PULL_EXISTS] >>
  conj_tac >> irule map_CONG >> simp[FORALL_PROD]
QED

Theorem relEQ:
  relF (=) = (=)
Proof
  simp[FUN_EQ_THM, relF_def, EQ_IMP_THM, FORALL_AND_THM,
       SUBSET_DEF, FORALL_PROD] >> conj_tac
  >- (simp[PULL_EXISTS] >> rpt strip_tac >> irule map_CONG>>
      simp[FORALL_PROD]) >>
  qx_gen_tac ‘a’ >> qexists_tac ‘mapF (\a. (a,a)) a’ >>
  simp[mapO', o_ABS_R, mapID, set_map']
QED

Theorem relF_inv[simp]:
  relF (inv R) x y = relF R y x
Proof
  simp[relF_def, SUBSET_DEF, FORALL_PROD, EQ_IMP_THM, PULL_EXISTS] >> rw[] >>
  qexists_tac ‘mapF (\ (a,b). (b,a)) z’>>
  simp[mapO', o_UNCURRY_R, o_ABS_R, set_map', EXISTS_PROD] >> rw[] >>
  irule map_CONG >> simp[FORALL_PROD]
QED

Theorem rel_monotone:
  (!a b. R a b ==> S a b) ==> (!A B. relF R A B ==> relF S A B)
Proof
  simp[relF_def, EXISTS_PROD, SUBSET_DEF, PULL_EXISTS, FORALL_PROD] >>
  metis_tac[]
QED

Type system[pp] = “:('a -> bool) # ('a -> 'a F)”

(* same as an "all" test *)
Definition Fset_def:
  Fset (A : 'a set) = { af | setF af SUBSET A }
End

Theorem map_preserves_INJ:
  INJ f A B ==> INJ (mapF f) (Fset A) (Fset B)
Proof
  strip_tac >> drule_then assume_tac LINV_DEF >>
  fs[INJ_IFF] >> simp[Fset_def, set_map', PULL_EXISTS, SUBSET_DEF] >>
  simp[EQ_IMP_THM] >> rw[] >>
  rename [‘mapF f x = mapF f y’] >>
  ‘mapF (LINV f A) (mapF f x) = mapF (LINV f A) (mapF f y)’ by simp[] >>
  fs[mapO'] >>
  ‘mapF (LINV f A o f) x = mapF (\x. x) x /\
   mapF (LINV f A o f) y = mapF (\x. x) y’
    by (conj_tac >> irule map_CONG >> simp[]) >>
  fs[mapID]
QED

Theorem map_preserves_funs:
  (!a. a IN A ==> f a IN B) ==> (!af. af IN Fset A ==> mapF f af IN Fset B)
Proof
  simp[Fset_def, SUBSET_DEF, set_map', PULL_EXISTS]
QED

Definition system_def:
  system ((A,af) : 'a system) <=>
  (!a. a IN A ==> af a IN Fset A) /\ !a. a NOTIN A ==> af a = ARB
End

Theorem system_members:
  system (A,af) ==> !a b. a IN A /\ b IN setF (af a) ==> b IN A
Proof
  metis_tac[system_def |> SIMP_RULE (srw_ss()) [Fset_def, SUBSET_DEF]]
QED

Definition hom_def:
  hom h (A,af) (B,bf) <=>
  system (A,af) /\ system (B,bf) /\
  (!a. a IN A ==> h a IN B /\ bf (h a) = mapF h (af a)) /\
  (!a. a NOTIN A ==> h a = ARB)
End

Theorem homs_compose:
  hom f As Bs /\ hom g Bs Cs ==> hom (restr (g o f) (FST As)) As Cs
Proof
  map_every PairCases_on [‘As’, ‘Bs’, ‘Cs’] >>
  simp[hom_def, restr_def, mapO'] >> rw[] >>
  irule map_CONG >> rpt (dxrule_then strip_assume_tac system_members) >>
  simp[] >> metis_tac[]
QED

Theorem hom_ID:
  system (A, af) ==>
  hom (restr (\x. x) A) (A,af) (A,af)
Proof
  csimp[hom_def, restr_def, system_def, Fset_def, SUBSET_DEF] >> rw[]
  >- metis_tac[] >>
  ‘!x. x IN setF (af a) ==> (\x. if x IN A then x else ARB) x = (\x.x) x’
    by metis_tac[] >>
  drule map_CONG >> simp[mapID]
QED

Definition bisim_def:
  bisim R (A,af) (B,bf) <=>
  system (A,af) /\ system (B,bf) /\
  !a b. R a b ==> a IN A /\ b IN B /\ relF R (af a) (bf b)
End

Theorem bisim_system:
  bisim R As Bs ==> system As /\ system Bs
Proof
  map_every Cases_on [‘As’, ‘Bs’] >> simp[bisim_def]
QED

Definition bisimilar_def:
  bisimilar As Bs <=> ?R. bisim R As Bs
End

Inductive genS:
  (!a0. a0 IN FST As ==> genS As a0 a0) /\
  (!a0 a1 a. genS As a0 a1 /\ a IN setF (SND As a1) ==> genS As a0 a)
End

Definition genU_def:
  genU ((A,af):'a system) : ('a # 'a) system =
    (BIGUNION $ IMAGE (\a. IMAGE ((,) a) (genS (A,af) a)) A,
     (\ (a0,a). if a0 IN A /\ genS (A,af) a0 a then mapF ((,) a0) (af a)
                else ARB))
End

Theorem genS_system:
  genS (A,af) a0 a ==> system (A,af) ==> a IN A
Proof
  Induct_on ‘genS’ >> rw[] >> fs[] >> metis_tac[system_members]
QED

Theorem IN_genS[simp]:
  x IN genS A x0 <=> genS A x0 x
Proof
  simp[IN_DEF]
QED

Theorem genU_system:
  system (A,af) ==> system (genU (A, af))
Proof
  strip_tac >>
  simp[system_def, genU_def, Fset_def, SUBSET_DEF, FORALL_PROD,
       PULL_EXISTS] >> rw[]
  >- (rename [‘a0 IN A’, ‘genS (A,af) a0 a’, ‘(a1,a2) IN setF _’] >>
      fs[set_map'] >> metis_tac[genS_rules, SND])
  >- fs[set_map']
QED


Theorem sbisimulation_projns_homo:
  bisim R (A,af) (B,bf) <=>
  ?Rf.
    hom (restr FST (UNCURRY R)) (UNCURRY R, Rf) (A, af) /\
    hom (restr SND (UNCURRY R)) (UNCURRY R, Rf) (B, bf)
Proof
  rw[bisim_def, hom_def, EQ_IMP_THM, restr_applies, FORALL_PROD] >> simp[]
  >- (fs[relF_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM, PULL_EXISTS,
         SUBSET_DEF] >>
      rename [‘_ IN setF (RF _ _) ==> _ IN UNCURRY R’] >>
      qexists_tac ‘restr (UNCURRY RF) (UNCURRY R)’ >> csimp[restr_def] >> rw[]
      >- metis_tac[]
      >- (first_x_assum $ drule_then (strip_assume_tac o GSYM) >>
          simp[] >> irule map_CONG >> simp[])
      >- (simp[system_def, SUBSET_DEF, Fset_def, FORALL_PROD] >>
          fs[FORALL_PROD] >> metis_tac[])
      >- metis_tac[] >>
      first_x_assum $ drule_then (strip_assume_tac o GSYM) >>
      simp[] >> irule map_CONG >> simp[])
  >- metis_tac[]
  >- metis_tac[] >>
  simp[relF_def, SUBSET_DEF, FORALL_PROD] >>
  qexists_tac ‘Rf (a, b)’ >> rpt (first_x_assum drule) >> simp[] >> rw[] >>
  fs[system_def, SUBSET_DEF, Fset_def, FORALL_PROD]
  >- metis_tac[]
  >- (irule map_CONG>> simp[restr_def,FORALL_PROD] >> metis_tac[])
  >- (irule map_CONG>> simp[restr_def,FORALL_PROD] >> metis_tac[])
QED

Theorem lemma2_4_1:
  hom (h o g) (A,af) (C,cf) /\ hom g (A,af) (B,bf) /\ SURJ g A B /\
  (!b. b NOTIN B ==> h b = ARB) ==>
  hom h (B,bf) (C,cf)
Proof
  simp[hom_def] >> strip_tac >> qx_gen_tac ‘b’ >> strip_tac >>
  ‘?a. a IN A /\ g a = b’ by metis_tac[SURJ_DEF] >>
  rw[mapO']
QED

Theorem lemma2_4_2:
  hom (h o g) (A,af) (C,cf) /\ hom h (B,bf) (C,cf) /\
  (!a. a IN A ==> g a IN B) /\ (!a. a NOTIN A ==> g a = ARB) /\
  INJ h B C ==>
  hom g (A,af) (B,bf)
Proof
  simp[hom_def] >> strip_tac >> qx_gen_tac ‘a’ >> strip_tac >>
  fs[GSYM mapO'] >>
  last_assum (first_assum o mp_then (Pos hd) mp_tac) >>
  ‘bf (g a) IN Fset B /\ mapF g (af a) IN Fset B’
    suffices_by metis_tac[INJ_IFF, map_preserves_INJ] >>
  simp[Fset_def, SUBSET_DEF, set_map', PULL_EXISTS] >> metis_tac[system_members]
QED

Theorem thm2_5:
  hom h (A,af) (B,bf) <=>
  (!a. a IN A ==> h a IN B) /\ (!a. a NOTIN A ==> h a = ARB) /\
  bisim (Gr h A) (A,af) (B,bf)
Proof
  simp[hom_def, bisim_def] >>
  map_every Cases_on [‘system (A,af)’, ‘system(B,bf)’] >> simp[] >>
  Cases_on ‘!a. a NOTIN A ==> h a = ARB’ >> simp[] >>
  reverse (Cases_on ‘!a. a IN A ==> h a IN B’ >> simp[])
  >- metis_tac[] >>
  simp[relF_def, SUBSET_DEF, FORALL_PROD] >> eq_tac
  >- (rw[] >> qexists_tac ‘mapF (\a. (a, h a)) (af a)’ >>
      simp[mapO', o_ABS_R, mapID, set_map'] >> rw[]
      >- metis_tac[system_members] >>
      irule map_CONG >> simp[]) >>
  rw[] >> first_x_assum (drule_then (strip_assume_tac o GSYM))  >>
  simp[mapO'] >> irule map_CONG >> simp[FORALL_PROD]
QED


Theorem prop5_1:
  system (A,af) ==> bisim (Delta A) (A,af) (A,af)
Proof
  strip_tac >> drule hom_ID >> simp[thm2_5, restr_applies]
QED

Theorem thm5_2[simp]:
  bisim (inv R) Bs As <=> bisim R As Bs
Proof
  map_every PairCases_on [‘As’, ‘Bs’] >> simp[bisim_def] >> metis_tac[]
QED

Theorem lemma5_3:
  hom f (A,af) (B,bf) /\ hom g (A,af) (C,cf) ==>
  bisim (span A f g) (B,bf) (C,cf)
Proof
  csimp[hom_def, bisim_def, PULL_EXISTS] >>
  rw[relF_def, SUBSET_DEF, FORALL_PROD] >>
  rename [‘a IN A’, ‘mapF FST _ = mapF f (af a)’] >>
  qexists_tac ‘mapF (\a. (f a, g a)) (af a)’>>
  simp[mapO', set_map', PULL_EXISTS, o_ABS_R] >>
  simp_tac (bool_ss ++ boolSimps.ETA_ss) [] >>
  metis_tac[system_members]
QED

(* Rutten, Thm 5.4 *)
Theorem bisimulations_compose:
  bisim R (A,af) (B,bf) /\ bisim Q (B,bf) (C,cf) ==>
  bisim (Q O R) (A,af) (C,cf)
Proof
  rw[bisim_def] >> fs[O_DEF, GSYM relO_EQ] >> metis_tac[]
QED

Theorem thm5_4 = bisimulations_compose

Theorem thm5_5:
  (!R. R IN Rs ==> bisim R As Bs) /\
  system (As:'a system) /\ system (Bs:'b system) ==>
  bisim (\a b. ?R. R IN Rs /\ R a b) As Bs
Proof
  tmCases_on “As : 'a system” ["A af"] >>
  tmCases_on “Bs : 'b system” ["B bf"] >>
  rw[bisim_def] >- metis_tac[] >- metis_tac[] >>
  ntac 2 (first_x_assum $ drule_then strip_assume_tac) >>
  irule rel_monotone >> simp[] >> metis_tac[]
QED

Theorem bisim_RUNION:
  bisim R1 As Bs /\ bisim R2 As Bs ==> bisim (R1 RUNION R2) As Bs
Proof
  strip_tac >>
  ‘R1 RUNION R2 = (\a b. ?R. R IN {R1;R2} /\ R a b)’
    by dsimp[Ntimes FUN_EQ_THM 2, RUNION] >>
  pop_assum SUBST1_TAC >> irule thm5_5 >> simp[DISJ_IMP_THM] >>
  drule bisim_system >> simp[]
QED

Theorem prop5_7:
  hom f (A,af) (B,bf) ==>
  bisim (kernel A f) (A,af) (A,af) /\ kernel A f equiv_on A
Proof
  rpt strip_tac
  >- (simp[kernel_graph]>> irule bisimulations_compose >>
      simp[] >> metis_tac[thm2_5]) >>
  simp[equiv_on_def] >> metis_tac[]
QED


Theorem prop5_9_1:
  hom f (A,af) (B,bf) /\ bisim R (A,af) (A,af) ==>
  bisim (RIMAGE f A R) (B,bf) (B,bf)
Proof
  simp[RIMAGE_Gr] >> strip_tac >> IRULE bisimulations_compose >>
  IRULE bisimulations_compose >>
  simp[] >> goal_assum drule >> fs[thm2_5]
QED

Theorem prop5_9_2:
  hom f (A,af) (B,bf) /\ bisim Q (B,bf) (B,bf) ==>
  bisim (RINV_IMAGE f A Q) (A,af) (A,af)
Proof
  simp[RINV_IMAGE_Gr] >> strip_tac >> IRULE bisimulations_compose >>
  IRULE bisimulations_compose >> simp[] >> first_assum IRULE >>
  fs[thm2_5]
QED

Definition subsystem_def:
  subsystem V (A,af) <=>
  system (A,af) /\ V SUBSET A /\ ?vf. hom (restr (\x.x) V) (V,vf) (A,af)
End

Theorem prop6_1:
  V SUBSET A /\ hom (restr (\x.x) V) (V,kf) (A,af) /\
  hom (restr (\x.x) V) (V,lf) (A,af) ==>
  kf = lf
Proof
  simp[hom_def, restr_def] >> rw[] >> simp[FUN_EQ_THM] >> qx_gen_tac ‘v’ >>
  reverse (Cases_on ‘v IN V’) >- fs[system_def] >>
  ‘(!a. a IN V ==>
        mapF (\x. if x IN V then x else ARB) (kf a) = mapF (\x. x) (kf a)) /\
   !a. a IN V ==>
       mapF (\x. if x IN V then x else ARB) (lf a) = mapF (\x. x) (lf a)’
    by (rw[] >> irule map_CONG >> simp[] >> metis_tac[system_members]) >>
  fs[mapID]
QED

Theorem prop6_2:
  system (A,af) ==>
  (subsystem V (A,af) <=> V SUBSET A /\ bisim (Delta V) (A,af) (A,af))
Proof
  simp[subsystem_def] >> strip_tac >> eq_tac
  >- (csimp[PULL_EXISTS] >> rpt strip_tac >>
      ‘hom (restr (\x.x) V) (V,restr af V) (A,af)’
        by (fs[hom_def, restr_def] >> fs[system_def, Fset_def, SUBSET_DEF] >>
            rw[] >- (fs[set_map'] >> metis_tac[]) >>
            simp[mapO', o_ABS_R] >> irule map_CONG >> simp[] >> rw[]>> fs[]) >>
      ‘vf = restr af V’ by metis_tac[prop6_1] >>
      qpat_x_assum ‘hom _ _ _ ’ mp_tac >>
      csimp[bisim_def, thm2_5, restr_def]) >>
  csimp[bisim_def, SUBSET_DEF] >> strip_tac >>
  qexists_tac ‘restr af V’ >>
  simp[hom_def, restr_applies] >>
  conj_asm1_tac
  >- (fs[system_def, Fset_def, relF_def, SUBSET_DEF, FORALL_PROD, restr_def] >>
      rw[] >>
      first_x_assum $ drule_then strip_assume_tac >>
      rename [‘mapF FST z = af a’]>>
      ‘setF (mapF FST z) = setF (af a)’ by simp[] >>
      pop_assum mp_tac >> REWRITE_TAC [EXTENSION, set_map'] >>
      simp[EXISTS_PROD]) >>
  reverse conj_tac >- simp[restr_def] >>
  qx_gen_tac ‘a’ >> strip_tac >>
  ‘mapF (restr (\x. x) V) (af a) = mapF (\x. x) (af a)’
    suffices_by simp[mapID] >>
  irule map_CONG >> drule system_members >> csimp[restr_def] >> metis_tac[]
QED

Theorem bisimilar_equivalence:
  bisimilar equiv_on system
Proof
  simp[equiv_on_def, FORALL_PROD, IN_DEF] >> rw[]
  >- (simp[bisimilar_def, bisim_def] >> rename [‘system (A,af)’] >>
      qexists_tac ‘Delta A’ >> simp[relF_def, SUBSET_DEF, FORALL_PROD] >>
      qx_gen_tac ‘a’ >> strip_tac >> qexists_tac ‘mapF (\x. (x,x)) (af a)’ >>
      simp[set_map', mapO', o_ABS_R, mapID] >>
      metis_tac[system_members])
  >- (rpt (pop_assum mp_tac) >>
      ‘!A af B bf.
         system ((A,af):'a system) /\ system((B,bf):'a system) /\
         bisimilar (A,af) (B,bf) ==>
         bisimilar (B,bf) (A,af)’ suffices_by metis_tac[] >>
      simp[bisimilar_def, PULL_EXISTS] >> rw[] >>
      rename [‘bisim R _ _’] >> qexists_tac ‘inv R’ >> simp[]) >>
  fs[bisimilar_def] >>
  rename [‘bisim R1 (A,af) (B,bf)’, ‘bisim R2 (B,bf) (C,cf)’,
          ‘bisim _ (A,af) (C,cf)’] >>
  fs[bisim_def] >> qexists_tac ‘R2 O R1’ >>
  simp[O_DEF, PULL_EXISTS, GSYM relO_EQ] >> metis_tac[]
QED

Definition gbisim_def:
  gbisim (A,af) x y <=> ?R. bisim R (A,af) (A,af) /\ R x y
End

Theorem gbisim_equivalence:
  system (A,af) ==> gbisim (A,af) equiv_on A
Proof
  simp[equiv_on_def, gbisim_def] >> rw[]
  >- (qexists_tac ‘Delta A’ >> simp[prop5_1])
  >- metis_tac[inv_DEF, thm5_2] >>
  rename [‘bisim R1 _ _ ’, ‘R1 a b’, ‘bisim R2 _ _’, ‘R2 b c’] >>
  qexists_tac ‘R2 O R1’ >> simp[O_DEF] >> metis_tac[thm5_4]
QED

Theorem bisim_gbisim:
  system (A,af) ==> bisim (gbisim (A,af)) (A,af) (A,af)
Proof
  simp[bisim_def,gbisim_def, PULL_EXISTS] >> rw[] >>
  first_assum drule >> simp_tac (srw_ss()) [relF_def] >>
  simp[relF_def, SUBSET_DEF, FORALL_PROD, PULL_EXISTS, gbisim_def] >> rw[] >>
  rename [‘mapF FST z = _’, ‘mapF SND z = _’, ‘_ IN setF z ==> R _ _’] >>
  qexists_tac ‘z’ >>
  rw[] >> qexists_tac ‘R’>> simp[bisim_def] >> metis_tac[]
QED

Definition simple_def:
  simple (A : 'a system) <=>
  !R. bisim R A A ==> !x y. R x y ==> x = y
End

Theorem simple_imp4:
  simple (As:'a system) ==>
  !Bs:'b system f g. hom f Bs As /\ hom g Bs As ==> f = g
Proof
  tmCases_on “As:'a system” ["A af"] >> rw[simple_def] >>
  tmCases_on “Bs:'b system” ["B bf"] >>
  ‘bisim (span B f g) (A,af) (A,af)’
    suffices_by (strip_tac >> first_x_assum drule >>
                 simp[PULL_EXISTS, FUN_EQ_THM] >> fs[hom_def] >>
                 metis_tac[]) >>
  irule lemma5_3 >> metis_tac[]
QED

Theorem simple_eq3:
  simple As <=> ∀R. bisim R As As /\ R equiv_on (FST As) ⇒ R = Delta (FST As)
Proof
  tmCases_on “As : 'a system” ["A af"] >>
  simp[simple_def] >> eq_tac >> rw[]
  >- (simp[FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] >>
      metis_tac[equiv_on_def, bisim_def]) >>
  ‘system (A,af)’ by metis_tac[bisim_def] >>
  ‘bisim (gbisim (A,af)) (A,af) (A,af)’ by simp[bisim_gbisim] >>
  first_x_assum drule >> simp[gbisim_equivalence] >>
  simp[FUN_EQ_THM, gbisim_def] >> metis_tac[]
QED




val _ = export_theory();
