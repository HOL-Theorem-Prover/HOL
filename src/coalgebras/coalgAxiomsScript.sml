open HolKernel Parse boolLib bossLib;

open relationTheory pairTheory pred_setTheory combinTheory
open cardinalTheory simpleSetCatTheory

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

val _ = app (ignore o hide) ["S", "W"]

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

Theorem UNIV_system[simp]:
  system (UNIV,af)
Proof
  simp[system_def, Fset_def]
QED

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

Definition epi_def:
  epi f ((A,af):'a system) ((B,bf):'b system) (:'c) <=>
  hom f (A,af) (B,bf) /\
  !C cf g h. hom g (B,bf) ((C,cf):'c system) /\ hom h (B,bf) (C,cf) /\
             restr (g o f) A = restr (h o f) A ==> g = h
End

Definition iso_def:
  iso (A,af) (B,bf) <=>
     ?f g. hom f (A,af) (B,bf) /\ hom g (B,bf) (A,af) /\
           (!a. a IN A ==> g (f a) = a) /\
           (!b. b IN B ==> f (g b) = b)
End

Theorem iso_SYM:
  iso (A,af) (B,bf) <=> iso (B,bf) (A,af)
Proof
  simp[iso_def] >> metis_tac[]
QED

Theorem INJ_homs_mono:
  hom f (A,af) (B,bf) /\ INJ f A B ==>
  !C cf g h.
    hom g (C,cf) (A,af) /\ hom h (C,cf) (A,af) /\
    f o g = f o h ==> g = h
Proof
  simp[INJ_IFF, hom_def] >> rw[FUN_EQ_THM] >> metis_tac[]
QED

Theorem SURJ_homs_epi:
  hom f ((A,af):'a system) ((B,bf):'b system) /\ SURJ f A B ==>
  epi f (A,af) (B,bf) (:'c)
Proof
  simp[SURJ_DEF, hom_def, FUN_EQ_THM, epi_def] >> rw[] >>
  Cases_on ‘x IN B’ >> simp[] >>
  ‘?a. a IN A /\ f a = x’ by metis_tac[] >>
  fs[restr_def] >> metis_tac[]
QED

Definition Fpushout_def:
  Fpushout ((A,af):'a system) ((B,bf):'b system) ((C,cf):'c system) f g
           ((P,pf):'p system,i1,i2) (:'d)
  <=>
  hom f (A,af) (B,bf) /\ hom g (A,af) (C,cf) /\ hom i1 (B,bf) (P,pf) /\
  hom i2 (C,cf) (P,pf) /\ restr (i1 o f) A = restr (i2 o g) A  /\
  !Q qf j1 j2.
    hom j1 (B,bf) ((Q,qf):'d system) /\ hom j2 (C,cf) (Q,qf) /\
    restr (j1 o f) A = restr (j2 o g) A ==>
    ?!u. hom u (P,pf) (Q,qf) /\
         restr (u o i1) B = j1 /\
         restr (u o i2) C = j2
End

Theorem hom_implies_restr:
  hom f (A,af) Bs ==> restr f A = f
Proof
  Cases_on ‘Bs’ >> simp[hom_def, restr_def, FUN_EQ_THM] >> metis_tac[]
QED

Theorem epi_Fpushout:
  epi f (A,af) (B,bf) (:'c) <=>
  Fpushout (A,af) (B,bf) (B,bf) f f ((B,bf),restr (\x.x) B,restr (\x.x) B) (:'c)
Proof
  simp[epi_def, Fpushout_def] >> Cases_on ‘hom f (A,af) (B,bf)’ >>
  simp[] >> ‘system (A,af) /\ system (B,bf)’ by fs[hom_def] >> simp[hom_ID] >>
  simp_tac (srw_ss() ++ boolSimps.CONJ_ss ++ SatisfySimps.SATISFY_ss)
           [hom_implies_restr] >>
  simp[EXISTS_UNIQUE_THM] >> metis_tac[]
QED

Theorem hom_shom:
  hom f (A,af) (B,bf) ==> shom f A B
Proof
  simp[hom_def, shom_def]
QED


(*
Theorem Spushout_Fpushout_IMP:
  hom f (A,af) (B,bf) /\ hom g (A,af) (C,cf) /\
  Spushout A B C f g (P,i1,i2) (:'d) ==>
  ?pf. Fpushout (A,af) (B,bf) (C,cf) f g ((P,pf),i1,i2) (:'d)
Proof
  rpt strip_tac >>
  ‘Spushout A B C f g (SPO A B C f g) (:'d)’ by metis_tac[hom_shom,Spushout_quotient] >>
  fs[SPO_def] >> pop_assum mp_tac >>
  qmatch_abbrev_tac ‘Spushout _ _ _ _ _ (SPOq, SPOi1, SPOi2) _ ==> _’ >> strip_tac >>

  simp[Fpushout_def, Spushout_def] >> rpt strip_tac >>
  ‘shom f A B /\ shom g A C /\ shom i1 B P /\ shom i2 C P’
    by metis_tac[hom_shom] >> simp[] >>
  Cases_on ‘restr (i1 o f) A = restr (i2 o g) A’ >> simp[] >> reverse eq_tac
  >- (rw[] >>
      ‘shom j1 B Q /\ shom j2 C Q’ by metis_tac[hom_shom] >>
      first_x_assum drule_all >>
      CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [EXISTS_UNIQUE_THM])) >>
      rw[]
  reverse (Cases_on ‘hom f (A,af) (B,bf)’) >> simp[]
  >- (Cases_on ‘shom f A B’ >> simp[] >>
*)

Theorem BIJ_homs_iso:
  hom f (A,af) (B,bf) /\ BIJ f A B ==> iso (A,af) (B,bf)
Proof
  simp[hom_def, iso_def, BIJ_IFF_INV] >> rw[] >>
  qexistsl_tac [‘f’, ‘restr g B’] >> simp[restr_applies] >>
  reverse conj_tac >- simp[restr_def] >>
  qx_gen_tac ‘b’ >> strip_tac >>
  ‘bf b = bf (f (g b))’ by metis_tac[] >> pop_assum SUBST1_TAC >>
  simp[mapO'] >>
  ‘mapF (restr g B o f) (af (g b)) = mapF (\x. x) (af (g b))’
    suffices_by simp[mapID] >>
  irule map_CONG >> simp[restr_def] >> ‘g b IN A’ by simp[] >>
  metis_tac[system_members]
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


Definition bquot_def:
  bquot ((A,af):'a system) R : 'a set system =
     (partition R A,
      restr (\ap. mapF (eps R A) (af (CHOICE ap))) (partition R A))
End


Theorem bquot_correct:
  system (A,af) /\ bisim R (A,af) (A,af) /\ R equiv_on A ==>
  system (bquot (A,af) R) /\ hom (eps R A) (A,af) (bquot (A,af) R)
Proof
  csimp[hom_def, bquot_def, restr_applies] >> rw[eps_partition]
  >- (simp[system_def, Fset_def, SUBSET_DEF, restr_applies, set_map',
           PULL_EXISTS] >>reverse conj_tac
      >- simp[restr_def] >>
      qx_gen_tac ‘ap’ >> strip_tac >> qx_gen_tac ‘a’ >>
      DEEP_INTRO_TAC CHOICE_INTRO >> conj_tac
      >- metis_tac[EMPTY_NOT_IN_partition, MEMBER_NOT_EMPTY] >>
      qx_gen_tac ‘a0’ >> rpt strip_tac >> irule eps_partition >>
      metis_tac[system_members, partition_SUBSET, SUBSET_DEF])
  >- (DEEP_INTRO_TAC CHOICE_INTRO >> conj_tac
      >- metis_tac[eps_partition, EMPTY_NOT_IN_partition, MEMBER_NOT_EMPTY] >>
      qx_gen_tac ‘a'’ >> simp[eps_def] >> strip_tac >>
      fs[sbisimulation_projns_homo] >> rpt (qpat_x_assum ‘hom _ _ _ ’ mp_tac) >>
      simp[hom_def, FORALL_PROD, restr_applies] >> rw[] >>
      ‘af a = mapF (restr FST (UNCURRY R)) (Rf (a, a')) /\
       af a' = mapF (restr SND (UNCURRY R)) (Rf (a, a'))’ by simp[] >>
      simp[mapO'] >> irule map_CONG >> simp[FORALL_PROD] >>
      qx_genl_tac [‘a1’, ‘a2’] >> strip_tac >> ‘(a,a') IN UNCURRY R’ by simp[]>>
      ‘(a1,a2) IN UNCURRY R’ by metis_tac[system_members] >>
      pop_assum mp_tac >> simp[restr_applies, eps_def] >>
      strip_tac >> ‘a1 IN A /\ a2 IN A’ by metis_tac[] >>
      simp[EXTENSION] >> qx_gen_tac ‘aa’ >> Cases_on ‘aa IN A’ >> simp[] >>
      prove_tac[equiv_on_def]) >>
  simp[eps_def]
QED

Theorem prop5_8 = bquot_correct

Definition coequalizer_def:
  coequalizer ((A,af):'a system) ((B,bf):'b system) f1 f2 ((C,cf), g) (:'d) <=>
  hom f1 (A,af) (B,bf) /\ hom f2 (A,af) (B,bf) /\
  hom g (B,bf) ((C,cf):'c system) /\ restr (g o f1) A = restr (g o f2) A /\
  !h D df.
    hom h (B,bf) ((D,df):'d system) /\ restr (h o f1) A = restr (h o f2) A ==>
    ?!u. hom u (C,cf) (D,df) /\ h = restr (u o g) B
End

Theorem coequalizer_thm =
  coequalizer_def |> SPEC_ALL
                  |> Q.INST [‘C'’ |-> ‘FST (Cs : 'c system)’,
                             ‘cf’ |-> ‘SND (Cs : 'c system)’]
                  |> SIMP_RULE (srw_ss()) []

Theorem bquot_coequalizer:
  system (A,af) /\ bisim R (A,af) (A,af) /\ R equiv_on A ==>
  ?Rf.
    coequalizer (UNCURRY R, Rf)
                (A,af)
                (restr FST (UNCURRY R))
                (restr SND (UNCURRY R))
                (bquot (A,af) R, eps R A)
                (:'d)
Proof
  Cases_on ‘bquot (A,af) R’ >>
  simp[coequalizer_def, sbisimulation_projns_homo] >> rw[] >>
  first_assum IRULE >> rw[]
  >- metis_tac[bquot_correct,sbisimulation_projns_homo]
  >- (simp[Once FUN_EQ_THM, restr_def, FORALL_PROD] >>
      rw[EXTENSION] >> simp[eps_def] >> rw[]
      >- (fs[equiv_on_def] >> metis_tac[])
      >- (fs[hom_def, FORALL_PROD, restr_def] >> metis_tac[])
      >- (fs[hom_def, FORALL_PROD, restr_def] >> metis_tac[]))
  >- (fs[bquot_def] >> rw[] >>
      fs[FUN_EQ_THM, restr_def, FORALL_PROD, EXISTS_UNIQUE_THM] >>
      conj_tac
      >- (qexists_tac ‘restr (\p. h (CHOICE p)) (partition R A)’ >> conj_tac
          >- (simp[hom_def, restr_def, mapO', o_ABS_L] >> rw[]
              >- (simp[system_def] >> rw[] >>
                  irule map_preserves_funs >> qexists_tac ‘A’ >>
                  simp[eps_partition] >> DEEP_INTRO_TAC CHOICE_INTRO >> rw[]
                  >- (rename [‘A0 IN partition R A’] >>
                      ‘A0 <> {}’ suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
                      metis_tac[EMPTY_NOT_IN_partition]) >>
                  rename [‘a0 IN A0’, ‘A0 IN partition _ _’] >>
                  ‘a0 IN A’ suffices_by metis_tac[system_def] >>
                  metis_tac[partition_SUBSET, SUBSET_DEF])
              >- fs[hom_def]
              >- (‘CHOICE ap IN A’ suffices_by metis_tac[hom_def] >>
                  DEEP_INTRO_TAC CHOICE_INTRO >> rw[]
                  >- (rename [‘A0 IN partition R A’] >>
                      ‘A0 <> {}’ suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
                      metis_tac[EMPTY_NOT_IN_partition]) >>
                  rename [‘a0 IN A0’, ‘A0 IN partition _ _’] >>
                  ‘a0 IN A’ suffices_by metis_tac[system_def] >>
                  metis_tac[partition_SUBSET, SUBSET_DEF]) >>
              DEEP_INTRO_TAC CHOICE_INTRO >> rw[]
              >- (rename [‘A0 IN partition R A’] >>
                  ‘A0 <> {}’ suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
                  metis_tac[EMPTY_NOT_IN_partition]) >>
              rename [‘a0 IN A0’, ‘A0 IN partition R A’] >>
              ‘a0 IN A’ by metis_tac[SUBSET_DEF, partition_SUBSET] >>
              fs[hom_def] >> irule map_CONG >> qx_gen_tac ‘a1’ >> strip_tac >>
              ‘a1 IN A’ by metis_tac[system_members] >>
              simp[eps_partition] >> simp[eps_def] >>
              DEEP_INTRO_TAC CHOICE_INTRO >> conj_tac
              >- (simp[] >> metis_tac[equiv_on_def]) >>
              simp[] >> metis_tac[]) >>
          reverse (rw[]) >- fs[hom_def] >>
          simp[eps_partition, restr_def] >> simp[eps_def] >>
          DEEP_INTRO_TAC CHOICE_INTRO >> conj_tac
          >- (simp[] >> metis_tac[equiv_on_def]) >>
          simp[] >> metis_tac[]) >>
      qx_genl_tac [‘u1’, ‘u2’] >> strip_tac >> qx_gen_tac ‘ap’ >>
      CCONTR_TAC >> reverse (Cases_on ‘ap IN partition R A’)
      >- (qpat_x_assum ‘_ <> _’ mp_tac >> fs[hom_def]) >>
      ‘?a. a IN ap’
        by metis_tac[MEMBER_NOT_EMPTY, EMPTY_NOT_IN_partition] >>
      ‘a IN A’ by metis_tac[partition_SUBSET, SUBSET_DEF] >>
      ‘eps R A a = ap’
        by (simp[eps_def] >> simp[EXTENSION] >>
            fs[partition_def] >> rw[] >> fs[] >> fs[equiv_on_def] >>
            metis_tac[]) >>
      metis_tac[])
QED

Theorem prop5_9_1:
  hom (restr f A) (A,af) (B,bf) /\ bisim R (A,af) (A,af) ==>
  bisim (RIMAGE f A R) (B,bf) (B,bf)
Proof
  simp[RIMAGE_Gr] >> strip_tac >> IRULE bisimulations_compose >>
  IRULE bisimulations_compose >>
  simp[] >> goal_assum (drule_at (Pos (el 2))) >> fs[thm2_5]
QED

Theorem prop5_9_2:
  hom (restr f A) (A,af) (B,bf) /\ bisim Q (B,bf) (B,bf) ==>
  bisim (RINV_IMAGE f A Q) (A,af) (A,af)
Proof
  simp[RINV_IMAGE_Gr] >> strip_tac >> IRULE bisimulations_compose >>
  IRULE bisimulations_compose >> simp[] >> first_assum IRULE >>
  fs[thm2_5]
QED

(* Section 6: Subsystems *)

Definition subsystem_def:
  subsystem V (A,af) <=>
  system (A,af) /\ V SUBSET A /\ ?vf. hom (restr (\x.x) V) (V,vf) (A,af)
End

Theorem subsystem_refl[simp]:
  system (A,af) ==> subsystem A (A,af)
Proof
  simp[subsystem_def] >> strip_tac >> IRULE hom_ID >> simp[]
QED

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

Theorem subsystem_system:
  subsystem V (A,af) ==> system (V, restr af V)
Proof
  strip_tac >> ‘system (A,af)’ by fs[subsystem_def] >>
  fs[prop6_2, bisim_def] >>
  fs[system_def, SUBSET_DEF, Fset_def, restr_def] >>
  rpt strip_tac >> first_x_assum drule >>
  csimp[relF_def, PULL_EXISTS, SUBSET_DEF, FORALL_PROD] >> rw[] >>
  rename [‘mapF FST rr = af a’] >>
  ‘setF (mapF FST rr) = setF (af a)’ by simp[] >> pop_assum mp_tac >>
  simp[EXTENSION, set_map', EXISTS_PROD] >> rename [‘x IN setF (af a)’] >>
  disch_then (qspec_then ‘x’ mp_tac) >> simp[] >> metis_tac[]
QED

Theorem thm6_3_1:
  hom f (A,af) (B,bf) /\ subsystem V (A,af) ==>
  subsystem (IMAGE f V) (B, bf)
Proof
  strip_tac >>
  ‘system (A, af) /\ system (B,bf)’ by fs[hom_def] >>
  ‘system (V, restr af V)’ by metis_tac[subsystem_system] >>
  simp[prop6_2, Delta_IMAGE] >> conj_tac
  >- fs[hom_def, subsystem_def, SUBSET_DEF, PULL_EXISTS] >>
  irule prop5_9_1 >> qexists_tac ‘restr af V’ >> fs[prop6_2] >>
  conj_tac >- (fs[bisim_def] >> simp[restr_def]) >>
  fs[hom_def] >> simp[restr_def] >> fs[SUBSET_DEF] >>
  rpt strip_tac >> irule map_CONG >> simp[] >>
  metis_tac[system_members, restr_def]
QED

Theorem thm6_3_2:
  hom f (A,af) (B,bf) /\ subsystem W (B,bf) ==>
  subsystem (PREIMAGE f W INTER A) (A, af)
Proof
  strip_tac >>
  ‘system (A, af) /\ system (B, bf) /\ system (W,restr bf W)’
    by metis_tac[hom_def, subsystem_system] >>
  simp[prop6_2, Delta_INTER] >>
  csimp[bisim_def, RINTER, relF_def, SUBSET_DEF, FORALL_PROD] >>
  qx_gen_tac ‘a0’ >> strip_tac >>
  qexists_tac ‘mapF (\a. (a,a)) (af a0)’  >>
  simp[mapO', o_ABS_R, mapID, set_map'] >>
  qx_gen_tac ‘a'’ >> strip_tac >> reverse conj_tac
  >- metis_tac[system_members] >>
  fs[hom_def] >>
  ‘bf (f a0) = mapF f (af a0)’ by metis_tac[] >>
  ‘restr bf W (f a0) = mapF f (af a0)’ by simp[restr_def] >>
  pop_assum (mp_tac o Q.AP_TERM ‘setF’) >>
  simp[EXTENSION, set_map'] >>
  ‘setF (restr bf W (f a0)) SUBSET W’
    by (simp[SUBSET_DEF] >> metis_tac[system_members]) >>
  strip_tac >>
  ‘f a' IN setF (restr bf W (f a0))’ suffices_by metis_tac[SUBSET_DEF] >>
  simp[] >> metis_tac[]
QED

Theorem subsystem_UNION:
  system (A,af) /\ (!V. V IN VS ==> subsystem V (A,af)) ==>
  subsystem (BIGUNION VS) (A, af)
Proof
  csimp[prop6_2, BIGUNION_SUBSET] >> strip_tac >>
  ‘Delta (BIGUNION VS) = (\a b. ?V. V IN (IMAGE Delta VS) /\ V a b)’
    by (simp[Ntimes FUN_EQ_THM 2, PULL_EXISTS] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >> irule thm5_5 >> simp[PULL_EXISTS]
QED

Theorem subsystem_ALT:
  subsystem V (A,af) <=>
  V SUBSET A /\ system(A,af) /\ hom (restr (\x.x) V) (V, restr af V) (A,af)
Proof
  eq_tac
  >- (strip_tac >> drule_then assume_tac subsystem_system >>
      ‘system (A,af) /\ V SUBSET A’ by fs[subsystem_def] >> simp[] >>
      simp[hom_def] >> reverse conj_tac >- simp[restr_def] >>
      simp[restr_applies] >>
      ‘!a. a IN V ==> mapF (restr (\x.x) V) (af a) = mapF (\x.x) (af a)’
        suffices_by (simp[mapID] >> fs[subsystem_def, SUBSET_DEF]) >>
      rw[] >> irule map_CONG >> simp[restr_def] >>
      metis_tac[system_members, restr_def]) >>
  simp[subsystem_def] >> metis_tac[]
QED

Theorem subsystem_INTER:
  system (A,af) /\ (!V. V IN VS ==> subsystem V (A,af)) /\ VS <> {} ==>
  subsystem (BIGINTER VS) (A, af)
Proof
  strip_tac >> simp[subsystem_ALT] >> rw[]
  >- fs[BIGINTER_SUBSET, subsystem_def] >>
  rw[hom_def, restr_applies]
  >- (simp[system_def, PULL_EXISTS, restr_def, Fset_def, SUBSET_DEF,
           AllCaseEqs()] >> rw[]
      >- (rename [‘V IN VS’, ‘v IN V’, ‘v IN setF (af v0)’] >>
          ‘system (V,restr af V)’ by metis_tac[subsystem_system] >>
          metis_tac[system_members, restr_def]) >>
      metis_tac[])
  >- metis_tac [MEMBER_NOT_EMPTY, subsystem_def, SUBSET_DEF]
  >- (‘mapF (restr (\x.x) (BIGINTER VS)) (af a) = mapF (\x.x) (af a)’
        suffices_by simp[mapID] >>
      irule map_CONG >>
      ‘!x. x IN setF (af a) ==> x IN BIGINTER VS’
        suffices_by simp[restr_applies] >> rw[] >>
      rename [‘V IN VS’, ‘v IN V’, ‘v IN setF (af v0)’] >>
      ‘v0 IN V’ by simp[] >>
      metis_tac[system_members, restr_def, subsystem_system]) >>
  simp[restr_def] >> metis_tac[]
QED

Definition genS_def:
  genS As X = BIGINTER { V | subsystem V As /\ X SUBSET V }
End

Theorem genS_correct:
  system (A,af) /\ X SUBSET A ==> subsystem (genS (A,af) X) (A,af)
Proof
  simp[genS_def] >> strip_tac >>
  irule subsystem_INTER >> simp[EXTENSION] >> IRULE subsystem_refl >>
  simp[]
QED

Definition bounded_def:
  bounded (:'a) (:'b) =
   !a A af. system ((A,af):'a system) /\ a IN A ==>
            ?f V:'b set. INJ f (genS (A,af) {a}) V
End

(* Section 7 *)
(*
Theorem thm7_1:
  hom f (A,af) (B,bf) ==>
  hom f (A,af) (IMAGE f A,restr bf (IMAGE f A)) /\
  (!g h C cf. hom g (IMAGE f A,restr bf (IMAGE f A)) (C,cf) /\
              hom h (IMAGE f A,restr bf (IMAGE f A)) (C,cf) /\
              restr (h o f) A = restr (g o f) A ==> h = g) /\
  hom (eps (kernel A f) A) (A,af) (bquot (A,af) (kernel A f)) /\
  hom (restr (\x.x) (IMAGE f A))
      (IMAGE f A, restr bf (IMAGE f A))
      (B,bf) /\
  iso (IMAGE f A, restr bf (IMAGE f A))
      (bquot (A,af) (kernel A f)) /\
  ?mu. hom mu (bquot (A,af) (kernel A f)) (B,bf) /\
       INJ mu (FST (bquot (A,af) (kernel A f))) B
Proof
  strip_tac >> ‘system (A,af) /\ system (B,bf)’ by fs[hom_def] >>
  drule_then (qspec_then ‘A’ mp_tac) thm6_3_1 >> simp[] >>
  simp[subsystem_ALT] >> strip_tac >>
  conj_asm1_tac
  >- (irule lemma2_4_2 >> rw[] >- fs[hom_def] >>
      qexistsl_tac [‘B’, ‘bf’, ‘restr (\x.x) (IMAGE f A)’] >>
      qabbrev_tac ‘ss = IMAGE f A’ >>
      ‘!a. a IN A ==> f a IN ss’ by metis_tac[IN_IMAGE] >>
      rw[]
      >- (simp[INJ_IFF, PULL_EXISTS, restr_def] >> fs[SUBSET_DEF])
      >- (simp[hom_def, restr_def] >> reverse conj_tac >- fs[hom_def] >>
          fs[hom_def] >> rw[] >> irule map_CONG >> simp[] >> rw[] >>
          metis_tac[system_members, IN_IMAGE])) >>
  conj_asm1_tac
  >- (‘SURJ f A (IMAGE f A)’ suffices_by metis_tac[SURJ_homs_epi, epi_def] >>
      simp[SURJ_DEF]) >>
  conj_asm1_tac >- metis_tac[bquot_correct, prop5_7] >>
  conj_asm1_tac
  >- (drule_then strip_assume_tac prop5_7 >>
      drule_all_then strip_assume_tac
                     (INST_TYPE [delta |-> beta] bquot_coequalizer) >>
      drule_then drule (cj 5 (iffLR coequalizer_thm)) >>
      impl_tac >- simp[FUN_EQ_THM, restr_def, FORALL_PROD] >>
      simp[EXISTS_UNIQUE_THM] >>
      disch_then (CONJUNCTS_THEN2 (qx_choose_then ‘u’ strip_assume_tac)
                  strip_assume_tac) >>
      ‘?Qt qf. bquot (A,af) (kernel A f) = (Qt,qf)’
        by metis_tac[pair_CASES] >>
      ‘SURJ u Qt (IMAGE f A)’
        by (qabbrev_tac ‘imgfA = IMAGE f A’ >> simp[SURJ_DEF, PULL_EXISTS] >>
            conj_tac >- fs[hom_def] >>
            qx_gen_tac ‘b’ >> strip_tac >>
            ‘?a. a IN A /\ f a = b’ by metis_tac[IN_IMAGE] >>
            pop_assum (SUBST1_TAC o SYM) >>
            qpat_x_assum ‘f = restr _ A’
                         (assume_tac o SIMP_RULE (srw_ss()) [FUN_EQ_THM]) >>
            simp[] >> simp[restr_def] >> metis_tac[hom_def, FST]) >>
      ‘INJ u Qt (IMAGE f A)’
        by (qabbrev_tac ‘imgfA = IMAGE f A’ >> simp[INJ_DEF] >>
            conj_tac >- fs[hom_def] >> qx_genl_tac [‘ap1’, ‘ap2’]>>
            rpt strip_tac >> CCONTR_TAC >>
            fs[bquot_def] >>
            ‘(?a1. a1 IN ap1) /\ ?a2. a2 IN ap2’
              by metis_tac[MEMBER_NOT_EMPTY, EMPTY_NOT_IN_partition] >>
            ‘a1 IN A /\ a2 IN A’ by metis_tac[partition_SUBSET, SUBSET_DEF] >>
            rw[] >> fs[partition_def] >> rw[] >> fs[] >>
            ‘a1 <> a2 /\ f a1 <> f a2’ by (rpt strip_tac >> fs[]) >>
            full_simp_tac (bool_ss ++ boolSimps.CONJ_ss)[] >>
            qpat_x_assum ‘f = restr _ _ ’
                         (ASSUME_TAC o SIMP_RULE (srw_ss()) [FUN_EQ_THM]) >>
            pop_assum (fn th => qspec_then ‘a1’ mp_tac th >>
                       qspec_then ‘a2’ mp_tac th) >>
            csimp[restr_def, eps_def] >>
            fs[AC CONJ_ASSOC CONJ_COMM] >> metis_tac[]) >>
      simp[] >>
      irule (iffLR iso_SYM) >> irule BIJ_homs_iso >>
      fs[] >> qexists_tac ‘u’ >> simp[BIJ_DEF]) >>

*)




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
  simple As <=> !R. bisim R As As /\ R equiv_on (FST As) ==> R = Delta (FST As)
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
