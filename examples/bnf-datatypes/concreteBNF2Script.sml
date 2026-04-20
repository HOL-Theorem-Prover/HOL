Theory concreteBNF2
Ancestors
  hol bnfPrelims pred_set cardinal pair ordinalBasic combin
Libs
  bnfBase bnfLib

(* example defining a mutually recursive pair of types that one would
   specify as

mty = M1 pty | M2 ('b -> (pty # mty) option) ;
pty = P1 mty | P2 mty pty    (* non-empty list of mty's *)

*)


(* The functor type for ty1, 'a1 will be instantiated with ty2 eventually;
   'a2 is where this type recurses on itself *)
Type F[pp] = “:'a1 + ('b1 -> ('a1 # 'a2) option)”

val (Fmap0, Fset, bis) = functorToMapAndSet (fullDB()) “:('a1,'a, 'b1)F”
val Fmap = mk_abs(mk_var("f", alpha --> beta), Fmap0)
Overload Fmap = Fmap
Overload Fset = Fset

(* As recursion variable is 'a2, non-emptiness depends on the 'a1 *)

val mapIDs = HOLset.foldl (fn (bI i, A) => #mapID i :: A) [] bis
val mapCONGs = HOLset.foldl (fn (bI i, A) => #mapCONG i :: A) [] bis
val bndthms = HOLset.foldl (fn (bI i, A) => #bndthms i @ A) [] bis
val mapOs = HOLset.foldl (fn (bI i, A) => #mapO i :: A) [] bis
val mapIMAGEs = HOLset.foldl (fn (bI i, A) => #mapIMAGE i @  A) [] bis

val bsimp = asm_simp_tac bool_ss
val BRULE = SIMP_RULE bool_ss
val BCONV = SIMP_CONV bool_ss

(* ----------------------------------------------------------------------
    Can now define set and map for our new functor; establishing
    functoriality and naturalness
   ---------------------------------------------------------------------- *)

Theorem FmapID:
  ^(inst [beta|-> alpha] Fmap) (I:'a -> 'a) =
  I : ('a1,'a,'b1) F -> ('a1,'a,'b1) F
Proof
  CONV_TAC (LAND_CONV BETA_CONV) >>
  REWRITE_TAC mapIDs
QED

Theorem FmapID' = PURE_REWRITE_RULE [FUN_EQ_THM, I_THM] FmapID

Theorem FmapO:
  ^(inst [alpha |-> gamma, beta |-> delta] Fmap) (f2 : 'c -> 'd) o
  ^(inst [beta |-> gamma] Fmap) (g2 : 'a -> 'c) =
  ^(inst [beta |-> delta] Fmap) (f2 o g2) : ('a1,'a,'b1) F -> ('a1,'d,'b1) F
Proof
  CONV_TAC (FORK_CONV(BINOP_CONV BETA_CONV, BETA_CONV)) >>
  REWRITE_TAC(I_o_ID :: mapOs)
QED

Theorem FmapO' =
        CONV_RULE (LAND_CONV $ BCONV[o_DEF, Excl "BETA_CONV"] THENC
                   BCONV[FUN_EQ_THM, Excl "BETA_CONV"])
                  FmapO

fun oprime_ify th = BRULE [FUN_EQ_THM, combinTheory.o_THM] th

val mapIMG_ofy =
  SPEC_ALL o
  CONV_RULE (
    STRIP_QUANT_CONV (
      BINOP_CONV (PURE_ONCE_REWRITE_CONV [GSYM o_THM])
      ) THENC
    BINDER_CONV (PURE_REWRITE_CONV [GSYM FUN_EQ_THM]))

fun mkall ths = ths @ map mapIMG_ofy ths

Theorem FmapIMAGE:
  ^(inst [alpha |-> beta] Fset) (^Fmap (f2:'a -> 'b) x) : 'b set =
  IMAGE f2 (^Fset (x:('a1,'a,'b1) F))
Proof
  CONV_TAC (LAND_CONV (RAND_CONV (RATOR_CONV BETA_CONV))) >>
  REWRITE_TAC (mkall mapIMAGEs @
               [BIMG_EQUAL, IMAGE_UNION, IMAGE_EMPTY, o_THM, GSYM o_ASSOC,
                IMAGE_IMAGE, BIMG_K0, combinTheory.S_THM, BIMG_IMAGEo,
                K_o_THM, K_THM, SKg_thm, UNION_EMPTY1,
                IMAGE_IMAGE_o, IMAGE_IMAGE_ro,BIGUNION_o_IMAGE_IMAGE,
                BIGUNION_o_IMAGE_IMAGEr, GSYM IMAGE_BIGUNION,
                IMAGE_BIGUNIONo,
                UNION_EMPTY, I_THM, I_o_ID])
QED

val th = SCONV [PULL_EXISTS] “x ∈ (BIMG f o g) v”

Theorem FmapCONG:
  (∀a. a ∈ ^Fset v ⇒ f a = g a) ⇒
  ^Fmap (f:'a -> 'b) v = ^Fmap g v
Proof
  REWRITE_TAC[S_THM, K_o_THM, BIMG_K0, K_THM, UNION_EMPTY, UNION_EMPTY1,
              SKg_thm, I_o_ID, BIMG_EQUAL, I_THM, IN_UNION, GSYM o_ASSOC] >>
  strip_tac >> BETA_TAC >> rpt strip_tac >>
  rpt (FIRST (map irule mapCONGs) >> REWRITE_TAC[] >> rpt strip_tac) >>
  first_x_assum irule >> bsimp [th, PULL_EXISTS] >>
  rpt (first_assum $ irule_at Any)
QED

Theorem Fmap_eq_id:
  (∀b. b ∈ ^Fset x ⇒ g b = b) ⇒ ^(inst [beta |-> alpha] Fmap) g x = x
Proof
  strip_tac >> CONV_TAC (RAND_CONV (REWR_CONV $ GSYM FmapID')) >>
  irule FmapCONG >> simp[]
QED

(* ----------------------------------------------------------------------
    functor must also be bounded
   ---------------------------------------------------------------------- *)
(*
Theorem Fset1_bounded:
  Fset1 (v:('a1,'a2,'b1)F) ≼ univ(:num + 'b1)
Proof
  irule UNION_CARDLE >>
  REWRITE_TAC[num_INFINITE,disjUNION_UNIV,CARD_ADD_FINITE_EQ,
              BIMG_K0, EMPTY_CARDLEQ, BIMG_EQUAL] >>
  conj_tac
  >- ((* l branch *)
      metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                #bndthms sum_data))
  >- ((* r branch *)
      irule CARD_BIGUNION >>
      simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE, UNIV_NOT_EMPTY,
                        CARD_ADD_FINITE_EQ, SING_CARDLE, disjUNION_EQ_EMPTY] >>
      reverse conj_tac
      >- (irule IMAGE_cardleq_rwt >> (* setR ok *)
          metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                                 #bndthms sum_data))
      >- (rpt strip_tac >>
          irule CARD_BIGUNION >>
          simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE, UNIV_NOT_EMPTY,
                            CARD_ADD_FINITE_EQ, SING_CARDLE,
                            disjUNION_EQ_EMPTY] >>
          reverse conj_tac
          >- (irule IMAGE_cardleq_rwt >> (* function OK *)
              metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                                     #bndthms fun_data))
          >- (rpt strip_tac >>
              irule CARD_BIGUNION >>
              simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE,
                                UNIV_NOT_EMPTY,
                                CARD_ADD_FINITE_EQ, SING_CARDLE,
                                disjUNION_EQ_EMPTY] >>
              reverse conj_tac
              >- (irule IMAGE_cardleq_rwt >> (* optSET OK *)
                  metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                            #bndthms opt_data)) >>
              rpt strip_tac >>(* pair OK *)
              metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                        UNION_EMPTY :: #bndthms pair_data))))
QED
*)

Theorem Fset_bounded:
  ^Fset (v:('a1,'a,'b1)F) ≼ univ(:num + 'b1)
Proof
  REWRITE_TAC[S_THM, BIMG_K0, SKg_thm, K_o_THM, K_THM, UNION_EMPTY,
              UNION_EMPTY1, I_o_ID, BIMG_EQUAL, I_THM] >>
  REWRITE_TAC[o_THM] >>
  irule CARD_BIGUNION >>
  simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE, UNIV_NOT_EMPTY, o_THM,
                    CARD_ADD_FINITE_EQ, SING_CARDLE, disjUNION_EQ_EMPTY,
                    disjUNION_UNIV] >>
  reverse conj_tac
  >- (irule IMAGE_cardleq_rwt (* setR ok *) >>
      resolve_then (Pos last) irule CARD_LE_ADDR cardleq_TRANS >>
      FIRST (map MATCH_ACCEPT_TAC bndthms))
  >- (rpt strip_tac >>
      irule CARD_BIGUNION >>
      simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE, UNIV_NOT_EMPTY,
                        CARD_ADD_FINITE_EQ, SING_CARDLE,
                        disjUNION_EQ_EMPTY] >>
      reverse conj_tac
      >- (irule IMAGE_cardleq_rwt (* function OK *) >>
          resolve_then (Pos last) irule CARD_LE_ADDL cardleq_TRANS >>
          FIRST (map MATCH_ACCEPT_TAC bndthms))
      >- (rpt strip_tac >> REWRITE_TAC[o_THM] >>
          irule CARD_BIGUNION >>
          simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE, UNIV_NOT_EMPTY,
                            CARD_ADD_FINITE_EQ, SING_CARDLE,
                            disjUNION_EQ_EMPTY] >>
          reverse conj_tac
          >- (irule IMAGE_cardleq_rwt (* optSET OK *) >>
              resolve_then (Pos last) irule CARD_LE_ADDR cardleq_TRANS >>
              FIRST (map MATCH_ACCEPT_TAC bndthms))
          >- (rpt strip_tac >>
              resolve_then (Pos last) irule CARD_LE_ADDR cardleq_TRANS >>
              FIRST (map MATCH_ACCEPT_TAC bndthms))))
QED

(* ----------------------------------------------------------------------
    start constructing algebra-level arguments
   ---------------------------------------------------------------------- *)

Definition Fin_def:
  Fin As = { a : ('a1,'a,'b1) F | ^Fset a ⊆ As }
End

Theorem witness:
  Fin (∅ :'a2 set) ≠ ∅
Proof
  REWRITE_TAC[EXTENSION, Fin_def] >>
  simp_tac bool_ss [NOT_IN_EMPTY, IN_GSPEC_IFF,
                    SUBSET_DEF, IN_UNION, IN_BIGUNION, IN_IMAGE, PULL_EXISTS,
                    K_THM, NOT_IN_EMPTY, IN_equal, IN_UNIV] >>
  (* this stage needs to be doable by appeal to a suitably constructed
     witness theorem, one about sums in this case *)
  qexists_tac ‘INL ARB’ >> simp[]
QED

Theorem IN_setR:
  x IN setR (INR x)
Proof
  simp[]
QED

Theorem IN_setSND:
  y IN setSND (x,y)
Proof
  simp[]
QED

Theorem IN_optSET:
  x IN optSET (SOME x)
Proof
  simp[bnfPrelimsTheory.optSET_def]
QED

Theorem IN_fnSET:
  v ∈ flip IMAGE UNIV (K v)
Proof
  bsimp[combinTheory.C_THM, combinTheory.K_THM, IN_IMAGE, IN_UNIV]
QED

(* given chain of ∃x1 x2 .. xn. x1 ∈ set1 x2 ∧ x2 ∈ set2 x3 ∧ ...
                                x<n-1> ∈ set<n-1> xn
   push last xn to end, and resolve with exists-thm, which should all be of
   form ∃y x. x IN set<i> y

   The existing forms above x ∈ set (f x)
*)

Theorem Fset_exists:
  ∃x. ^Fset x ≠ ∅
Proof
  REWRITE_TAC[S_THM, BIMG_K0, K_o_THM, UNION_EMPTY1, K_THM, I_THM, SKg_thm,
              I_o_ID, BIMG_EQUAL, EXTENSION, NOT_IN_EMPTY] >>
  CONV_TAC (BINDER_CONV NOT_FORALL_CONV) >>
  REWRITE_TAC[o_THM, DE_MORGAN_THM] >>
  bsimp[IN_UNION, IN_BIGUNION, IN_IMAGE, PULL_EXISTS, o_THM] >>
  irule_at Any IN_setR >>
  irule_at Any IN_fnSET >>
  irule_at Any IN_optSET >>
  irule_at Any IN_setSND
QED

Definition alg_def:
  alg (A : 'a2 set, s : ('a1,'a2,'b1) F -> 'a2) ⇔ ∀x. x ∈ Fin A ⇒ s x ∈ A
End

Theorem alg_nonempty:
  alg(A, s : ('a1,'a2,'b1)F -> 'a2) ⇒ A ≠ ∅
Proof
  rpt strip_tac >> gvs[alg_def] >>
  ‘Fin ∅ : ('a1,'a2,'b1) F set = ∅’ by simp[EXTENSION] >>
  gs[witness]
QED

Definition minset_def:
  minset (s : ('a1,'a2,'b1)F -> 'a2) = BIGINTER { B | alg(B,s) }
End

Theorem minset_is_alg[simp]:
  alg (minset s, s)
Proof
  simp[minset_def, alg_def, Fin_def, SUBSET_BIGINTER]
QED

Theorem IN_minset:
  x IN minset s ⇔ ∀A. alg(A,s) ⇒ x IN A
Proof
  simp[minset_def]
QED

Definition hom_def:
  hom h (A,s) (B,t) ⇔
    alg(A,s) ∧ alg(B,t) ∧ (∀a. a IN A ⇒ h a IN B) ∧
    ∀af. af ∈ Fin A ⇒ t (Fmap h af) = h (s af)
End

Theorem homs_on_same_domain:
  hom h (A,s) (B,t) ∧ (∀a. a ∈ A ⇒ h' a = h a) ⇒ hom h' (A,s) (B,t)
Proof
  simp_tac bool_ss [hom_def, Fin_def] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >> rpt strip_tac >>
  rename [‘Fset af ⊆ A’] >>
  ‘s af ∈ A’ by gs[alg_def, Fin_def] >> simp[] >>
  ‘Fmap h' af = Fmap h af’ suffices_by simp[] >>
  irule (BETA_RULE FmapCONG) >> simp_tac bool_ss [] >> metis_tac[SUBSET_DEF]
QED

Theorem homs_compose:
  hom f (A : 'a2 set,s : ('a1,'a2,'b1)F -> 'a2) (B : 'c2 set,t) ∧
  hom g (B,t) (C : 'd2 set,u) ⇒
  hom (g o f) (A,s) (C,u)
Proof
  simp_tac bool_ss [hom_def, SF CONJ_ss, o_THM] >> rpt strip_tac >>
  RULE_ASSUM_TAC GSYM >> bsimp [] >>
  ‘Fmap f af ∈ Fin B’
    by (qpat_x_assum ‘af ∈ Fin _’ mp_tac >>
        simp_tac bool_ss [Fin_def, IN_GSPEC_IFF, BETA_RULE FmapIMAGE,
                          SUBSET_UNIV] >>
        bsimp [SUBSET_DEF, IN_IMAGE, PULL_EXISTS]) >>
  bsimp [BETA_RULE FmapO', I_o_ID]
QED
(*
Theorem Fset2_SUBSET_minset:
  Fset2 f ⊆ minset s ⇒ s f ∈ minset s
Proof
  simp_tac bool_ss [IN_minset, SUBSET_DEF] >> rpt strip_tac >>
  first_assum (irule o SRULE[alg_def]) >>
  simp[Fin_def, BIMG_EQUAL, BIMG_K0] >>
  simp[NoAsms, SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
  first_x_assum irule>> ASM_REWRITE_TAC[] >>
  simp[PULL_EXISTS, IN_equal] >> metis_tac[]
QED

Theorem minset_ind:
  ∀P. (∀x. Fset2 x ⊆ minset s ∧ (∀y. y ∈ Fset2 x ⇒ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ minset s ⇒ P x
Proof
  gen_tac >>
  ‘∀x. (∀y. y ∈ Fset2 x ⇒ P y) ⇔ Fset2 x ⊆ {z | P z}’
    by (gen_tac >> simp_tac bool_ss [SUBSET_DEF]>>
        CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
        REWRITE_TAC[]) >>
  pop_assum (REWRITE_TAC o single) >>
  strip_tac >>
  ‘minset s ⊆ {x | P x } INTER minset s’ suffices_by simp[SUBSET_DEF, IN_DEF] >>
  simp[minset_def, SimpL “$SUBSET”] >> irule BIGINTER_SUBSET >>
  qexists_tac ‘{x | P x} INTER minset s’ >> reverse conj_tac
  >- REWRITE_TAC[INTER_SUBSET] >>
  simp_tac bool_ss [alg_def, Fin_def, SUBSET_DEF, IN_INTER] >>
  CONV_TAC pred_setLib.SET_SPEC_CONV >> GEN_TAC >>
  CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [IN_INTER, IN_UNIV, IMP_CONJ_THM, FORALL_AND_THM] >>
  simp_tac bool_ss [GSYM SUBSET_DEF] >> conj_tac
  >- (strip_tac >>
      CONV_TAC pred_setLib.SET_SPEC_CONV >> first_x_assum irule >>
      ASM_REWRITE_TAC[]) >>
  rename [‘_ ⇒ s x ∈ minset s (* g *)’] >>
  Cases_on ‘Fset2 x ⊆ {x|P x}’ >> ASM_REWRITE_TAC[] >>
  ntac 2 (pop_assum kall_tac) >>
  MATCH_ACCEPT_TAC (GEN_ALL Fset2_SUBSET_minset)
QED

Theorem hom_equals_fmap:
  hom h (A,f) (B,g) ∧ Fset2 x ⊆ A ⇒ h (f x) = g (Fmap h x)
Proof
  simp_tac bool_ss [hom_def] >> strip_tac >> sym_tac >>
  first_x_assum irule >>
  simp_tac bool_ss [Fin_def, SUBSET_UNIV] >>
  CONV_TAC pred_setLib.SET_SPEC_CONV >> first_assum ACCEPT_TAC
QED

Theorem minsub_gives_unique_homs:
  hom h1 (minset s, s) (C,t) ∧ hom h2 (minset s,s) (C,t) ⇒
  ∀a. a ∈ minset s ⇒ h1 a = h2 a
Proof
  strip_tac >> ho_match_mp_tac minset_ind >> qx_gen_tac ‘af’ >> strip_tac >>
  rpt (dxrule_then drule hom_equals_fmap) >> rpt strip_tac >>
  ASM_REWRITE_TAC[] >> AP_TERM_TAC >>
  irule FmapCONG >> bsimp []
QED

Definition subalg_def:
  subalg (A,s) (B,t) ⇔ alg(A,s) ∧ alg (B,t) ∧
                       (∀af. af ∈ Fin A ⇒ s af = t af) ∧ A ⊆ B
End

Theorem subalgs_preserve_homs:
  subalg A1 A2 ∧ hom f A2 C ⇒ hom f A1 C
Proof
  Cases_on ‘A1’ >> Cases_on ‘A2’ >> Cases_on ‘C’ >>
  simp[hom_def,Fin_def,subalg_def] >> metis_tac[SUBSET_DEF]
QED

Theorem minsub_subalg:
  alg(A,s) ⇒ subalg (minset s, s) (A,s)
Proof
  simp[subalg_def, minset_def] >> strip_tac >>
  irule BIGINTER_SUBSET >> simp[] >> metis_tac[SUBSET_REFL]
QED

Theorem minsub_I_subalg:
  alg(A,s) ⇒ hom I (minset s, s) (A,s)
Proof
  strip_tac >> drule minsub_subalg >>
  simp[hom_def, Fin_def, FmapID, subalg_def, SUBSET_DEF]
QED

Type alg[local,pp] = “:'a2 set # (('a1,'a2,'b1)F -> 'a2)”

val idx_tydef as
              {absrep_id, newty, repabs_pseudo_id, termP, termP_exists,
               termP_term_REP, ...} =
  newtypeTools.rich_new_type{
  tyname = "idx",
  exthm = prove(“∃i : ('a1,'a2,'b1) alg. alg i”,
           simp[pairTheory.EXISTS_PROD] >> qexists_tac ‘UNIV’ >>
           simp[alg_def]),
  ABS = "mkIx",
  REP = "dIx"};

Definition bigprod_def:
  bigprod : ('a1, ('a1,'a2,'b1)idx -> 'a2, 'b1) alg =
  ({ f | ∀i. f i ∈ FST (dIx i) },
   λfv i. SND (dIx i) $ Fmap (λf. f i) fv)
End

Theorem bigprod_isalg:
  alg bigprod
Proof
  bsimp[bigprod_def, alg_def, FORALL_PROD, Fin_def, IN_GSPEC_IFF] >>
  rpt strip_tac >>
  Cases_on ‘dIx i’ >> rename [‘dIx i = (A,s)’] >> bsimp[FST, SND] >>
  ‘alg(A,s)’ by metis_tac[termP_term_REP] >>
  pop_assum mp_tac >> bsimp[alg_def] >>
  disch_then irule >>
  bsimp[Fin_def, IN_GSPEC_IFF, SUBSET_UNIV, FmapIMAGE] >>
  bsimp[SUBSET_DEF, PULL_EXISTS, IN_IMAGE] >>
  rpt strip_tac >> drule_all $ iffLR SUBSET_DEF >>
  bsimp[IN_GSPEC_IFF] >> disch_then $ qspec_then ‘i’ mp_tac >>
  bsimp[FST]
QED

Theorem bigprod_proj:
  alg (A,s) ⇒ hom (λf. f (mkIx (A,s))) bigprod (A,s)
Proof
  simp[hom_def, bigprod_def] >> rpt strip_tac
  >- metis_tac[bigprod_isalg, bigprod_def]
  >- (‘dIx (mkIx (A,s)) = (A,s)’ by metis_tac[repabs_pseudo_id] >>
      first_x_assum $ qspec_then ‘mkIx (A,s)’ mp_tac >> simp[]) >>
  ‘dIx (mkIx (A,s)) = (A,s)’ by metis_tac[repabs_pseudo_id] >>
  simp[]
QED

val bigprod_ty = ty_antiq “: ('a1, ('a1,'a2,'b1) idx -> 'a2, 'b1) alg”

Theorem minbigprod_has_unique_homs:
  let s = SND (bigprod : ^bigprod_ty)
  in
    ∀A f. alg (A, f : ('a1,'a2,'b1) F -> 'a2) ⇒
          ∃!h. (∀d. d ∉ minset s ⇒ h d = ARB) ∧ hom h (minset s, s) (A, f)
Proof
  Cases_on ‘bigprod : ^bigprod_ty’ >> simp[] >>
  rpt strip_tac >>
  rename [‘bigprod = (AA,FF)’] >> gs[] >>
  ‘alg (AA,FF)’ by simp[bigprod_isalg] >>
  ‘alg (minset FF, FF)’ by simp[] >>
  ‘∃h0. hom h0 (bigprod:^bigprod_ty) (A,f)’
    by (irule_at (Pos hd) bigprod_proj >> simp[]) >>
  ‘subalg (minset FF, FF) (AA,FF)’
    by metis_tac[minsub_subalg] >>
  ‘hom h0 (minset FF, FF) (A,f)’ by metis_tac[subalgs_preserve_homs] >>
  simp[EXISTS_UNIQUE_ALT] >>
  qexists_tac ‘λa. if a ∈ minset FF then h0 a else ARB’ >>
  simp[EQ_IMP_THM, FORALL_AND_THM] >> reverse conj_tac
  >- (irule homs_on_same_domain >> first_assum $ irule_at Any >>
      simp[]) >>
  qx_gen_tac ‘h1’ >> strip_tac >> csimp[FUN_EQ_THM, AllCaseEqs()] >>
  metis_tac[minsub_gives_unique_homs]
QED

(* there are unique homs out of the minimised product of all α-algebras into
   α-algebras, but we have to find an α that is big enough that algebras over
   other types can be injected into them.

*)

(* Traytel's K function, from MSc thesis, p 15 *)

val KK_def = new_specification(
  "KK", ["KK"],
  ord_RECURSION |> Q.ISPEC ‘∅ : γ set’
                |> Q.SPEC ‘λx r. r ∪ { s(x) | Fset2 x ⊆ r }’
                |> Q.SPEC ‘λx rs. BIGUNION rs’
                |> BETA_RULE
                |> Q.GEN ‘s’ |> CONV_RULE SKOLEM_CONV);

Theorem KK_mono:
  ∀β α. α < β ⇒ KK s α ⊆ KK s β
Proof
  ho_match_mp_tac simple_ord_induction >>
  bsimp
               [KK_def, ordlt_SUC_DISCRETE, DISJ_IMP_THM, FORALL_AND_THM,
                ordlt_ZERO, SUBSET_UNION] >>
  rpt strip_tac
  >- (first_x_assum $ drule_then (C (resolve_then (Pos hd) irule) SUBSET_TRANS)>>
      REWRITE_TAC[SUBSET_UNION]) >>
  gs[omax_NONE] >>
  last_x_assum $ drule_then strip_assume_tac>>
  first_x_assum $ drule_all_then assume_tac >>
  irule SUBSET_BIGUNION_I >> simp[]
QED

Theorem KK_mono_LE:
  ∀α β. α ≤ β ⇒ KK s α ⊆ KK s β
Proof
  metis_tac[SUBSET_REFL, KK_mono, ordle_lteq]
QED

Theorem KK_SUB_min:
  ∀α. KK s α ⊆ minset s
Proof
  ho_match_mp_tac simple_ord_induction >>
  simp_tac bool_ss [KK_def, EMPTY_SUBSET] >> rpt strip_tac
  >- (REWRITE_TAC [SUBSET_DEF] >>
      gen_tac >> CONV_TAC (LAND_CONV (REWR_CONV IN_UNION)) >> strip_tac
      >- (irule (iffLR SUBSET_DEF) >> rpt (first_assum $ irule_at Any)) >>
      pop_assum mp_tac >> CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
      strip_tac >> ASM_REWRITE_TAC []>>
      irule Fset2_SUBSET_minset >> irule SUBSET_TRANS >>
      first_assum $ irule_at Any >> ASM_REWRITE_TAC[SUBSET_DEF]) >>
  ASM_REWRITE_TAC [BIGUNION_IMAGE_SUBSET, IN_preds]
QED

Theorem KK_fixp_is_alg:
  { s x | x | Fset2 x ⊆ KK s ε } = KK s ε ⇒
  alg(KK s ε, s)
Proof
  simp_tac bool_ss [alg_def, Fin_def] >>
  disch_then (assume_tac o SYM) >> gen_tac >>
  CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
  REWRITE_TAC[SUBSET_UNIV] >> strip_tac >>
  qpat_assum ‘_ = _’ (ONCE_REWRITE_TAC o single) >>
  CONV_TAC pred_setLib.SET_SPEC_CONV >>
  irule_at Any EQ_REFL >> first_assum ACCEPT_TAC
QED

Theorem KK_sup:
  ords ≼ 𝕌(:num + 'a) ⇒
  KK s (sup ords : 'a ordinal) = BIGUNION (IMAGE (KK s) ords)
Proof
  strip_tac >> Cases_on ‘ords = ∅’ >> simp[KK_def] >>
  Cases_on ‘omax ords’
  >- (gs[omax_NONE] >>
      ‘islimit (sup ords)’
        by (simp[omax_NONE, sup_thm, PULL_EXISTS] >>
            metis_tac[ordlt_TRANS]) >>
      Cases_on ‘sup ords = 0’ >- gs[KK_def, sup_EQ_0] >>
      ‘0 < sup ords’ by metis_tac[IFF_ZERO_lt] >>
      simp[KK_def] >> irule SUBSET_ANTISYM >>
      simp[SUBSET_DEF, PULL_EXISTS, sup_thm] >> rw[] >> (* 2 *)
      metis_tac[SUBSET_DEF, KK_mono]) >>
  gs[omax_SOME] >> rename [‘_ ≤ mx’, ‘mx ∈ ords’] >>
  ‘sup ords = mx’ by metis_tac[sup_eq_max] >> simp[] >>
  irule SUBSET_ANTISYM >> simp[SUBSET_DEF, PULL_EXISTS] >> rw[] (* 2 *)
  >- metis_tac[] >>
  metis_tac[KK_mono_LE, SUBSET_DEF]
QED

Theorem KK_preds_subset:
  BIGUNION (IMAGE (KK s) (preds α)) ⊆ KK s α
Proof
  qid_spec_tac ‘α’ >> ho_match_mp_tac simple_ord_induction >>
  rw[] (* 2 *)
  >- (simp[KK_def, preds_ordSUC] >> irule SUBSET_TRANS >> goal_assum drule >>
      simp[]) >>
  simp[KK_def]
QED

Theorem KK_thm:
  KK s α = if α = 0 then ∅
           else BIGUNION (IMAGE (λa. { s fv | fv | Fset2 fv ⊆ KK s a})
                          (preds α))
Proof
  qid_spec_tac ‘α’ >> ho_match_mp_tac simple_ord_induction >>
  rpt strip_tac >> REWRITE_TAC[ordSUC_ZERO] (* 3 *)
  >- simp[KK_def]
  >- (ONCE_ASM_REWRITE_TAC[KK_def] >>
      simp_tac bool_ss [preds_ordSUC, IMAGE_INSERT, BIGUNION_INSERT] >>
      Cases_on ‘α = 0’
      >- (pop_assum SUBST_ALL_TAC >>
          REWRITE_TAC [KK_def, UNION_EMPTY, preds_0, IMAGE_EMPTY,
                       BIGUNION_EMPTY]) >>
      qpat_x_assum ‘_ = _’ mp_tac >> ASM_REWRITE_TAC[] >>
      disch_then (assume_tac o SYM) >>
      bsimp [AC UNION_ASSOC UNION_COMM]) >>
  ‘α ≠ 0’ by (disch_then SUBST_ALL_TAC >> qpat_x_assum ‘0 < 0o’ mp_tac >>
              REWRITE_TAC[ordlt_REFL]) >>
  bsimp [] >>
  bsimp [KK_def] >>
  simp_tac bool_ss [Once EXTENSION, PULL_EXISTS, IN_BIGUNION, IN_IMAGE] >>
  qx_gen_tac ‘v’ >> iff_tac
  >- (simp_tac bool_ss [PULL_EXISTS, IN_preds] >> qx_gen_tac ‘u’ >>
      Cases_on ‘u = 0’ >- bsimp [NOT_IN_EMPTY] >>
      rpt strip_tac >> rename [‘v ∈ KK s a’] >>
      ‘a ≠ 0’ by (strip_tac >> gs[KK_def]) >>
      ‘KK s a = BIGUNION (IMAGE (λa0. { s fv | fv | Fset2 fv ⊆ KK s a0})
                          (preds a))’ by metis_tac[] >>
      gs[PULL_EXISTS] >> metis_tac[ordlt_TRANS]) >>
  CONV_TAC LEFT_IMP_EXISTS_CONV >> qx_gen_tac ‘u’ >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  REWRITE_TAC [IN_preds] >> strip_tac >>
  rpt strip_tac >> rename [‘a < α’, ‘Fset2 fv ⊆ KK s a’] >>
  qexists_tac ‘a⁺’ >> simp_tac bool_ss [KK_def, IN_UNION] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  metis_tac[islimit_SUC_lt]
QED

Theorem sucbnd_suffices:
  ω ≤ (bd : γ ordinal) ∧ (∀x : ('a1,'a2,'b1)F. Fset2 x ≼ preds bd) ⇒
  alg (KK (s:('a1,'a2,'b1)F -> 'a2) (csuc bd), s)
Proof
  strip_tac >>
  ‘INFINITE (preds bd)’ by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
  irule KK_fixp_is_alg >> irule SUBSET_ANTISYM >> conj_tac >>
  ONCE_REWRITE_TAC [SUBSET_DEF] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [PULL_EXISTS] >>
  rpt strip_tac
  >- (rename [‘s fv ∈ KK s _’] >>
      drule_then strip_assume_tac csuc_is_nonzero_limit >>
      qpat_x_assum ‘Fset2 fv ⊆ _’ mp_tac >>
      bsimp [KK_def, PULL_EXISTS, IN_BIGUNION, IN_IMAGE,
                            IN_preds, lt_csuc, SUBSET_DEF] >>
      disch_then (strip_assume_tac o
                  BRULE [GSYM RIGHT_EXISTS_IMP_THM,
                                     SKOLEM_THM]) >>
      rename [‘_ ∈ KK s (g _)’, ‘preds (g _) ≼ preds bd’] >>
      qabbrev_tac ‘B = sup (IMAGE g $ Fset2 fv)’ >>
      ‘IMAGE g $ Fset2 fv ≼ univ(:num + (γ + num -> bool))’
        by (irule IMAGE_cardleq_rwt >>
            first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
            resolve_then (Pos hd) irule preds_inj_univ cardleq_TRANS >>
            simp[cardleq_lteq, bumpUNIV_cardlt]) >>
      ‘∀a. a < B ⇔ ∃v. v ∈ Fset2 fv ∧ a < g v’
        by bsimp [Abbr‘B’, sup_thm, PULL_EXISTS, IN_IMAGE] >>
      qexists_tac ‘B⁺’ >> bsimp [KK_def] >> reverse conj_tac
      >- (simp[preds_ordSUC, INFINITE_cardleq_INSERT] >>
          bsimp [Abbr‘B’, preds_sup, dclose_BIGUNION] >>
          irule CARD_BIGUNION >>
          bsimp [IMAGE_cardleq_rwt, PULL_EXISTS, IN_IMAGE]) >>
      ‘KK s B = BIGUNION (IMAGE (KK s) (IMAGE g (Fset2 fv)))’
        by bsimp [KK_sup, Abbr‘B’] >>
      ‘s fv ∈ {s x | x | Fset2 x ⊆ KK s B}’ suffices_by
        (strip_tac >> ASM_REWRITE_TAC[IN_UNION]) >>
      CONV_TAC pred_setLib.SET_SPEC_CONV >>
      qexists_tac ‘fv’ >> bsimp [SUBSET_DEF, PULL_EXISTS] >>
      qx_gen_tac ‘x’ >>
      rpt strip_tac >> REWRITE_TAC[IN_BIGUNION, IN_IMAGE] >>
      bsimp [PULL_EXISTS] >> qexists_tac ‘x’ >>
      bsimp []) >>
  rename [‘v ∈ KK s (csuc bd)’] >>
  drule_then strip_assume_tac csuc_is_nonzero_limit >>
  qpat_x_assum ‘v ∈ KK _ _’ mp_tac >>
  bsimp [KK_def, IN_BIGUNION, IN_IMAGE, PULL_EXISTS,
                        IN_preds] >>
  qx_gen_tac ‘a’ >>
  bsimp [Once KK_thm] >>
  Cases_on ‘a = 0’ >- bsimp [NOT_IN_EMPTY] >>
  bsimp [IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_preds] >>
  qx_gen_tac ‘b’ >> CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  strip_tac >> rename [‘Fset2 fv ⊆ KK s b’] >>
  first_assum $ irule_at Any >>
  irule SUBSET_BIGUNION_SUBSET_I >>
  bsimp [PULL_EXISTS, IN_IMAGE, IN_preds] >>
  qexists_tac ‘b’ >> first_assum $ irule_at Any >>
  irule ordlt_TRANS >> qexists_tac ‘a’ >> ASM_REWRITE_TAC[]
QED

Theorem KKbnd_EQ_minset:
  ω ≤ (bd : γ ordinal) ∧ (∀x : ('a1,'a2,'b1)F. Fset2 x ≼ preds bd) ⇒
  KK (s : ('a1,'a2,'b1)F -> 'a2) (csuc bd) = minset s
Proof
  strip_tac >> drule_all_then (qspec_then ‘s’ assume_tac) sucbnd_suffices >>
  irule SUBSET_ANTISYM >> REWRITE_TAC[KK_SUB_min] >>
  drule minsub_I_subalg >>
  bsimp [hom_def, FmapID, SUBSET_DEF, I_THM]
QED

Theorem nontrivialBs:
  (∃x:('a1,'a2,'b1)F. Fset2 x ≠ ∅) ⇒
  ∀B. (B:'a2 set) ≼ Fin B : ('a1,'a2,'b1) F set
Proof
  rpt strip_tac >> simp[cardleq_def] >>
  qexists_tac ‘λb. Fmap (K b) x’ >>
  simp_tac bool_ss [INJ_IFF, Fin_def, FmapIMAGE, SUBSET_UNIV] >>
  conj_tac
  >- (rpt strip_tac >> CONV_TAC pred_setLib.SET_SPEC_CONV >>
      bsimp [FmapIMAGE, SUBSET_DEF, IN_IMAGE, K_THM,
                            PULL_EXISTS]) >>
  simp_tac bool_ss [EQ_IMP_THM] >> rpt strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM ‘Fset2’ ) >>
  bsimp [FmapIMAGE, EXTENSION, IN_IMAGE, PULL_EXISTS,
                        K_THM] >>
  metis_tac[MEMBER_NOT_EMPTY]
QED

(* see Lemma 33 in ITP2014's
     "Cardinals in Isabelle/HOL" by Blanchette, Popescu and Traytel
 *)
Theorem CBDb:
  ω ≤ (bd : γ ordinal) ∧ (∀x:('a1,'a2,'b1)F. Fset2 x ≼ preds bd) ∧
  (∃x:('a1,γ ordinal,'b1)F. Fset2 x ≠ ∅)
⇒
  ∀B:'a2 set.
    𝟚 ≼ B ⇒
    Fin B : ('a1,'a2,'b1)F set ≼
    B ** cardSUC (Fin (preds bd) : ('a1,γ ordinal,'b1)F set)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘kA = Fin (preds bd) : ('a1,γ ordinal,'b1) F set CROSS
                    (B ** preds bd)’ >>
  qmatch_abbrev_tac ‘_ ≼ B ** k’ >>
  ‘kA ≼ B ** k’
    by (simp[Abbr‘k’, Abbr‘kA’] >> irule CARD_MUL2_ABSORB_LE >>
        simp[] >> rpt strip_tac
        >- (drule_all cardleq_TRANS >> simp[])
        >- (‘INFINITE (preds bd)’
              by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
            ‘preds bd ≼ Fin (preds bd) : ('a1,γ ordinal,'b1) F set’
              by metis_tac[nontrivialBs] >>
            metis_tac[CARD_LE_FINITE])
        >- (resolve_then (Pos last) irule CARD_LE_EXP cardleq_TRANS >>
            simp[]) >>
        irule set_exp_cardle_cong >> simp[] >> rpt strip_tac
        >- gvs[cardleq_empty] >>
        ‘preds bd ≼ Fin (preds bd) : ('a1,γ ordinal,'b1) F set’
          by metis_tac[nontrivialBs] >>
        first_x_assum $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
        simp[])>>
  first_assum $ C (resolve_then (Pos last) irule) cardleq_TRANS >>
  qabbrev_tac ‘d = λ(y:('a1,'c ordinal,'b1)F, f).
                     Fmap f y : ('a1,'a2,'b1) F’ >>
  simp[cardleq_def] >>
  irule_at Any (SRULE [PULL_EXISTS] SURJ_IMP_INJ) >> qexists_tac ‘d’ >>
  simp[SURJ_DEF] >> conj_tac
  >- (bsimp
                   [FORALL_PROD,Abbr‘kA’, Abbr‘d’, Fin_def,
                    set_exp_def, UNCURRY_DEF, IN_CARD_MUL, SUBSET_UNIV] >>
      CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
      bsimp [FmapIMAGE] >> rpt strip_tac >>
      bsimp [SUBSET_DEF, PULL_EXISTS, IN_IMAGE] >>
      qx_gen_tac ‘b’ >> strip_tac >>
      ‘b ∈ preds bd’ by metis_tac[SUBSET_DEF] >> bsimp []) >>
  qx_gen_tac ‘vf’ >> strip_tac >>
  ‘?g. INJ g (Fset2 vf) (preds bd)’ by metis_tac[cardleq_def] >>
  qabbrev_tac ‘y = Fmap g vf’ >>
  ‘Fset2 vf ⊆ B’
    by (qpat_x_assum ‘vf ∈ Fin _’ mp_tac >>
        simp_tac (bool_ss ++ pred_setLib.PRED_SET_ss)[Fin_def]) >>
  ‘?f. (!b. b ∈ Fset2 vf ⇒ f (g b) = b) /\ (!bp. bp < bd ==> f bp ∈ B)’
    by (‘?be. be ∈ B’ by (simp[MEMBER_NOT_EMPTY] >>
                          strip_tac >> gvs[cardleq_empty]) >>
        qexists_tac ‘λbp. case some b. b IN Fset2 vf /\ g b = bp of
                            NONE => be
                          | SOME b => b
                    ’ >> conj_tac >> bsimp [] >> rpt strip_tac
        >- (qpat_x_assum ‘INJ _ _ (preds bd)’ mp_tac >>
            bsimp [INJ_IFF, SF CONJ_ss] >>
            bsimp [SF CONJ_ss, optionTheory.some_EQ,
                                  optionTheory.option_case_def]) >>
        DEEP_INTRO_TAC optionTheory.some_intro >>
        bsimp [optionTheory.option_case_def] >>
        metis_tac[SUBSET_DEF]) >>
  qexists_tac ‘(y, λbp. if bp ∈ preds bd then f bp else ARB)’ >>
  conj_tac
  >- (bsimp
        [Abbr‘kA’, Fin_def, Abbr‘y’, IN_CARD_MUL, SUBSET_UNIV] >>
      conj_tac
      >- (CONV_TAC pred_setLib.SET_SPEC_CONV >>
          bsimp [FmapIMAGE, INJ_IMAGE_SUBSET]) >>
      simp[set_exp_def]) >>
  simp[Abbr‘d’, Abbr‘y’, FmapO'] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM FmapID'))) >>
  irule FmapCONG >>
  bsimp [o_THM, bool_case_eq, I_THM] >>
  qpat_x_assum ‘INJ _ _ _ ’ mp_tac >>
  simp_tac bool_ss [INJ_IFF, IN_preds]
QED

Theorem preds_bd_lemma[local]:
  Fset2 (gv  : ('a1,γ ordinal,'b1)F) ≠ ∅ ⇒
  preds (bd:γ ordinal) ≼
    preds (oleast a:('a1,γ ordinal,'b1)F ordinal.
             preds a ≈ Fin (preds bd) : ('a1,γ ordinal,'b1) F set)
Proof
  strip_tac >>
  ‘preds bd ≼ Fin (preds bd) : ('a1,γ ordinal,'b1) F set’
    by metis_tac[nontrivialBs] >>
  pop_assum mp_tac >>
  simp[Once cardleq_lteq, SimpL “$==>”] >> strip_tac
  >- (DEEP_INTRO_TAC oleast_intro >> conj_tac
      >- (irule cardeq_ordinals_exist >>
          simp[Once disjUNION_UNIV] >>
          resolve_then (Pos hd) irule CARD_LE_UNIV
                       CARD_LE_TRANS >>
          simp[CARD_LE_ADDL]) >>
      metis_tac[cardleq_lteq, CARD_LT_CONG, CARD_EQ_REFL]) >>
  DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- (irule cardeq_ordinals_exist >>
      simp[Once disjUNION_UNIV] >>
      resolve_then (Pos hd) irule CARD_LE_UNIV CARD_LE_TRANS >>
      simp[CARD_LE_ADDL]) >>
  metis_tac[CARD_LE_REFL, CARD_LE_CONG]
QED

Theorem Fin_MONO:
  s ⊆ t ⇒ Fin s ⊆ Fin t
Proof
  simp_tac bool_ss [Fin_def, SUBSET_DEF] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV)>> rpt strip_tac >>
  bsimp []
QED

Theorem Fin_cardleq:
  s ≼ t ⇒ Fin s : ('a1,'a2,'b1) F set ≼ Fin t : ('a1,'c2,'b1) F set
Proof
  simp_tac bool_ss [Fin_def, cardleq_def] >>
  disch_then $ qx_choose_then ‘f’ strip_assume_tac >>
  qexists_tac ‘Fmap f’ >>
  simp_tac bool_ss [INJ_IFF] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [FmapIMAGE, IMAGE_I] >>
  rpt strip_tac
  >- (dxrule_then assume_tac INJ_IMAGE_SUBSET >>
      irule SUBSET_TRANS >> irule_at Any IMAGE_SUBSET >>
      rpt (first_assum $ irule_at Any)) >>
  simp_tac bool_ss [EQ_IMP_THM] >> strip_tac >>
  ‘Fmap (LINV f s o f) x = Fmap I x ∧ Fmap (LINV f s o f) y = Fmap I y’
    by (conj_tac >> irule FmapCONG >> drule_then assume_tac LINV_DEF >>
        simp_tac bool_ss [I_THM, o_THM] >>
        metis_tac[SUBSET_DEF]) >>
  qpat_x_assum ‘Fmap f x = _’ (mp_tac o Q.AP_TERM ‘Fmap (LINV f s)’) >>
  bsimp [FmapO',funMap_ID, I_THM, FmapID]
QED

Theorem cardADD2[local]:
  s ≼ s +_c 𝟚
Proof
  simp[CARD_LE_ADDR]
QED

Theorem alg_cardinality_bound:
  ω ≤ (bd : 'b1 ordinal) ∧ (∀x:('a1,'a2+bool,'b1)F. Fset2 x ≼ preds bd) ∧
  (∃x:('a1,'b1 ordinal,'b1)F. Fset2 x ≠ ∅) ⇒
  KK (s:('a1,'a2,'b1)F -> 'a2) (csuc bd) ≼
  𝟚 ** (cardSUC $ Fin (preds bd) : ('a1,'b1 ordinal,'b1) F set)
Proof
  strip_tac >> rename [‘Fset2 gv ≠ ∅’] >>
  qmatch_abbrev_tac ‘_ ≼ 𝟚 ** BD’ >>
  ‘INFINITE BD’
    by (simp_tac bool_ss [Abbr‘BD’, FINITE_cardSUC] >> strip_tac >>
        ‘preds bd ≼ Fin (preds bd) : ('a1,'b1 ordinal,'b1) F set’
          by metis_tac[nontrivialBs] >>
        ‘FINITE (preds bd)’ by metis_tac[CARD_LE_FINITE] >>
        gs[FINITE_preds]) >>
  ‘BD ≠ ∅’ by simp[Abbr‘BD’] >>
  ‘∀i. i < csuc bd ⇒ KK s i ≼ 𝟚 ** BD’
    suffices_by (strip_tac >>
                 bsimp [csuc_is_nonzero_limit, KK_def] >>
                 irule CARD_BIGUNION >>
                 bsimp [PULL_EXISTS, IN_IMAGE, IN_preds,
                                       FINITE_setexp, CARD_12] >>
                 irule IMAGE_cardleq_rwt >>
                 resolve_then Any
                              (fn th =>
                                 resolve_then (Pos hd) irule th cardleq_TRANS)
                              cardleq_REFL
                              CARD_LE_EXP >>
                 irule set_exp_cardle_cong >>
                 bsimp [CARD_12, cardleq_REFL, cardSUC_def,
                                       NOT_INSERT_EMPTY, Abbr‘BD’] >>
                 irule cardleq_preds_csuc >> metis_tac[preds_bd_lemma]) >>
  ho_match_mp_tac ord_induction >> rpt strip_tac >>
  simp_tac bool_ss [Once KK_thm] >> COND_CASES_TAC
  >- simp_tac bool_ss [EMPTY_CARDLEQ] >> irule CARD_BIGUNION >>
  bsimp [IN_IMAGE, FINITE_setexp, CARD_12, PULL_EXISTS, IN_preds] >>
  reverse conj_tac
  >- (irule IMAGE_cardleq_rwt >>
      resolve_then Any
                   (fn th =>
                      resolve_then (Pos hd) irule th cardleq_TRANS)
                   cardleq_REFL
                   CARD_LE_EXP >> irule set_exp_cardle_cong >>
      bsimp [NOT_INSERT_EMPTY, cardleq_REFL] >> simp[] >>
      RULE_ASSUM_TAC (BRULE[lt_csuc]) >>
      drule_then (qspec_then ‘bd’ assume_tac) preds_bd_lemma >>
      dxrule_then assume_tac cardleq_preds_csuc >>
      bsimp [Abbr‘BD’, cardSUC_def] >>
      pop_assum (C (resolve_then (Pos last) irule) cardleq_TRANS) >>
      first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
      simp_tac bool_ss [preds_csuc_lemma]) >>
  qx_gen_tac ‘j’ >> strip_tac >>
  ‘{ s fv | fv | Fset2 fv ⊆ KK s j} = IMAGE s (Fin (KK s j))’
    by (simp_tac bool_ss [EXTENSION, Fin_def, IN_IMAGE] >>
        CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
        simp_tac bool_ss [SUBSET_UNIV]) >>
  ASM_REWRITE_TAC [] >>
  irule IMAGE_cardleq_rwt >>
  resolve_then (Pos hd) irule (MATCH_MP (GEN_ALL Fin_cardleq) cardADD2)
               cardleq_TRANS >>
  drule_then (drule_then $ qspec_then ‘KK s j +_c 𝟚’ mp_tac) CBDb >> impl_tac
  >- (conj_tac >- first_assum $ irule_at Any >> simp[CARD_LE_ADDL]) >>
  disch_then $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
  first_x_assum $ qspec_then ‘j’ mp_tac >> simp[] >>
  impl_tac >- metis_tac[ordlt_TRANS] >>
  disch_then
    (C (resolve_then (Pos hd) (qspecl_then [‘𝟚’, ‘𝟚’] mp_tac)) CARD_LE_ADD) >>
  simp[] >> strip_tac >>
  pop_assum (
    C (resolve_then (Pos (el 2)) (resolve_then (Pos last)
                                  (qspec_then ‘BD’ mp_tac) cardleq_REFL))
    set_exp_cardle_cong) >>
  impl_tac >- simp[Abbr‘BD’] >>
  disch_then (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
  ‘𝟚 ≼ 𝟚 ** BD’ by (simp[cardleq_setexp] >> simp[Abbr‘BD’]) >>
  ‘INFINITE (𝟚 ** BD)’ by simp[] >>
  ‘𝟚 ** BD +_c 𝟚 ≈ 𝟚 ** BD’
    by metis_tac[CARD_ADD_SYM, CARD_ADD_ABSORB, cardeq_TRANS] >>
  pop_assum (C (resolve_then (Pos hd) (qspecl_then [‘BD’, ‘BD’] mp_tac))
               set_exp_card_cong) >> simp_tac bool_ss [cardeq_REFL] >>
  strip_tac >>
  pop_assum (C (resolve_then (Pos hd)
                (resolve_then (Pos hd) irule cardeq_REFL))
             (iffRL CARD_LE_CONG)) >>
  resolve_then (Pos hd) (resolve_then (Pos hd) irule cardeq_REFL)
               set_exp_product (iffRL CARD_LE_CONG) >>
  irule set_exp_cardle_cong >>
  simp_tac bool_ss [NOT_INSERT_EMPTY, cardleq_REFL] >>
  ONCE_REWRITE_TAC [cardleq_lteq] >>
  bsimp [CARD_SQUARE_INFINITE]
QED

val ordOf_def = new_specification ("ordOf_def", ["ordOf"],
  MATCH_MP (cardeq_ordinals_exist
              |> INST_TYPE [beta |-> “:num + 'a”])
           (CARD_LE_UNIV |> SPEC_ALL |> INST_TYPE [alpha |-> “:num + 'a”])
       |> Q.GEN ‘s’
       |> CONV_RULE SKOLEM_CONV)

Definition bnd_def:
  bnd : 'b1 ordinal = ordOf (univ(:num + 'b1))
End

Theorem omega_le_bnd[local]:
  ω ≤ bnd : 'b1 ordinal
Proof
  simp[lt_omega, preds_nat] >> gen_tac >>
  disch_then (mp_tac o Q.AP_TERM ‘preds’) >>
  REWRITE_TAC[preds_nat, bnd_def] >> disch_then (assume_tac o SYM) >>
  qspec_then ‘univ(:num + 'b1)’ mp_tac ordOf_def >> ASM_REWRITE_TAC[] >>
  ‘IMAGE ($& : num -> 'b1 ordinal) (count m) ≺ univ(:num + 'b1)’
    suffices_by metis_tac[cardlt_lenoteq] >>
  resolve_then (Pos hd) irule (iffLR FINITE_CARD_LT) CARD_LTE_TRANS >>
  simp[disjUNION_UNIV, CARD_LE_ADDR]
QED

Theorem Fset2_cle_bnd:
  ∀x:('a1,'a2,'b1) F. Fset2 x ≼ preds (bnd : 'b1 ordinal)
Proof
  strip_tac >>
  ‘Fset2 x ≈ Fset2 x’ by REWRITE_TAC [cardeq_REFL] >>
  ‘preds (bnd:'b1 ordinal) ≈ univ(:num + 'b1)’
    by REWRITE_TAC[bnd_def,ordOf_def] >>
  dxrule_then (dxrule_then irule) (iffRL CARD_LE_CONG) >>
  MATCH_ACCEPT_TAC (GEN_ALL Fset_bounded)
QED

Theorem KK_EQ_MINSET =
        KKbnd_EQ_minset |> INST_TYPE [“:γ” |-> “:'b1”]
                        |> Q.INST [‘bd’ |-> ‘bnd’]
                        |> C MATCH_MP (CONJ omega_le_bnd Fset2_cle_bnd)

Theorem inst_bound =
        alg_cardinality_bound |> Q.INST [‘bd’ |-> ‘bnd’]
                              |> REWRITE_RULE [omega_le_bnd, KK_EQ_MINSET,
                                               Fset2_cle_bnd, Fset_exists]

Type algty0[pp] = (#1 $ dom_rng $ type_of $ rand $ concl inst_bound)

Theorem copy_alg_back:
  (A:'a2 set) ≼ (B:'c2 set) ∧ alg (A, s : ('a1,'a2,'b1)F -> 'a2) ⇒
  ∃(B0:'c2 set) (s':('a1,'c2,'b1)F -> 'c2) h j.
    hom h (B0,s') (A,s) ∧ hom j (A,s) (B0,s') ∧
    (∀a. a ∈ A ⇒ h (j a) = a) ∧ (∀b. b ∈ B0 ⇒ j (h b) = b)
Proof
  simp_tac bool_ss [cardleq_def] >> strip_tac >> rename [‘INJ h0 A B’] >>
  qexistsl_tac [‘IMAGE h0 A’, ‘λbv. h0 $ s $ Fmap (LINV h0 A) bv’,
                ‘LINV h0 A’, ‘h0’] >>
  asm_simp_tac (bool_ss ++ CONJ_ss)[hom_def, PULL_EXISTS, IN_IMAGE] >>
  drule_then assume_tac LINV_DEF >> rpt strip_tac >> bsimp []
  >- (qpat_x_assum ‘alg _’ mp_tac >>
      bsimp [alg_def, Fin_def, SUBSET_DEF, IN_UNIV, IN_IMAGE] >>
      CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >> rpt strip_tac >>
      irule_at Any EQ_REFL >> first_assum irule >>
      bsimp [FmapIMAGE, PULL_EXISTS, IN_IMAGE] >>
      rpt strip_tac >> first_assum drule >>
      bsimp[PULL_EXISTS])
  >- (‘s (Fmap (LINV h0 A) bv) ∈ A’
        by (qpat_x_assum ‘alg _’ mp_tac >>
            bsimp [alg_def, Fin_def, SUBSET_DEF, IN_UNIV, IN_IMAGE] >>
            CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >> rpt strip_tac >>
            first_assum irule >>
            bsimp [FmapIMAGE, IN_IMAGE, PULL_EXISTS] >>
            qpat_x_assum ‘bv ∈ Fin _’ mp_tac >>
            bsimp [Fin_def, SUBSET_UNIV] >>
            CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
            bsimp [SUBSET_DEF, PULL_EXISTS, IN_IMAGE] >>
            rpt strip_tac >>
            first_assum drule >> bsimp [PULL_EXISTS]) >>
      bsimp [])
  >- (irule_at Any EQ_REFL >> first_assum ACCEPT_TAC)
  >- (bsimp [FmapO', I_o_ID] >>
      rename [‘av ∈ Fin A’] >>
      ‘Fmap (LINV h0 A o h0) av = Fmap I av’
        suffices_by simp[FmapID, FmapO'] >>
      irule FmapCONG >>
      qpat_x_assum ‘_ ∈ Fin _’ mp_tac >>
      bsimp [Fin_def, SUBSET_UNIV, o_THM, I_THM] >>
      CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
      bsimp [SUBSET_DEF, PULL_EXISTS])
QED

Type algty[pp] = “:('a1,('a1,'b1) algty0,'b1)idx -> ('a1,'b1) algty0”
Definition Cons_def:
  Cons = SND $ bigprod : ('a1, ('a1,'b1) algty,'b1)alg
End

Definition IAlg_def:
  IAlg = minset Cons
End

Theorem IAlg_isalg:
  alg (IAlg, Cons)
Proof
  REWRITE_TAC [IAlg_def, minset_is_alg]
QED

Theorem hom_arbification:
  hom h (A,s) (B,t) ⇒
  ∃j. hom j (A,s) (B,t) ∧ ∀x. x ∉ A ⇒ j x = ARB
Proof
  strip_tac >>
  qexists_tac ‘λx. if x ∈ A then h x else ARB’ >> simp_tac bool_ss [] >>
  pop_assum mp_tac >> simp_tac bool_ss [hom_def, Fin_def, alg_def] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [SUBSET_UNIV] >> rpt strip_tac >>
  RULE_ASSUM_TAC GSYM >> bsimp [] >>
  AP_TERM_TAC >> irule FmapCONG >> bsimp [] >>
  qpat_x_assum ‘_ ⊆ _’ mp_tac >> simp_tac bool_ss [SUBSET_DEF]
QED

val cons_t = “Cons : ('a1,('a1,'b1)algty,'b1) F -> ('a1,'b1) algty”

Theorem initiality0:
  ∀(t:('a1,'a2,'b1)F -> 'a2) (G:'a2 set).
    alg(G,t) ⇒
    ∃!h. hom h (IAlg,^cons_t) (G,t) ∧ ∀x. x ∉ IAlg ⇒ h x = ARB
Proof
  rpt strip_tac >> simp_tac bool_ss [EXISTS_UNIQUE_THM] >> reverse conj_tac
  >- (rpt strip_tac >> REWRITE_TAC[FUN_EQ_THM] >> qx_gen_tac ‘a’ >>
      Cases_on ‘a ∈ IAlg’ >> bsimp[] >>
      RULE_ASSUM_TAC (REWRITE_RULE [IAlg_def]) >>
      dxrule_all minsub_gives_unique_homs >> simp_tac bool_ss []) >>
  irule hom_arbification >>
  simp[IAlg_def] >>
  ‘hom I (minset ^cons_t, ^cons_t) (FST bigprod,^cons_t)’
    by (irule minsub_I_subalg >> REWRITE_TAC[bigprod_isalg, Cons_def, PAIR]) >>
  dxrule_then (irule_at (Pos hd)) homs_compose >>
  ‘hom I (minset t, t) (G,t)’ by (irule minsub_I_subalg >> metis_tac[]) >>
  pop_assum $ C (resolve_then (Pos last) (irule_at (Pos hd))) homs_compose >>
  ‘alg (minset t, t)’ by REWRITE_TAC [minset_is_alg] >>
  resolve_then (Pos hd) (drule_then strip_assume_tac)
               inst_bound copy_alg_back >>
  rename [‘hom h (A0,s) (minset t, t)’] >>
  first_assum $ C (resolve_then (Pos last) (irule_at (Pos hd))) homs_compose >>
  REWRITE_TAC[PAIR,Cons_def] >>
  irule_at (Pos hd) bigprod_proj >> qpat_x_assum ‘hom _ (A0,s) _’ mp_tac >>
  simp_tac bool_ss [hom_def]
QED

Theorem inhabited:
  ∃w. IAlg w
Proof
  ‘alg (IAlg, Cons)’ by REWRITE_TAC[IAlg_isalg] >>
  drule alg_nonempty >> simp_tac bool_ss [EXTENSION, IN_DEF, EMPTY_DEF]
QED

Theorem alg_Fin:
  alg (A,s) ⇒ alg (Fin A : ('a1,'a2,'b1) F set, Fmap s)
Proof
  strip_tac >>
  simp_tac bool_ss [alg_def, Fin_def, SUBSET_DEF, PULL_EXISTS] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [IN_UNIV, FmapIMAGE, IN_IMAGE, PULL_EXISTS] >>
  rpt strip_tac >>
  rename [‘s vf ∈ A’, ‘vf ∈ Fset2 vff’] >>
  first_assum $ drule_then assume_tac >>
  irule (iffLR $ BRULE [Fin_def, PULL_EXISTS] alg_def) >>
  ASM_REWRITE_TAC[] >> CONV_TAC pred_setLib.SET_SPEC_CONV >>
  ASM_REWRITE_TAC[SUBSET_DEF, IN_UNIV]
QED

Definition arbify_def:
  arbify A f x = if x ∈ A then f x else ARB
End

Theorem IN_Fin_chained:
  x ∈ Fin A ∧ y ∈ Fset2 x ⇒ y ∈ A
Proof
  simp_tac bool_ss [Fin_def] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [SUBSET_DEF]
QED

Theorem hom_arbify:
  hom (arbify A f) (A,s : ('a1,'a2,'b1)F -> 'a2)
                   (B,t : ('a1,'c2,'b1)F -> 'c2) ⇔
    hom f (A,s) (B,t)
Proof
  simp_tac bool_ss [hom_def, arbify_def] >> Cases_on ‘alg (A,s)’ >>
  bsimp [] >>
  drule_then assume_tac (iffLR alg_def) >> bsimp [] >>
  iff_tac >> rpt strip_tac >> bsimp [] >>
  RULE_ASSUM_TAC GSYM >> bsimp [] >> AP_TERM_TAC >>
  irule FmapCONG >> drule_then assume_tac IN_Fin_chained >>
  bsimp [arbify_def]
QED

Theorem iso0:
  BIJ ^cons_t (Fin IAlg) IAlg
Proof
  ‘alg (IAlg, ^cons_t)’ by REWRITE_TAC[IAlg_isalg] >>
  drule_then assume_tac alg_Fin >>
  drule_then mp_tac initiality0 >>
  simp_tac bool_ss [EXISTS_UNIQUE_ALT] >> strip_tac >>
  rename[‘hom _ (IAlg,Cons) _ ∧ _ ⇔ H = _’] >>
  ‘hom H (IAlg,^cons_t) (Fin IAlg, Fmap Cons)’
    by (pop_assum (qspec_then ‘H’ mp_tac) >> simp_tac bool_ss []) >>
  ‘hom Cons (Fin IAlg, Fmap Cons) (IAlg,^cons_t)’
    by (bsimp [hom_def] >>
        bsimp [iffLR alg_def]) >>
  rev_drule_then (drule_then assume_tac) homs_compose >>
  rev_drule_then (strip_assume_tac o SRULE [EXISTS_UNIQUE_ALT]) initiality0 >>
  ‘hom (arbify IAlg (^cons_t o H)) (IAlg,Cons) (IAlg,Cons)’
    by ASM_REWRITE_TAC[hom_arbify] >>
  ‘∀x. x ∉ IAlg ⇒ arbify IAlg (Cons o H) x = ARB’
    by simp_tac bool_ss [arbify_def] >>
  ‘hom (arbify IAlg I) (IAlg,^cons_t) (IAlg,Cons)’
    by (bsimp [hom_arbify, hom_def, FmapID, I_THM])>>
  ‘∀x. x ∉ (IAlg:('a1,'b1) algty -> bool) ⇒ arbify IAlg I x = ARB’
    by simp_tac bool_ss [arbify_def] >>
  ‘arbify IAlg (^cons_t o H) = arbify IAlg I’ by metis_tac[] >>
  bsimp[BIJ_IFF_INV] >> conj_tac
  >- bsimp [iffLR alg_def] >>
  qexists_tac ‘H’ >> conj_tac
  >- (qpat_x_assum ‘hom H _ _’ mp_tac >> bsimp [hom_def]) >>
  conj_asm2_tac
  >- (qpat_x_assum ‘hom H _ _’ mp_tac >>
      bsimp [hom_def, FmapO', I_o_ID,
                            o_THM] >> strip_tac >>
      qx_gen_tac ‘a’ >> strip_tac >>
      ‘H (Cons a) = Fmap (Cons o H) a’ by bsimp [] >>
      pop_assum SUBST1_TAC >>
      ‘Fmap (Cons o H) a = Fmap I a’ suffices_by simp_tac bool_ss [FmapID']>>
      irule FmapCONG >> drule_then assume_tac IN_Fin_chained >>
      bsimp [o_THM, I_THM]) >>
  pop_assum mp_tac >>
  simp_tac bool_ss [Once FUN_EQ_THM, arbify_def, I_THM,
                    o_THM] >> metis_tac[]
QED

val itype = newtypeTools.rich_new_type{
  tyname = "nty", exthm = inhabited,
  ABS = "nty_ABS", REP = "nty_REP"
  }

Definition NCONS_def:
  NCONS (x : ('a1, ('a1,'b1)nty, 'b1)F) = nty_ABS $ Cons $ Fmap nty_REP x
End

Theorem NCONS_isalg:
  alg (UNIV, NCONS)
Proof
  simp[alg_def]
QED

Theorem hom_nty_ABS:
  hom nty_ABS (IAlg,Cons) (UNIV,NCONS)
Proof
  simp_tac bool_ss [hom_def, NCONS_isalg, IAlg_isalg, IN_UNIV] >>
  simp_tac bool_ss [NCONS_def, FmapO', I_o_ID] >>
  rpt strip_tac >> rpt AP_TERM_TAC >>
  CONV_TAC (RHS_CONV $ REWR_CONV $ GSYM FmapID') >>
  irule FmapCONG >>
  simp_tac bool_ss [I_THM, o_THM] >> rpt strip_tac >>
  irule $ #repabs_pseudo_id itype >> drule_all IN_Fin_chained >>
  simp_tac bool_ss [IN_DEF]
QED

Theorem hom_nty_REP:
  hom nty_REP (UNIV, NCONS) (IAlg:('a1,'b1)algty -> bool, Cons)
Proof
  simp_tac bool_ss [hom_def, NCONS_isalg, IAlg_isalg] >> conj_tac
  >- simp_tac bool_ss [IN_DEF, # termP_term_REP itype] >>
  simp_tac bool_ss [NCONS_def] >> rpt strip_tac >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  irule (#repabs_pseudo_id itype) >>
  ‘alg (IAlg : ('a1,'b1) algty set,Cons)’ by simp[IAlg_isalg] >>
  drule_then assume_tac (iffLR alg_def) >>
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] >> pop_assum irule >>
  simp_tac bool_ss [Fin_def] >> CONV_TAC pred_setLib.SET_SPEC_CONV >>
  simp_tac bool_ss [FmapIMAGE, PULL_EXISTS, IN_IMAGE, SUBSET_DEF, IN_UNIV] >>
  simp_tac bool_ss [IN_DEF, #termP_term_REP itype]
QED

Theorem initiality_hom:
  alg(B,t:('a1,'a2,'b1) F -> 'a2) ⇒ ∃!h. hom h (UNIV,NCONS) (B,t)
Proof
  strip_tac >>
  simp_tac bool_ss [EXISTS_UNIQUE_THM] >>
  drule_then (strip_assume_tac o BRULE [EXISTS_UNIQUE_ALT])
             initiality0 >>
  rename [‘hom _ _ _ ∧ _ ⇔ H = _’] >>
  ‘hom H (IAlg,^cons_t) (B,t)’ by metis_tac[] >> conj_tac
  >- metis_tac[homs_compose, hom_nty_REP] >>
  qx_genl_tac [‘h1’, ‘h2’] >> strip_tac >>
  ‘hom (arbify IAlg (h1 o nty_ABS)) (IAlg,^cons_t) (B,t) ∧
   hom (arbify IAlg (h2 o nty_ABS)) (IAlg,^cons_t) (B,t)’
    by (simp_tac bool_ss[hom_arbify] >> metis_tac[homs_compose, hom_nty_ABS]) >>
  ‘arbify IAlg (h1 o nty_ABS) = arbify IAlg (h2 o nty_ABS)’
    by metis_tac[arbify_def] >>
  pop_assum mp_tac >> ONCE_REWRITE_TAC [FUN_EQ_THM] >>
  simp_tac bool_ss [arbify_def] >>
  strip_tac >> qx_gen_tac ‘a’ >>
  qspec_then ‘a’ (SUBST1_TAC o SYM) (#absrep_id itype) >>
  pop_assum $ qspec_then ‘nty_REP a’ mp_tac >>
  simp_tac bool_ss [#termP_term_REP itype, IN_DEF, o_THM]
QED

Theorem initiality =
        initiality_hom |> Q.INST [‘B’ |-> ‘UNIV’]
                       |> BRULE [hom_def, alg_def, Fin_def,
                                 SUBSET_UNIV, IN_UNIV, GSPEC_T]
                       |> GSYM |> Q.GEN ‘t’

(* map for other type variable *)
Overload Nmap[local] =
  “λ(f1:'a1 -> 'c1).
     SUM_MAP f1 ($o (OPTION_MAP (f1 ## I)))
    : ('a1,'a2,'b1) F -> ('c1,'a2,'b1) F”

Theorem MAP_exists =
        initiality |> INST_TYPE [“:'a2” |-> “:('c1,'b1) nty” ]
                   |> Q.SPEC ‘NCONS o Nmap (f:'a1 -> 'c1)’
                   |> BRULE [oprime_ify (#mapO sum_data),
                             #mapO fun_data, #mapO opt_data,
                             #mapO pair_data, I_o_ID,
                             combinTheory.o_THM]
                   |> Q.GEN ‘f’
                   |> BRULE [UNIQUE_SKOLEM]
                   |> CONV_RULE (RENAME_VARS_CONV ["MAP"])
                   |> BRULE[EXISTS_UNIQUE_THM] |> cj 1

val MAP_def = new_specification("MAP_def", ["MAP"], MAP_exists);

Theorem minset_Cons = SYM IAlg_def

Theorem ALL_Ialg:
  (∀ia. ia ∈ IAlg ⇒ P ia) ⇔ (∀n. P (nty_REP n))
Proof
  simp_tac bool_ss [EQ_IMP_THM, IN_DEF] >> rpt strip_tac
  >- (first_x_assum irule >>
      simp_tac bool_ss [#termP_term_REP itype]) >>
  first_x_assum $ qspec_then ‘nty_ABS ia’ mp_tac >>
  bsimp [#repabs_pseudo_id itype]
QED

Theorem ALL_Ialgv:
  (∀av. Fset2 av ⊆ IAlg ⇒ P av) ⇔
  (∀n. P (Fmap nty_REP n))
Proof
  simp_tac bool_ss [EQ_IMP_THM] >> rpt strip_tac
  >- (pop_assum irule >>
      simp_tac bool_ss [FmapIMAGE, SUBSET_DEF, PULL_EXISTS, IN_IMAGE] >>
      simp_tac bool_ss [IN_DEF, #termP_term_REP itype]) >>
  first_x_assum $ qspec_then ‘Fmap nty_ABS av’ mp_tac >>
  simp_tac bool_ss [FmapO', o_THM, I_o_ID] >>
  ‘Fmap (nty_REP o nty_ABS) av = av’ suffices_by simp_tac bool_ss[] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM FmapID'))) >>
  irule FmapCONG >> simp_tac bool_ss [o_THM, I_THM] >> rpt strip_tac >>
  irule $ #repabs_pseudo_id itype >>
  metis_tac[SUBSET_DEF, IN_DEF]
QED

Theorem IN_Fset2:
  (∀y. y ∈ Fset2 x ⇒ Q (nty_ABS y)) ⇔ x ∈ Fin (Q o nty_ABS)
Proof
  simp_tac bool_ss [Fin_def, SUBSET_DEF, IN_UNIV, IN_GSPEC_IFF] >>
  simp_tac bool_ss [IN_DEF, o_THM]
QED

Theorem abs_o_rep:
  nty_ABS o nty_REP = I
Proof
  simp_tac bool_ss [FUN_EQ_THM, #absrep_id itype, I_THM, o_THM]
QED

Theorem Cons_NCONS:
  Fset2 x ⊆ IAlg ⇒
  Cons x = nty_REP (NCONS (Fmap nty_ABS x))
Proof
  simp_tac bool_ss [NCONS_def, FmapO', I_o_ID] >> strip_tac >>
  ‘Fmap (nty_REP o nty_ABS) x = x’
    by (irule Fmap_eq_id >>
        pop_assum mp_tac >>
        simp_tac bool_ss [SUBSET_DEF, #repabs_pseudo_id itype, o_THM, IN_DEF,
                          I_THM]) >>
  bsimp [] >>
  ‘Cons x ∈ IAlg’ suffices_by
    simp_tac bool_ss [IN_DEF, #repabs_pseudo_id itype] >>
  irule (iffLR alg_def) >>
  bsimp [IAlg_isalg, Fin_def, IN_GSPEC_IFF, SUBSET_UNIV]
QED


Theorem Fset2_applied:
  Fset2 x v ⇔ v ∈ Fset2 x
Proof
  bsimp [IN_DEF]
QED

Theorem IND =
        minset_ind |> Q.GEN ‘s’
                   |> Q.ISPEC ‘Cons’
                   |> BRULE [minset_Cons]
                   |> Q.SPEC ‘λia. Q (nty_ABS ia)’
                   |> BRULE[ALL_Ialg, #absrep_id itype, IN_Fset2, Cons_NCONS]
                   |> BRULE[GSYM AND_IMP_INTRO, ALL_Ialgv, FmapO', Fin_def,
                            FmapIMAGE, abs_o_rep, FmapID, IN_GSPEC_IFF,
                            SUBSET_UNIV, I_o_ID, I_THM]
                   |> BRULE[SUBSET_DEF, PULL_EXISTS, IN_IMAGE, #absrep_id itype]
                   |> BRULE [IN_DEF, o_THM, #absrep_id itype]
                   |> BRULE[Fset2_applied]

Theorem NCONS_comp:
  NCONS = nty_ABS o Cons o Fmap nty_REP
Proof
  bsimp[FUN_EQ_THM, NCONS_def, o_THM]
QED

Theorem iso:
  BIJ NCONS (Fin 𝕌(:('a1,'b1) nty)) 𝕌(:('a1,'b1) nty)
Proof
  bsimp[NCONS_comp] >> irule BIJ_COMPOSE >> qexists_tac ‘IAlg’ >>
  reverse conj_tac
  >- (bsimp[BIJ_IFF_INV, IN_UNIV] >> qexists_tac ‘nty_REP’ >>
      bsimp[#repabs_pseudo_id itype, #absrep_id itype, IN_DEF,
            #termP_term_REP itype]) >>
  irule BIJ_COMPOSE >> irule_at Any iso0 >>
  bsimp[BIJ_IFF_INV] >> conj_tac
  >- (bsimp[Fin_def, FmapIMAGE, SUBSET_DEF, PULL_EXISTS, IN_GSPEC_IFF,
            IN_UNIV, IN_IMAGE] >>
      bsimp[#termP_term_REP itype, IN_DEF]) >>
  qexists_tac ‘Fmap nty_ABS’ >>
  bsimp[FmapO', abs_o_rep, FmapID, funMap_ID, I_THM] >>
  conj_tac >- bsimp[Fin_def, IN_GSPEC_IFF, SUBSET_UNIV] >>
  rpt strip_tac >> irule Fmap_eq_id >> bsimp[I_THM, o_THM] >>
  drule_then assume_tac IN_Fin_chained >>
  rpt strip_tac >> irule (#repabs_pseudo_id itype) >>
  first_x_assum drule >> bsimp[IN_DEF]
QED

Theorem Fin_UNIV:
  Fin UNIV = UNIV
Proof
  bsimp[EXTENSION, Fin_def, IN_GSPEC_IFF, SUBSET_UNIV, IN_UNIV]
QED

Theorem NCONS_11:
  NCONS (x:('a1,('a1,'b1)nty,'b1)F) = NCONS y ⇔ x = y
Proof
  mp_tac iso >> bsimp[BIJ_DEF, Fin_UNIV, INJ_IFF, IN_UNIV]
QED

val DEST_def = new_specification("DEST_def", ["DEST"],
                                 iso |> SRULE [BIJ_IFF_INV, Fin_UNIV])

Theorem MAP_ID:
  MAP I = I
Proof
  REWRITE_TAC[FUN_EQ_THM, I_THM] >>
  ho_match_mp_tac IND >> bsimp[MAP_def, NCONS_11] >> rpt strip_tac >>
  irule Fmap_eq_id >> bsimp[I_THM]
QED

Theorem MAP_COMPOSE:
  ∀n. MAP f (MAP g n) = MAP (f o g) n
Proof
  ho_match_mp_tac IND >>
  bsimp[MAP_def, NCONS_11, oprime_ify (#mapO sum_data),
        #mapO fun_data, #mapO pair_data, #mapO opt_data] >>
  rpt strip_tac >>
  irule (#mapCONG sum_data) >> bsimp[o_THM] >> rpt strip_tac >>
  irule (#mapCONG fun_data) >> bsimp[o_THM] >> rpt strip_tac >>
  irule (#mapCONG opt_data) >> bsimp[o_THM] >> rpt strip_tac >>
  irule (#mapCONG pair_data) >> bsimp[o_THM] >> rpt strip_tac >>
  first_x_assum irule >>
  bsimp[IN_BIGUNION, IN_UNION, IN_IMAGE, PULL_EXISTS, K_THM, NOT_IN_EMPTY,
        IN_equal] >>
  rpt $ first_assum $ irule_at Any
QED

Theorem MAPO:
  MAP (f1:'c1 -> 'd1) o MAP (g1:'a1 -> 'c1) = MAP (f1 o g1)
Proof
  REWRITE_TAC[MAP_COMPOSE, FUN_EQ_THM, o_THM]
QED

Theorem BIMG_EQ:
  BIMG $= A = A
Proof
  simp[Once EXTENSION, PULL_EXISTS, IN_equal]
QED

val SET_def = new_specification (
  "SET_def", ["SET"],
  initiality |> Q.ISPEC ‘λv. Fset1 v ∪ BIGUNION (Fset2 v)’
             |> BRULE[EXISTS_UNIQUE_THM, FmapIMAGE] |> cj 1);

Theorem BIMG_CONG:
  A1 = A2 ∧ (∀x. x ∈ A2 ⇒ f1 x = f2 x) ⇒ BIMG f1 A1 = BIMG f2 A2
Proof
  rw[] >>
  bsimp[Once EXTENSION, IN_BIGUNION, IN_IMAGE, PULL_EXISTS, SF CONJ_ss]
QED

Theorem Fmap_SUM_MAP:
  Fmap f (SUM_MAP g h s) = SUM_MAP g ($o (OPTION_MAP (I ## f)) o h) s
Proof
  simp[oprime_ify (#mapO sum_data)]
QED

Theorem eq1_EQ_eq1:
  (=) x = (=) y ⇔ x = y
Proof
  simp[FUN_EQ_THM] >> iff_tac >> simp[]
QED

Theorem SET_MAP:
  ∀n. SET (MAP f n) = IMAGE f (SET n)
Proof
  ho_match_mp_tac IND >>
  bsimp[SET_def, MAP_def, Fmap_SUM_MAP, #mapO fun_data, #mapO opt_data, #mapO pair_data]>>
  bsimp(FmapIMAGE :: IMAGE_BIGUNION :: IMAGE_IMAGE :: IMAGE_o_equal ::
        o_ABS_R :: o_ABS_L :: I_o_ID :: K_o_THM :: IMAGE_EMPTY :: BIMG_K0 ::
        UNION_EMPTY :: IN_BIGUNION :: IN_UNION :: IN_IMAGE :: PULL_EXISTS ::
        IN_equal ::
        IMAGE_UNION :: #mapIMAGE sum_data @ #mapIMAGE fun_data @
        #mapIMAGE opt_data @ #mapIMAGE pair_data) >>
  rpt strip_tac >> cong_tac (SOME 2) >>
  rpt (irule BIMG_CONG >> rpt strip_tac >> bsimp[]) >>
  bsimp[o_THM, eq1_EQ_eq1] >> first_x_assum irule >>
  bsimp[K_THM, NOT_IN_EMPTY] >> rpt $ first_assum $ irule_at Any
QED

Theorem MAP_CONG:
  ∀n. (∀a. a ∈ SET n ⇒ f a = g a) ⇒ MAP f n = MAP g n
Proof
  ho_match_mp_tac IND >>
  bsimp[MAP_def, SET_def, PULL_EXISTS, NCONS_11] >> rpt strip_tac >>
  irule (#mapCONG sum_data) >> rw[]
  >- (first_x_assum irule>>
      bsimp(IN_UNION :: BIMG_EQUAL :: IMAGE_I :: #mapIMAGE sum_data))
  >- (irule (#mapCONG fun_data) >> rpt strip_tac >>
      irule (#mapCONG opt_data) >> rpt strip_tac >>
      irule (#mapCONG pair_data) >> rpt strip_tac >>
      first_x_assum irule >> rpt strip_tac >>
      bsimp(IN_UNION :: BIMG_EQUAL :: IMAGE_I :: BIMG_K0 :: IN_BIGUNION ::
            IN_IMAGE :: PULL_EXISTS :: K_THM :: NOT_IN_EMPTY ::
            IN_equal ::
            #mapIMAGE sum_data @ #mapIMAGE fun_data @
            #mapIMAGE opt_data @ #mapIMAGE pair_data)
      >- metis_tac[]
      >- (first_x_assum irule >> rpt strip_tac >>
          bsimp(IN_UNION :: BIMG_EQUAL :: IMAGE_I :: BIMG_K0 :: IN_BIGUNION ::
                IN_IMAGE :: PULL_EXISTS :: K_THM :: NOT_IN_EMPTY ::
                IN_equal ::
                #mapIMAGE sum_data @ #mapIMAGE fun_data @
                #mapIMAGE opt_data @ #mapIMAGE pair_data) >>
          metis_tac[]) >>
      metis_tac[])
QED

Theorem FORALL_SUMALG:
  (∀t : α + β -> γ. P t) ⇔
  (∀(t1: α -> γ) (t2 : β -> γ). P (λs. case s of INL x => t1 x
                                              | INR y => t2 y))
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  first_x_assum $ qspecl_then [‘t o INL’, ‘t o INR’] mp_tac>>
  qmatch_abbrev_tac ‘P x ⇒ P y’ >> ‘x = y’ suffices_by simp[] >>
  simp[Abbr‘x’, Abbr‘y’, FUN_EQ_THM, sumTheory.FORALL_SUM]
QED

Theorem FORALL_PAIRALG:
  (∀t: α # β -> γ. P t) ⇔ (∀t: α -> β -> γ. P (UNCURRY t))
Proof
  simp[EQ_IMP_THM] >> disch_then $ qspec_then ‘CURRY f’ (mp_tac o Q.GEN ‘f’) >>
  simp[UNCURRY_CURRY_THM]
QED

Definition C1_def:
  C1 x = NCONS (INL x)
End

Definition C2_def:
  C2 f = NCONS (INR f)
End

Theorem better_initiality =
        initiality |> SRULE [sumTheory.FORALL_SUM, FORALL_SUMALG]
                   |> SRULE [FORALL_PROD, FORALL_PAIRALG, GSYM C1_def,
                             GSYM C2_def]

Theorem lem:
  v ∈ UNCURRY f x ⇔ ∃a b. x = (a,b) ∧ v ∈ f a b
Proof
  Cases_on ‘x’ >> simp[]
QED

Theorem better_ind =
        IND |> SRULE [sumTheory.FORALL_SUM, PULL_EXISTS, IN_equal,
                      FORALL_PROD, lem,
                      GSYM C1_def, GSYM C2_def]

Theorem SET_C1:
  SET (C1 b) = {b}
Proof
  simp[C1_def, SET_def, Once EXTENSION, IN_equal]
QED

Theorem SET_C2:
  SET (C2 f) =
  { a | ∃x opt p. f x = opt ∧ p ∈ optSET opt ∧
                  (a ∈ setFST p ∨ ∃n. n ∈ setSND p ∧ a ∈ SET n) }
Proof
  bsimp[C2_def, SET_def] >>
  ONCE_REWRITE_TAC[EXTENSION] >>
  bsimp(IMAGE_I :: sumTheory.setL_def :: sumTheory.setR_def :: IN_GSPEC_IFF ::
        BIMG_K0 :: IN_UNION :: IN_BIGUNION :: PULL_EXISTS :: IN_IMAGE ::
        IN_equal :: NOT_IN_EMPTY :: IN_ABS ::
        #mapIMAGE sum_data @ #mapIMAGE fun_data @ #mapIMAGE opt_data @
        #mapIMAGE pair_data) >>
  bsimp[C_THM, IN_IMAGE, PULL_EXISTS, IN_UNIV] >> metis_tac[]
QED

(* gives bnd, but seems non-trivial to get automatically *)
Theorem SET_bounded:
  ∀n. SET (n:('a,'b)nty) ≼ univ(:num + 'b)
Proof
  ho_match_mp_tac IND >> rpt strip_tac >>
  bsimp[SET_def] >> irule UNION_CARDLE >> rpt strip_tac >~
  [‘FINITE univ(:num + 'b)’]
  >- (pop_assum mp_tac >>
      bsimp[disjUNION_UNIV, CARD_ADD_FINITE_EQ, INFINITE_NUM_UNIV]) >~
  [‘Fset1 n ≼ UNIV’]
  >- bsimp[Fset1_bounded] >>

  irule CARD_BIGUNION >> rpt conj_tac >~
  [‘INFINITE _ (* g *)’]
  >- bsimp[disjUNION_UNIV, CARD_ADD_FINITE_EQ, INFINITE_NUM_UNIV] >~
  [‘IMAGE SET _ ≼ _ (* g *)’]
  >- (irule IMAGE_cardleq_rwt >> bsimp[Fset_bounded]) >>
  bsimp[IN_IMAGE, PULL_EXISTS]
QED

Definition FIN_def:
  FIN A = { x | SET x ⊆ A }
End

val Fin_def = FIN_def

Theorem EXISTS_NCONS:
  (∃x:('a1,'b1) nty. P x) ⇔ ∃fv. P (NCONS fv)
Proof
  metis_tac[DEST_def]
QED

Theorem setL_EQ_EMPTY:
  setL s = {} ⇔ ∃x. s = INR x
Proof
  Cases_on ‘s’ >>
  bsimp[sumTheory.setL_def, EMPTY_DEF, FUN_EQ_THM, sumTheory.sum_distinct] >>
  irule_at Any EQ_REFL
QED

Theorem setR_EQ_EMPTY:
  setR s = {} ⇔ ∃x. s = INL x
Proof
  Cases_on ‘s’ >>
  bsimp[sumTheory.setR_def, EMPTY_DEF, FUN_EQ_THM, sumTheory.sum_distinct] >>
  irule_at Any EQ_REFL
QED

Theorem IMAGE_EQ_EQ0:
  IMAGE $= A = {∅} ⇔ F
Proof
  bsimp[Once EXTENSION, IN_IMAGE, IN_INSERT, NOT_IN_EMPTY, IN_GSPEC_IFF] >>
  bsimp [EQ_SING] >> bsimp[INSERT_applied, NOT_IN_EMPTY] >>
  qexists_tac ‘{}’ >>
  bsimp[PULL_EXISTS, NOT_EMPTY_INSERT]
QED

Theorem IMAGEf_eq_SING0:
  IMAGE f A = {∅} ⇔ (∀a. a ∈ A ⇒ f a = ∅) ∧ ∃a. a ∈ A
Proof
  simp[Once EXTENSION, SimpLHS] >> simp[] >> iff_tac
  >- (Cases_on ‘A = ∅’ >> simp[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
  metis_tac[]
QED

Theorem optSET_EQ_EMPTY:
  optSET x = ∅ ⇔ x = NONE
Proof
  Cases_on ‘x’ >> simp[bnfPrelimsTheory.optSET_def]
QED

Theorem Fmap_EQ_INR:
  Fmap f x = INR y ⇔ ∃x0. x = INR x0 ∧  OPTION_MAP (I ## f) o x0 = y
Proof
  Cases_on ‘x’ >> simp[]
QED

Theorem ABS_EQ:
  (λx. x = v) = {v}
Proof
  simp[EXTENSION]
QED

Theorem flip_IMAGE_UNIV_NEQ_EMPTY:
  flip IMAGE UNIV f ≠ {}
Proof
  simp[EXTENSION]
QED

Theorem IMAGE_K_UNIV:
  IMAGE (K v) UNIV = {v}
Proof
  simp[EXTENSION]
QED

(* blergh *)
Theorem Fwitness:
  ∃x:('a1,'b1) nty. SET x = {}
Proof
  qexists ‘C2 (K NONE)’ >>
  bsimp[SET_C2, optSET_def, K_THM, NOT_IN_EMPTY, GSPEC_F]
QED

Theorem nonempty:
  FIN ∅ ≠ ∅
Proof
  simp_tac bool_ss [Once EXTENSION, Fin_def, IN_GSPEC_IFF, SUBSET_EMPTY,
                    NOT_IN_EMPTY] >>
  MATCH_ACCEPT_TAC Fwitness
QED

Type G[pp] = “:('a1,'b1) nty + ('a1,'b1)nty # 'a1”

val summap = #map sum_data |> inst [a1 |-> “:('a1,'b1) nty”,
                                    a2 |-> “:('a1,'b1) nty # 'a1”,
                                    c1 |-> “:('c1,'b1) nty”,
                                    c2 |-> “:('c1,'b1) nty # 'c1”]
val pairmap = #map pair_data |> inst [a1 |-> “:('a1,'b1) nty”,
                                      a2 |-> “:'a1”,
                                      c1 |-> “:('c1,'b1) nty”,
                                      c2 |-> “:'c1”]

Overload Gmap[local] =
  “λ(f1:'a1 -> 'c1).
     ^summap  (MAP f1) (^pairmap (MAP f1) f1)
    : ('a1,'b1) G -> ('c1,'b1) G”

Overload Gset[local] =
  “λx : ('a1,'b1) G .
     BIMG (λf. SET f) (setL (x:('a1,'b1)G)) ∪
     BIMG
       (λp. BIMG (λn. SET n) (setFST p) ∪
            BIMG $= (setSND p))
       (setR x)
   : 'a1 set”

Theorem GmapID:
  Gmap (I:'a1 -> 'a1) = I : ('a1,'b1) G -> ('a1,'b1) G
Proof
  REWRITE_TAC[#mapID sum_data, #mapID fun_data, #mapID pair_data,
              #mapID opt_data, MAP_ID]
QED

Theorem GmapID' = PURE_REWRITE_RULE [FUN_EQ_THM, I_THM] GmapID

Theorem GmapO:
  Gmap (f1 : 'c1 -> 'd1) o Gmap (g1 : 'a1 -> 'c1) =
  Gmap (f1 o g1) : ('a1,'b1) G -> ('d1,'b1) G
Proof
  REWRITE_TAC[#mapO sum_data, #mapO fun_data, #mapO pair_data, #mapO opt_data,
              MAPO]
QED

Theorem GmapO' =
        CONV_RULE (LAND_CONV $ SCONV[o_DEF] THENC
                   SCONV[FUN_EQ_THM])
                  GmapO

Theorem BIMG_UNION:
  BIMG (λp. f p ∪ g p) A = BIMG f A ∪ BIMG g A
Proof
  dsimp[Once EXTENSION, PULL_EXISTS]
QED

Theorem GmapIMAGE:
  Gset (Gmap (f1:'a1 -> 'c1) x) : 'c1 set =
  IMAGE f1 (Gset (x : ('a1,'b1) G))
Proof
  simp_tac bool_ss (#mapIMAGE sum_data @
                    #mapIMAGE fun_data @
                    #mapIMAGE pair_data @
                    #mapIMAGE opt_data @
                    [BIMG_EQUAL, IMAGE_UNION, IMAGE_EMPTY,
                     IMAGE_IMAGE, BIMG_K0, IMAGE_UNION, BIMG_UNION,
                     o_ABS_L, K_o_THM, SET_MAP,
                     UNION_EMPTY, BIMG_IMAGE]) >>
  simp_tac bool_ss [SF ETA_ss]
QED

Theorem GmapCONG:
  (∀a. a ∈ Gset v ⇒ f1 a = g1 a) ⇒
  Gmap (f1:'a1 -> 'c1) v = Gmap g1 v
Proof
  simp_tac bool_ss [IN_UNION, IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_equal,
                    K_THM, NOT_IN_EMPTY, DISJ_IMP_THM,
                    FORALL_AND_THM, SF DNF_ss] >>
  strip_tac >>
  irule (#mapCONG sum_data) >> conj_tac
  >- ((* l branch via SET *)
      rpt strip_tac >> irule MAP_CONG >>
      rpt strip_tac >> first_x_assum drule_all >> REWRITE_TAC[])
  >- ((* r branch via pair *)
      rpt strip_tac >>
      irule (#mapCONG pair_data) >>
      rpt strip_tac
      >- ((* setFST *)
          irule MAP_CONG >>
          rpt strip_tac >> first_x_assum drule_all >> REWRITE_TAC[])
      >- (first_x_assum drule_all >> REWRITE_TAC[]))
QED

Theorem Gmap_eq_id:
  (∀a. a ∈ Gset x ⇒ f a = a)  ⇒ Gmap f x = x
Proof
  strip_tac >> CONV_TAC (RAND_CONV (REWR_CONV $ GSYM GmapID')) >>
  irule GmapCONG >> simp[]
QED

(* ----------------------------------------------------------------------
    functor must also be bounded
   ---------------------------------------------------------------------- *)

Theorem Gset_bounded:
  Gset (v:('a1,'b1)G) ≼ univ(:num + 'b1)
Proof
  irule UNION_CARDLE >>
  REWRITE_TAC[num_INFINITE,disjUNION_UNIV,CARD_ADD_FINITE_EQ,
              BIMG_K0, EMPTY_CARDLEQ, BIMG_EQUAL] >>
  conj_tac
  >- ((* l branch *)
      irule CARD_BIGUNION >>
      simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE, UNIV_NOT_EMPTY,
                        CARD_ADD_FINITE_EQ, SING_CARDLE, disjUNION_EQ_EMPTY] >>
      reverse conj_tac
      >- (irule IMAGE_cardleq_rwt >>
          metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                                 #bndthms sum_data))
      >- (rpt strip_tac >> metis_tac[SET_bounded, disjUNION_UNIV]))
  >- ((* r branch *)
      irule CARD_BIGUNION >>
      simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE, UNIV_NOT_EMPTY,
                        CARD_ADD_FINITE_EQ, SING_CARDLE, disjUNION_EQ_EMPTY] >>
      reverse conj_tac
      >- (irule IMAGE_cardleq_rwt >> (* setR ok *)
          metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                                 #bndthms sum_data))
      >- (rpt strip_tac >>
          irule UNION_CARDLE >>
          REWRITE_TAC[num_INFINITE,disjUNION_UNIV,CARD_ADD_FINITE_EQ,
                      BIMG_K0, EMPTY_CARDLEQ, BIMG_EQUAL] >>
          conj_tac
          >- (irule CARD_BIGUNION >>
              simp_tac bool_ss [IN_IMAGE, PULL_EXISTS, num_INFINITE,
                                UNIV_NOT_EMPTY,
                                CARD_ADD_FINITE_EQ, SING_CARDLE,
                                disjUNION_EQ_EMPTY] >>
              reverse conj_tac
              >- (irule IMAGE_cardleq_rwt >> (* setFST OK *)
                  metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                                         #bndthms pair_data))
              >- (rpt strip_tac >>
                  metis_tac[SET_bounded, disjUNION_UNIV]))
          >- ((* setSND OK *)
              metis_tac(CARD_LE_ADDL :: CARD_LE_ADDR :: cardleq_TRANS ::
                                         #bndthms pair_data))))
QED

(* ----------------------------------------------------------------------
    start constructing algebra-level arguments
   ---------------------------------------------------------------------- *)

Definition GFin_def:
  GFin As = { a : ('a1,'b1) G | Gset a ⊆ As }
End

Theorem setLR_thm:
  setL (INL x) = {x} ∧ setL (INR y) = {} ∧
  setR (INL x) = {} ∧ setR (INR y) = {y}
Proof
  simp_tac bool_ss [sumTheory.setL_def, sumTheory.setR_def, EXTENSION,
                    IN_DEF, INSERT_applied, EMPTY_DEF]
QED

Theorem Gwitness:
  ∃g:('a1,'b1)G. Gset g = {}
Proof
  simp_tac bool_ss [NOT_IN_EMPTY, IN_GSPEC_IFF, SUBSET_EMPTY, EMPTY_UNION,
                    BIMG_UNION, BIGUNION_EQ_EMPTY, IMAGE_EQ_EMPTY] >>
  strip_assume_tac Fwitness >>
  qexists ‘INL x’ >>
  asm_simp_tac bool_ss [setLR_thm, IMAGE_INSERT, IMAGE_EMPTY, EQUAL_SING]
QED

Theorem GFin_witness:
  GFin ∅ ≠ ∅
Proof
  simp_tac bool_ss [Once EXTENSION, GFin_def, IN_GSPEC_IFF, SUBSET_EMPTY,
                    NOT_IN_EMPTY] >>
  MATCH_ACCEPT_TAC Gwitness
QED

Theorem Gset_exists:
  ∃g:('a1,'b1)G. Gset g ≠ ∅
Proof
  simp_tac bool_ss [Once EXTENSION, GFin_def, IN_GSPEC_IFF, SUBSET_EMPTY,
                    NOT_IN_EMPTY, IN_UNION, IN_IMAGE, IN_BIGUNION,
                    PULL_EXISTS, IN_equal, SF DNF_ss] >>
  metis_tac[IN_setR, IN_setSND]
QED

Definition Galg_def:
  Galg (A : 'a1 set, s : ('a1,'b1) G -> 'a1) ⇔ ∀x. x ∈ GFin A ⇒ s x ∈ A
End

Theorem Galg_nonempty:
  Galg(A, s : ('a1,'b1)G -> 'a1) ⇒ A ≠ ∅
Proof
  rpt strip_tac >> gvs[Galg_def] >>
  ‘GFin ∅ : ('a1,'b1) G set = ∅’ by simp[EXTENSION] >>
  gs[GFin_witness]
QED

Definition Gminset_def:
  Gminset (s : ('a1,'b1)G -> 'a1) = BIGINTER { B | Galg(B,s) }
End

Theorem Gminset_is_alg[simp]:
  Galg (Gminset s, s)
Proof
  simp[Gminset_def, Galg_def, GFin_def, SUBSET_BIGINTER]
QED

Theorem IN_Gminset:
  x IN Gminset s ⇔ ∀A. Galg(A,s) ⇒ x IN A
Proof
  simp[Gminset_def]
QED

Definition Ghom_def:
  Ghom h (A,s) (B,t) ⇔
    Galg(A,s) ∧ Galg(B,t) ∧ (∀a. a IN A ⇒ h a IN B) ∧
    ∀af. af ∈ GFin A ⇒ t (Gmap h af) = h (s af)
End

Theorem Ghoms_on_same_domain:
  Ghom h (A,s) (B,t) ∧ (∀a. a ∈ A ⇒ h' a = h a) ⇒ Ghom h' (A,s) (B,t)
Proof
  simp_tac bool_ss [Ghom_def, GFin_def, IN_GSPEC_IFF] >>
  rpt strip_tac >>
  rename [‘Gset af ⊆ A’] >>
  ‘s af ∈ A’ by gs[Galg_def, GFin_def] >> simp[] >>
  ‘Gmap h' af = Gmap h af’ suffices_by simp[] >>
  irule GmapCONG >> simp_tac bool_ss [] >> metis_tac[SUBSET_DEF]
QED

Theorem Ghoms_compose:
  Ghom f (A : 'a1 set, s : ('a1,'b1)G -> 'a1) (B : 'c1 set,t) ∧
  Ghom g (B,t) (C : 'd1 set,u) ⇒
  Ghom (g o f) (A,s) (C,u)
Proof
  simp_tac bool_ss [Ghom_def, SF CONJ_ss, o_THM] >> rpt strip_tac >>
  RULE_ASSUM_TAC GSYM >> bsimp [] >>
  ‘Gmap f af ∈ GFin B’
    by (qpat_x_assum ‘af ∈ GFin _’ mp_tac >>
        simp_tac bool_ss [GFin_def, IN_GSPEC_IFF, GmapIMAGE] >>
        bsimp [SUBSET_DEF, IN_IMAGE, PULL_EXISTS]) >>
  bsimp [GmapO', I_o_ID]
QED

Theorem Gset_SUBSET_Gminset:
  Gset f ⊆ Gminset s ⇒ s f ∈ Gminset s
Proof
  simp_tac bool_ss [IN_Gminset, SUBSET_DEF] >> rpt strip_tac >>
  first_assum (irule o SRULE[Galg_def]) >>
  simp[GFin_def, BIMG_EQUAL, BIMG_K0] >>
  simp[NoAsms, SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
  first_x_assum irule>> ASM_REWRITE_TAC[] >>
  simp[PULL_EXISTS, IN_equal] >> metis_tac[]
QED

Theorem Gminset_ind:
  ∀P. (∀x. Gset x ⊆ Gminset s ∧ (∀y. y ∈ Gset x ⇒ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ Gminset s ⇒ P x
Proof
  gen_tac >>
  ‘∀x. (∀y. y ∈ Gset x ⇒ P y) ⇔ Gset x ⊆ {z | P z}’
    by (gen_tac >> simp_tac bool_ss [SUBSET_DEF]>>
        CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
        REWRITE_TAC[]) >>
  pop_assum (REWRITE_TAC o single) >>
  strip_tac >>
  ‘Gminset s ⊆ {x | P x } INTER Gminset s’ suffices_by simp[SUBSET_DEF, IN_DEF] >>
  simp[Gminset_def, SimpL “$SUBSET”] >> irule BIGINTER_SUBSET >>
  qexists_tac ‘{x | P x} INTER Gminset s’ >> reverse conj_tac
  >- REWRITE_TAC[INTER_SUBSET] >>
  simp_tac bool_ss [Galg_def, GFin_def, SUBSET_DEF, IN_INTER] >>
  CONV_TAC pred_setLib.SET_SPEC_CONV >> GEN_TAC >>
  CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [IN_INTER, IN_UNIV, IMP_CONJ_THM, FORALL_AND_THM] >>
  simp_tac bool_ss [GSYM SUBSET_DEF] >> conj_tac
  >- (strip_tac >>
      CONV_TAC pred_setLib.SET_SPEC_CONV >> first_x_assum irule >>
      ASM_REWRITE_TAC[]) >>
  rename [‘_ ⇒ s x ∈ Gminset s (* g *)’] >>
  Cases_on ‘Gset x ⊆ {x|P x}’ >> ASM_REWRITE_TAC[] >>
  ntac 2 (pop_assum kall_tac) >>
  MATCH_ACCEPT_TAC (GEN_ALL Gset_SUBSET_Gminset)
QED

Theorem Ghom_equals_fmap:
  Ghom h (A,f) (B,g) ∧ Gset x ⊆ A ⇒ h (f x) = g (Gmap h x)
Proof
  simp_tac bool_ss [Ghom_def] >> strip_tac >> sym_tac >>
  first_x_assum irule >>
  simp_tac bool_ss [GFin_def, SUBSET_UNIV] >>
  CONV_TAC pred_setLib.SET_SPEC_CONV >> first_assum ACCEPT_TAC
QED

Theorem minsub_gives_unique_Ghoms:
  Ghom h1 (Gminset s, s) (C,t) ∧ Ghom h2 (Gminset s,s) (C,t) ⇒
  ∀a. a ∈ Gminset s ⇒ h1 a = h2 a
Proof
  strip_tac >> ho_match_mp_tac Gminset_ind >> qx_gen_tac ‘af’ >> strip_tac >>
  rpt (dxrule_then drule Ghom_equals_fmap) >> rpt strip_tac >>
  ASM_REWRITE_TAC[] >> AP_TERM_TAC >>
  irule GmapCONG >> bsimp []
QED

Definition subGalg_def:
  subGalg (A,s) (B,t) ⇔ Galg(A,s) ∧ Galg (B,t) ∧
                       (∀af. af ∈ GFin A ⇒ s af = t af) ∧ A ⊆ B
End

Theorem subalgs_preserve_Ghoms:
  subGalg A1 A2 ∧ Ghom f A2 C ⇒ Ghom f A1 C
Proof
  Cases_on ‘A1’ >> Cases_on ‘A2’ >> Cases_on ‘C’ >>
  simp[Ghom_def,GFin_def,subGalg_def] >> metis_tac[SUBSET_DEF]
QED

Theorem minsub_subGalg:
  Galg(A,s) ⇒ subGalg (Gminset s, s) (A,s)
Proof
  simp[subGalg_def, Gminset_def] >> strip_tac >>
  irule BIGINTER_SUBSET >> simp[] >> metis_tac[SUBSET_REFL]
QED

Theorem minsub_I_subGalg:
  Galg(A,s) ⇒ Ghom I (Gminset s, s) (A,s)
Proof
  strip_tac >> drule minsub_subGalg >>
  simp[Ghom_def, GFin_def, GmapID, subGalg_def, SUBSET_DEF]
QED

Type Galg[local,pp] = “:'a1 set # (('a1,'b1)G -> 'a1)”

val Gidx_tydef as
              {absrep_id, newty, repabs_pseudo_id, termP, termP_exists,
               termP_term_REP, ...} =
  newtypeTools.rich_new_type{
  tyname = "Gidx",
  exthm = prove(“∃i : ('a1,'b1) Galg. Galg i”,
           simp[pairTheory.EXISTS_PROD] >> qexists_tac ‘UNIV’ >>
           simp[Galg_def]),
  ABS = "mkGIx",
  REP = "dGIx"};

Definition Gbigprod_def:
  Gbigprod : (('a1,'b1)Gidx -> 'a1, 'b1) Galg =
  ({ f | ∀i. f i ∈ FST (dGIx i) },
   λfv i. SND (dGIx i) $ Gmap (λf. f i) fv)
End

Theorem Gbigprod_isalg:
  Galg Gbigprod
Proof
  bsimp[Gbigprod_def, Galg_def, FORALL_PROD, GFin_def, IN_GSPEC_IFF] >>
  rpt strip_tac >>
  Cases_on ‘dGIx i’ >> rename [‘dGIx i = (A,s)’] >> bsimp[FST, SND] >>
  ‘Galg(A,s)’ by metis_tac[termP_term_REP] >>
  pop_assum mp_tac >> bsimp[Galg_def] >>
  disch_then irule >>
  bsimp[GFin_def, IN_GSPEC_IFF, SUBSET_UNIV, GmapIMAGE] >>
  bsimp[SUBSET_DEF, PULL_EXISTS, IN_IMAGE] >>
  rpt strip_tac >> drule_all $ iffLR SUBSET_DEF >>
  bsimp[IN_GSPEC_IFF] >> disch_then $ qspec_then ‘i’ mp_tac >>
  bsimp[FST]
QED

Theorem Gbigprod_proj:
  Galg (A,s) ⇒ Ghom (λf. f (mkGIx (A,s))) Gbigprod (A,s)
Proof
  simp[Ghom_def, Gbigprod_def] >> rpt strip_tac
  >- metis_tac[Gbigprod_isalg, Gbigprod_def]
  >- (‘dGIx (mkGIx (A,s)) = (A,s)’ by metis_tac[repabs_pseudo_id] >>
      first_x_assum $ qspec_then ‘mkGIx (A,s)’ mp_tac >> simp[]) >>
  ‘dGIx (mkGIx (A,s)) = (A,s)’ by metis_tac[repabs_pseudo_id] >>
  simp[]
QED

val Gbigprod_ty = ty_antiq “: (('a1,'b1) Gidx -> 'a1, 'b1) Galg”

Theorem minGbigprod_has_unique_Ghoms:
  let s = SND (Gbigprod : ^Gbigprod_ty)
  in
    ∀A f. Galg (A, f : ('a1,'b1) G -> 'a1) ⇒
          ∃!h. (∀d. d ∉ Gminset s ⇒ h d = ARB) ∧ Ghom h (Gminset s, s) (A, f)
Proof
  Cases_on ‘Gbigprod : ^Gbigprod_ty’ >> simp[] >>
  rpt strip_tac >>
  rename [‘Gbigprod = (AA,FF)’] >> gs[] >>
  ‘Galg (AA,FF)’ by simp[Gbigprod_isalg] >>
  ‘Galg (Gminset FF, FF)’ by simp[] >>
  ‘∃h0. Ghom h0 (Gbigprod:^Gbigprod_ty) (A,f)’
    by (irule_at (Pos hd) Gbigprod_proj >> simp[]) >>
  ‘subGalg (Gminset FF, FF) (AA,FF)’
    by metis_tac[minsub_subGalg] >>
  ‘Ghom h0 (Gminset FF, FF) (A,f)’ by metis_tac[subalgs_preserve_Ghoms] >>
  simp[EXISTS_UNIQUE_ALT] >>
  qexists_tac ‘λa. if a ∈ Gminset FF then h0 a else ARB’ >>
  simp[EQ_IMP_THM, FORALL_AND_THM] >> reverse conj_tac
  >- (irule Ghoms_on_same_domain >> first_assum $ irule_at Any >>
      simp[]) >>
  qx_gen_tac ‘h1’ >> strip_tac >> csimp[FUN_EQ_THM, AllCaseEqs()] >>
  metis_tac[minsub_gives_unique_Ghoms]
QED

(* there are unique Ghoms out of the minimised product of all α-algebras into
   α-algebras, but we have to find an α that is big enough that algebras over
   other types can be injected into them.

*)

(* Traytel's K function, from MSc thesis, p 15 *)

val KKG_def = new_specification(
  "KKG", ["KKG"],
  ord_RECURSION |> Q.ISPEC ‘∅ : γ set’
                |> Q.SPEC ‘λx r. r ∪ { s(x) | Gset x ⊆ r }’
                |> Q.SPEC ‘λx rs. BIGUNION rs’
                |> BETA_RULE
                |> Q.GEN ‘s’ |> CONV_RULE SKOLEM_CONV);

Theorem KKG_mono:
  ∀β α. α < β ⇒ KKG s α ⊆ KKG s β
Proof
  ho_match_mp_tac simple_ord_induction >>
  bsimp
               [KKG_def, ordlt_SUC_DISCRETE, DISJ_IMP_THM, FORALL_AND_THM,
                ordlt_ZERO, SUBSET_UNION] >>
  rpt strip_tac
  >- (first_x_assum $ drule_then (C (resolve_then (Pos hd) irule) SUBSET_TRANS)>>
      REWRITE_TAC[SUBSET_UNION]) >>
  gs[omax_NONE] >>
  last_x_assum $ drule_then strip_assume_tac>>
  first_x_assum $ drule_all_then assume_tac >>
  irule SUBSET_BIGUNION_I >> simp[]
QED

Theorem KKG_mono_LE:
  ∀α β. α ≤ β ⇒ KKG s α ⊆ KKG s β
Proof
  metis_tac[SUBSET_REFL, KKG_mono, ordle_lteq]
QED

Theorem KKG_SUB_min:
  ∀α. KKG s α ⊆ Gminset s
Proof
  ho_match_mp_tac simple_ord_induction >>
  simp_tac bool_ss [KKG_def, EMPTY_SUBSET] >> rpt strip_tac
  >- (REWRITE_TAC [SUBSET_DEF] >>
      gen_tac >> CONV_TAC (LAND_CONV (REWR_CONV IN_UNION)) >> strip_tac
      >- (irule (iffLR SUBSET_DEF) >> rpt (first_assum $ irule_at Any)) >>
      pop_assum mp_tac >> CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
      strip_tac >> ASM_REWRITE_TAC []>>
      irule Gset_SUBSET_Gminset >> irule SUBSET_TRANS >>
      first_assum $ irule_at Any >> ASM_REWRITE_TAC[SUBSET_DEF]) >>
  ASM_REWRITE_TAC [BIGUNION_IMAGE_SUBSET, IN_preds]
QED

Theorem KKG_fixp_is_alg:
  { s x | x | Gset x ⊆ KKG s ε } = KKG s ε ⇒
  Galg(KKG s ε, s)
Proof
  simp_tac bool_ss [Galg_def, GFin_def] >>
  disch_then (assume_tac o SYM) >> gen_tac >>
  CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
  REWRITE_TAC[SUBSET_UNIV] >> strip_tac >>
  qpat_assum ‘_ = _’ (ONCE_REWRITE_TAC o single) >>
  CONV_TAC pred_setLib.SET_SPEC_CONV >>
  irule_at Any EQ_REFL >> first_assum ACCEPT_TAC
QED

Theorem KKG_sup:
  ords ≼ 𝕌(:num + 'a) ⇒
  KKG s (sup ords : 'a ordinal) = BIGUNION (IMAGE (KKG s) ords)
Proof
  strip_tac >> Cases_on ‘ords = ∅’ >> simp[KKG_def] >>
  Cases_on ‘omax ords’
  >- (gs[omax_NONE] >>
      ‘islimit (sup ords)’
        by (simp[omax_NONE, sup_thm, PULL_EXISTS] >>
            metis_tac[ordlt_TRANS]) >>
      Cases_on ‘sup ords = 0’ >- gs[KKG_def, sup_EQ_0] >>
      ‘0 < sup ords’ by metis_tac[IFF_ZERO_lt] >>
      simp[KKG_def] >> irule SUBSET_ANTISYM >>
      simp[SUBSET_DEF, PULL_EXISTS, sup_thm] >> rw[] >> (* 2 *)
      metis_tac[SUBSET_DEF, KKG_mono]) >>
  gs[omax_SOME] >> rename [‘_ ≤ mx’, ‘mx ∈ ords’] >>
  ‘sup ords = mx’ by metis_tac[sup_eq_max] >> simp[] >>
  irule SUBSET_ANTISYM >> simp[SUBSET_DEF, PULL_EXISTS] >> rw[] (* 2 *)
  >- metis_tac[] >>
  metis_tac[KKG_mono_LE, SUBSET_DEF]
QED

Theorem KKG_preds_subset:
  BIGUNION (IMAGE (KKG s) (preds α)) ⊆ KKG s α
Proof
  qid_spec_tac ‘α’ >> ho_match_mp_tac simple_ord_induction >>
  rw[] (* 2 *)
  >- (simp[KKG_def, preds_ordSUC] >> irule SUBSET_TRANS >> goal_assum drule >>
      simp[]) >>
  simp[KKG_def]
QED

Theorem KKG_thm:
  KKG s α = if α = 0 then ∅
           else BIGUNION (IMAGE (λa. { s fv | fv | Gset fv ⊆ KKG s a})
                          (preds α))
Proof
  qid_spec_tac ‘α’ >> ho_match_mp_tac simple_ord_induction >>
  rpt strip_tac >> REWRITE_TAC[ordSUC_ZERO] (* 3 *)
  >- simp[KKG_def]
  >- (ONCE_ASM_REWRITE_TAC[KKG_def] >>
      simp_tac bool_ss [preds_ordSUC, IMAGE_INSERT, BIGUNION_INSERT] >>
      Cases_on ‘α = 0’
      >- (pop_assum SUBST_ALL_TAC >>
          REWRITE_TAC [KKG_def, UNION_EMPTY, preds_0, IMAGE_EMPTY,
                       BIGUNION_EMPTY]) >>
      qpat_x_assum ‘_ = _’ mp_tac >> ASM_REWRITE_TAC[] >>
      disch_then (assume_tac o SYM) >>
      bsimp [AC UNION_ASSOC UNION_COMM]) >>
  ‘α ≠ 0’ by (disch_then SUBST_ALL_TAC >> qpat_x_assum ‘0 < 0o’ mp_tac >>
              REWRITE_TAC[ordlt_REFL]) >>
  bsimp [] >>
  bsimp [KKG_def] >>
  simp_tac bool_ss [Once EXTENSION, PULL_EXISTS, IN_BIGUNION, IN_IMAGE] >>
  qx_gen_tac ‘v’ >> iff_tac
  >- (simp_tac bool_ss [PULL_EXISTS, IN_preds] >> qx_gen_tac ‘u’ >>
      Cases_on ‘u = 0’ >- bsimp [NOT_IN_EMPTY] >>
      rpt strip_tac >> rename [‘v ∈ KKG s a’] >>
      ‘a ≠ 0’ by (strip_tac >> gs[KKG_def]) >>
      ‘KKG s a = BIGUNION (IMAGE (λa0. { s fv | fv | Gset fv ⊆ KKG s a0})
                          (preds a))’ by metis_tac[] >>
      gs[PULL_EXISTS] >> metis_tac[ordlt_TRANS]) >>
  CONV_TAC LEFT_IMP_EXISTS_CONV >> qx_gen_tac ‘u’ >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  REWRITE_TAC [IN_preds] >> strip_tac >>
  rpt strip_tac >> rename [‘a < α’, ‘Gset fv ⊆ KKG s a’] >>
  qexists_tac ‘a⁺’ >> simp_tac bool_ss [KKG_def, IN_UNION] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  metis_tac[islimit_SUC_lt]
QED

Theorem Gsucbnd_suffices:
  ω ≤ (bd : γ ordinal) ∧ (∀x : ('a1,'b1)G. Gset x ≼ preds bd) ⇒
  Galg (KKG (s:('a1,'b1)G -> 'a1) (csuc bd), s)
Proof
  strip_tac >>
  ‘INFINITE (preds bd)’ by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
  irule KKG_fixp_is_alg >> irule SUBSET_ANTISYM >> conj_tac >>
  ONCE_REWRITE_TAC [SUBSET_DEF] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [PULL_EXISTS] >>
  rpt strip_tac
  >- (rename [‘s fv ∈ KKG s _’] >>
      drule_then strip_assume_tac csuc_is_nonzero_limit >>
      qpat_x_assum ‘Gset fv ⊆ _’ mp_tac >>
      bsimp [KKG_def, PULL_EXISTS, IN_BIGUNION, IN_IMAGE,
                            IN_preds, lt_csuc, SUBSET_DEF] >>
      disch_then (strip_assume_tac o
                  BRULE [GSYM RIGHT_EXISTS_IMP_THM,
                                     SKOLEM_THM]) >>
      rename [‘_ ∈ KKG s (g _)’, ‘preds (g _) ≼ preds bd’] >>
      qabbrev_tac ‘B = sup (IMAGE g $ Gset fv)’ >>
      ‘IMAGE g $ Gset fv ≼ univ(:num + (γ + num -> bool))’
        by (irule IMAGE_cardleq_rwt >>
            first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
            resolve_then (Pos hd) irule preds_inj_univ cardleq_TRANS >>
            simp[cardleq_lteq, bumpUNIV_cardlt]) >>
      ‘∀a. a < B ⇔ ∃v. v ∈ Gset fv ∧ a < g v’
        by bsimp [Abbr‘B’, sup_thm, PULL_EXISTS, IN_IMAGE] >>
      qexists_tac ‘B⁺’ >> bsimp [KKG_def] >> reverse conj_tac
      >- (simp[preds_ordSUC, INFINITE_cardleq_INSERT] >>
          bsimp [Abbr‘B’, preds_sup, dclose_BIGUNION] >>
          irule CARD_BIGUNION >>
          bsimp [IMAGE_cardleq_rwt, PULL_EXISTS, IN_IMAGE]) >>
      ‘KKG s B = BIGUNION (IMAGE (KKG s) (IMAGE g (Gset fv)))’
        by bsimp [KKG_sup, Abbr‘B’] >>
      ‘s fv ∈ {s x | x | Gset x ⊆ KKG s B}’ suffices_by
        (strip_tac >> ASM_REWRITE_TAC[IN_UNION]) >>
      CONV_TAC pred_setLib.SET_SPEC_CONV >>
      qexists_tac ‘fv’ >> bsimp [SUBSET_DEF, PULL_EXISTS] >>
      qx_gen_tac ‘x’ >>
      rpt strip_tac >> REWRITE_TAC[IN_BIGUNION, IN_IMAGE] >>
      bsimp [PULL_EXISTS] >> qexists_tac ‘x’ >>
      bsimp []) >>
  rename [‘v ∈ KKG s (csuc bd)’] >>
  drule_then strip_assume_tac csuc_is_nonzero_limit >>
  qpat_x_assum ‘v ∈ KKG _ _’ mp_tac >>
  bsimp [KKG_def, IN_BIGUNION, IN_IMAGE, PULL_EXISTS,
                        IN_preds] >>
  qx_gen_tac ‘a’ >>
  bsimp [Once KKG_thm] >>
  Cases_on ‘a = 0’ >- bsimp [NOT_IN_EMPTY] >>
  bsimp [IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_preds] >>
  qx_gen_tac ‘b’ >> CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  strip_tac >> rename [‘Gset fv ⊆ KKG s b’] >>
  first_assum $ irule_at Any >>
  irule SUBSET_BIGUNION_SUBSET_I >>
  bsimp [PULL_EXISTS, IN_IMAGE, IN_preds] >>
  qexists_tac ‘b’ >> first_assum $ irule_at Any >>
  irule ordlt_TRANS >> qexists_tac ‘a’ >> ASM_REWRITE_TAC[]
QED

Theorem KKGbnd_EQ_Gminset:
  ω ≤ (bd : γ ordinal) ∧ (∀x : ('a1,'b1)G. Gset x ≼ preds bd) ⇒
  KKG (s : ('a1,'b1)G -> 'a1) (csuc bd) = Gminset s
Proof
  strip_tac >> drule_all_then (qspec_then ‘s’ assume_tac) Gsucbnd_suffices >>
  irule SUBSET_ANTISYM >> REWRITE_TAC[KKG_SUB_min] >>
  drule minsub_I_subGalg >>
  bsimp [Ghom_def, GmapID, SUBSET_DEF, I_THM]
QED

Theorem GnontrivialBs:
  (∃x:('a1,'b1)G. Gset x ≠ ∅) ⇒
  ∀B. (B:'a1 set) ≼ GFin B : ('a1,'b1) G set
Proof
  rpt strip_tac >> simp[cardleq_def] >>
  qexists_tac ‘λb. Gmap (K b) x’ >>
  simp_tac bool_ss [INJ_IFF, GFin_def, GmapIMAGE, SUBSET_UNIV] >>
  conj_tac
  >- (rpt strip_tac >> CONV_TAC pred_setLib.SET_SPEC_CONV >>
      bsimp [GmapIMAGE, SUBSET_DEF, IN_IMAGE, K_THM,
             PULL_EXISTS]) >>
  simp_tac bool_ss [EQ_IMP_THM] >> rpt strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM ‘Gset’ ) >>
  bsimp [GmapIMAGE, EXTENSION, IN_IMAGE, PULL_EXISTS, K_THM] >>
  metis_tac[MEMBER_NOT_EMPTY]
QED

(* see Lemma 33 in ITP2014's
     "Cardinals in Isabelle/HOL" by Blanchette, Popescu and Traytel
 *)
Theorem GCBDb:
  ω ≤ (bd : γ ordinal) ∧ (∀x:('a1,'b1)G. Gset x ≼ preds bd) ∧
  (∃x:(γ ordinal,'b1)G. Gset x ≠ ∅)
⇒
  ∀B:'a1 set.
    𝟚 ≼ B ⇒
    GFin B : ('a1,'b1)G set ≼
    B ** cardSUC (GFin (preds bd) : (γ ordinal,'b1)G set)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘kA = GFin (preds bd) : (γ ordinal,'b1) G set CROSS
                    (B ** preds bd)’ >>
  qmatch_abbrev_tac ‘_ ≼ B ** k’ >>
  ‘kA ≼ B ** k’
    by (simp[Abbr‘k’, Abbr‘kA’] >> irule CARD_MUL2_ABSORB_LE >>
        simp[] >> rpt strip_tac
        >- (drule_all cardleq_TRANS >> simp[])
        >- (‘INFINITE (preds bd)’
              by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
            ‘preds bd ≼ GFin (preds bd) : (γ ordinal,'b1) G set’
              by metis_tac[GnontrivialBs] >>
            metis_tac[CARD_LE_FINITE])
        >- (resolve_then (Pos last) irule CARD_LE_EXP cardleq_TRANS >>
            simp[]) >>
        irule set_exp_cardle_cong >> simp[] >> rpt strip_tac
        >- gvs[cardleq_empty] >>
        ‘preds bd ≼ GFin (preds bd) : (γ ordinal,'b1) G set’
          by metis_tac[GnontrivialBs] >>
        first_x_assum $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
        simp[]) >>
  first_assum $ C (resolve_then (Pos last) irule) cardleq_TRANS >>
  qabbrev_tac ‘d = λ(y:('c ordinal,'b1)G, f). Gmap f y : ('a1,'b1) G’ >>
  simp[cardleq_def] >>
  irule_at Any (SRULE [PULL_EXISTS] SURJ_IMP_INJ) >> qexists_tac ‘d’ >>
  simp[SURJ_DEF] >> conj_tac
  >- (bsimp
                   [FORALL_PROD,Abbr‘kA’, Abbr‘d’, GFin_def,
                    set_exp_def, UNCURRY_DEF, IN_CARD_MUL, SUBSET_UNIV] >>
      CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
      bsimp [GmapIMAGE] >> rpt strip_tac >>
      bsimp [SUBSET_DEF, PULL_EXISTS, IN_IMAGE] >>
      qx_gen_tac ‘b’ >> strip_tac >>
      ‘b ∈ preds bd’ by metis_tac[SUBSET_DEF] >> bsimp []) >>
  qx_gen_tac ‘vf’ >> strip_tac >>
  ‘?g. INJ g (Gset vf) (preds bd)’ by metis_tac[cardleq_def] >>
  qabbrev_tac ‘y = Gmap g vf’ >>
  ‘Gset vf ⊆ B’
    by (qpat_x_assum ‘vf ∈ GFin _’ mp_tac >>
        simp_tac (bool_ss ++ pred_setLib.PRED_SET_ss)[GFin_def]) >>
  ‘?f. (!b. b ∈ Gset vf ⇒ f (g b) = b) /\ (!bp. bp < bd ==> f bp ∈ B)’
    by (‘?be. be ∈ B’ by (simp[MEMBER_NOT_EMPTY] >>
                          strip_tac >> gvs[cardleq_empty]) >>
        qexists_tac ‘λbp. case some b. b IN Gset vf /\ g b = bp of
                            NONE => be
                          | SOME b => b
                    ’ >> conj_tac >> bsimp [] >> rpt strip_tac
        >- (qpat_x_assum ‘INJ _ _ (preds bd)’ mp_tac >>
            bsimp [INJ_IFF, SF CONJ_ss] >>
            bsimp [SF CONJ_ss, optionTheory.some_EQ,
                                  optionTheory.option_case_def]) >>
        DEEP_INTRO_TAC optionTheory.some_intro >>
        bsimp [optionTheory.option_case_def] >>
        metis_tac[SUBSET_DEF]) >>
  qexists_tac ‘(y, λbp. if bp ∈ preds bd then f bp else ARB)’ >>
  conj_tac
  >- (bsimp
        [Abbr‘kA’, GFin_def, Abbr‘y’, IN_CARD_MUL, SUBSET_UNIV] >>
      conj_tac
      >- (CONV_TAC pred_setLib.SET_SPEC_CONV >>
          bsimp [GmapIMAGE, INJ_IMAGE_SUBSET]) >>
      simp[set_exp_def]) >>
  simp[Abbr‘d’, Abbr‘y’, GmapO'] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM GmapID'))) >>
  irule GmapCONG >>
  bsimp [o_THM, bool_case_eq, I_THM] >>
  qpat_x_assum ‘INJ _ _ _ ’ mp_tac >>
  simp_tac bool_ss [INJ_IFF, IN_preds]
QED

Theorem preds_bd_lemma[local]:
  Gset (gv  : (γ ordinal,'b1)G) ≠ ∅ ⇒
  preds (bd:γ ordinal) ≼
    preds (oleast a:(γ ordinal,'b1)G ordinal.
             preds a ≈ GFin (preds bd) : (γ ordinal,'b1) G set)
Proof
  strip_tac >>
  ‘preds bd ≼ GFin (preds bd) : (γ ordinal,'b1) G set’
    by metis_tac[GnontrivialBs] >>
  pop_assum mp_tac >>
  simp[Once cardleq_lteq, SimpL “$==>”] >> strip_tac
  >- (DEEP_INTRO_TAC oleast_intro >> conj_tac
      >- (irule cardeq_ordinals_exist >>
          simp[Once disjUNION_UNIV] >>
          resolve_then (Pos hd) irule CARD_LE_UNIV
                       CARD_LE_TRANS >>
          simp[CARD_LE_ADDL]) >>
      metis_tac[cardleq_lteq, CARD_LT_CONG, CARD_EQ_REFL]) >>
  DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- (irule cardeq_ordinals_exist >>
      simp[Once disjUNION_UNIV] >>
      resolve_then (Pos hd) irule CARD_LE_UNIV CARD_LE_TRANS >>
      simp[CARD_LE_ADDL]) >>
  metis_tac[CARD_LE_REFL, CARD_LE_CONG]
QED

Theorem GFin_MONO:
  s ⊆ t ⇒ GFin s ⊆ GFin t
Proof
  simp_tac bool_ss [GFin_def, SUBSET_DEF, IN_GSPEC_IFF]
QED

Theorem GFin_cardleq:
  s ≼ t ⇒ GFin s : ('a1,'b1) G set ≼ GFin t : ('c1,'b1) G set
Proof
  simp_tac bool_ss [GFin_def, cardleq_def] >>
  disch_then $ qx_choose_then ‘f’ strip_assume_tac >>
  qexists_tac ‘Gmap f’ >>
  simp_tac bool_ss [INJ_IFF, IN_GSPEC_IFF, GmapIMAGE, IMAGE_I] >>
  rpt strip_tac
  >- (dxrule_then assume_tac INJ_IMAGE_SUBSET >>
      irule SUBSET_TRANS >> irule_at Any IMAGE_SUBSET >>
      rpt (first_assum $ irule_at Any)) >>
  simp_tac bool_ss [EQ_IMP_THM] >> strip_tac >>
  ‘Gmap (LINV f s o f) x = Gmap I x ∧ Gmap (LINV f s o f) y = Gmap I y’
    by (conj_tac >> irule GmapCONG >> drule_then assume_tac LINV_DEF >>
        simp_tac bool_ss [I_THM, o_THM] >>
        metis_tac[SUBSET_DEF]) >>
  qpat_x_assum ‘Gmap f x = _’ (mp_tac o Q.AP_TERM ‘Gmap (LINV f s)’) >>
  bsimp [GmapO',funMap_ID, I_THM, GmapID]
QED

Theorem Galg_cardinality_bound:
  ω ≤ (bd : 'b1 ordinal) ∧ (∀x:('a1+bool,'b1)G. Gset x ≼ preds bd) ∧
  (∃x:('b1 ordinal,'b1)G. Gset x ≠ ∅) ⇒
  KKG (s:('a1,'b1)G -> 'a1) (csuc bd) ≼
  𝟚 ** (cardSUC $ GFin (preds bd) : ('b1 ordinal,'b1) G set)
Proof
  strip_tac >> rename [‘Gset gv ≠ ∅’] >>
  qmatch_abbrev_tac ‘_ ≼ 𝟚 ** BD’ >>
  ‘INFINITE BD’
    by (simp_tac bool_ss [Abbr‘BD’, FINITE_cardSUC] >> strip_tac >>
        ‘preds bd ≼ GFin (preds bd) : ('b1 ordinal,'b1) G set’
          by metis_tac[GnontrivialBs] >>
        ‘FINITE (preds bd)’ by metis_tac[CARD_LE_FINITE] >>
        gs[FINITE_preds]) >>
  ‘BD ≠ ∅’ by simp[Abbr‘BD’] >>
  ‘∀i. i < csuc bd ⇒ KKG s i ≼ 𝟚 ** BD’
    suffices_by (strip_tac >>
                 bsimp [csuc_is_nonzero_limit, KKG_def] >>
                 irule CARD_BIGUNION >>
                 bsimp [PULL_EXISTS, IN_IMAGE, IN_preds,
                                       FINITE_setexp, CARD_12] >>
                 irule IMAGE_cardleq_rwt >>
                 resolve_then Any
                              (fn th =>
                                 resolve_then (Pos hd) irule th cardleq_TRANS)
                              cardleq_REFL
                              CARD_LE_EXP >>
                 irule set_exp_cardle_cong >>
                 bsimp [CARD_12, cardleq_REFL, cardSUC_def,
                                       NOT_INSERT_EMPTY, Abbr‘BD’] >>
                 irule cardleq_preds_csuc >> metis_tac[preds_bd_lemma]) >>
  ho_match_mp_tac ord_induction >> rpt strip_tac >>
  simp_tac bool_ss [Once KKG_thm] >> COND_CASES_TAC
  >- simp_tac bool_ss [EMPTY_CARDLEQ] >> irule CARD_BIGUNION >>
  bsimp
               [IN_IMAGE, FINITE_setexp, CARD_12, PULL_EXISTS, IN_preds] >>
  reverse conj_tac
  >- (irule IMAGE_cardleq_rwt >>
      resolve_then Any
                   (fn th =>
                      resolve_then (Pos hd) irule th cardleq_TRANS)
                   cardleq_REFL
                   CARD_LE_EXP >> irule set_exp_cardle_cong >>
      bsimp [NOT_INSERT_EMPTY, cardleq_REFL] >> simp[] >>
      RULE_ASSUM_TAC (BRULE[lt_csuc]) >>
      drule_then (qspec_then ‘bd’ assume_tac) preds_bd_lemma >>
      dxrule_then assume_tac cardleq_preds_csuc >>
      bsimp [Abbr‘BD’, cardSUC_def] >>
      pop_assum (C (resolve_then (Pos last) irule) cardleq_TRANS) >>
      first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
      simp_tac bool_ss [preds_csuc_lemma]) >>
  qx_gen_tac ‘j’ >> strip_tac >>
  ‘{ s fv | fv | Gset fv ⊆ KKG s j} = IMAGE s (GFin (KKG s j))’
    by (simp_tac bool_ss [EXTENSION, GFin_def, IN_IMAGE] >>
        CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
        simp_tac bool_ss [SUBSET_UNIV]) >>
  ASM_REWRITE_TAC [] >>
  irule IMAGE_cardleq_rwt >>
  resolve_then (Pos hd) irule (MATCH_MP (GEN_ALL GFin_cardleq) cardADD2)
               cardleq_TRANS >>
  drule_then (drule_then $ qspec_then ‘KKG s j +_c 𝟚’ mp_tac) GCBDb >> impl_tac
  >- (conj_tac >- first_assum $ irule_at Any >> simp[CARD_LE_ADDL]) >>
  disch_then $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
  first_x_assum $ qspec_then ‘j’ mp_tac >> simp[] >>
  impl_tac >- metis_tac[ordlt_TRANS] >>
  disch_then
    (C (resolve_then (Pos hd) (qspecl_then [‘𝟚’, ‘𝟚’] mp_tac)) CARD_LE_ADD) >>
  simp[] >> strip_tac >>
  pop_assum (
    C (resolve_then (Pos (el 2)) (resolve_then (Pos last)
                                  (qspec_then ‘BD’ mp_tac) cardleq_REFL))
    set_exp_cardle_cong) >>
  impl_tac >- simp[Abbr‘BD’] >>
  disch_then (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
  ‘𝟚 ≼ 𝟚 ** BD’ by (simp[cardleq_setexp] >> simp[Abbr‘BD’]) >>
  ‘INFINITE (𝟚 ** BD)’ by simp[] >>
  ‘𝟚 ** BD +_c 𝟚 ≈ 𝟚 ** BD’
    by metis_tac[CARD_ADD_SYM, CARD_ADD_ABSORB, cardeq_TRANS] >>
  pop_assum (C (resolve_then (Pos hd) (qspecl_then [‘BD’, ‘BD’] mp_tac))
               set_exp_card_cong) >> simp_tac bool_ss [cardeq_REFL] >>
  strip_tac >>
  pop_assum (C (resolve_then (Pos hd)
                (resolve_then (Pos hd) irule cardeq_REFL))
             (iffRL CARD_LE_CONG)) >>
  resolve_then (Pos hd) (resolve_then (Pos hd) irule cardeq_REFL)
               set_exp_product (iffRL CARD_LE_CONG) >>
  irule set_exp_cardle_cong >>
  simp_tac bool_ss [NOT_INSERT_EMPTY, cardleq_REFL] >>
  ONCE_REWRITE_TAC [cardleq_lteq] >>
  bsimp [CARD_SQUARE_INFINITE]
QED

Theorem Gset_cle_bnd:
  ∀x:('a1,'b1) G. Gset x ≼ preds (bnd : 'b1 ordinal)
Proof
  strip_tac >>
  ‘Gset x ≈ Gset x’ by REWRITE_TAC [cardeq_REFL] >>
  ‘preds (bnd:'b1 ordinal) ≈ univ(:num + 'b1)’
    by REWRITE_TAC[bnd_def,ordOf_def] >>
  dxrule_then (dxrule_then irule) (iffRL CARD_LE_CONG) >>
  MATCH_ACCEPT_TAC (GEN_ALL Gset_bounded)
QED

Theorem KKG_EQ_GMINSET =
        KKGbnd_EQ_Gminset |> INST_TYPE [“:γ” |-> “:'b1”]
                        |> Q.INST [‘bd’ |-> ‘bnd’]
                        |> C MATCH_MP (CONJ omega_le_bnd Gset_cle_bnd)

Theorem Ginst_bound =
        Galg_cardinality_bound |> Q.INST [‘bd’ |-> ‘bnd’]
                               |> REWRITE_RULE [omega_le_bnd, KKG_EQ_GMINSET,
                                                Gset_cle_bnd, Gset_exists]

Type Galgty0[pp] = (#1 $ dom_rng $ type_of $ rand $ concl Ginst_bound)

Theorem Gcopy_alg_back:
  (A:'a1 set) ≼ (B:'c1 set) ∧ Galg (A, s : ('a1,'b1)G -> 'a1) ⇒
  ∃(B0:'c1 set) (s':('c1,'b1)G -> 'c1) h j.
    Ghom h (B0,s') (A,s) ∧ Ghom j (A,s) (B0,s') ∧
    (∀a. a ∈ A ⇒ h (j a) = a) ∧ (∀b. b ∈ B0 ⇒ j (h b) = b)
Proof
  simp_tac bool_ss [cardleq_def] >> strip_tac >> rename [‘INJ h0 A B’] >>
  qexistsl_tac [‘IMAGE h0 A’, ‘λbv. h0 $ s $ Gmap (LINV h0 A) bv’,
                ‘LINV h0 A’, ‘h0’] >>
  asm_simp_tac (bool_ss ++ CONJ_ss)[Ghom_def, PULL_EXISTS, IN_IMAGE] >>
  drule_then assume_tac LINV_DEF >> rpt strip_tac >> bsimp []
  >- (qpat_x_assum ‘Galg _’ mp_tac >>
      bsimp [Galg_def, GFin_def, SUBSET_DEF, IN_UNIV, IN_IMAGE] >>
      CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >> rpt strip_tac >>
      irule_at Any EQ_REFL >> first_assum irule >>
      bsimp [GmapIMAGE, PULL_EXISTS, IN_IMAGE] >>
      rpt strip_tac >> first_assum drule >>
      bsimp[PULL_EXISTS])
  >- (‘s (Gmap (LINV h0 A) bv) ∈ A’
        by (qpat_x_assum ‘Galg _’ mp_tac >>
            bsimp [Galg_def, GFin_def, SUBSET_DEF, IN_UNIV,
                                  IN_IMAGE] >>
            CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >> rpt strip_tac >>
            first_assum irule >>
            bsimp [GmapIMAGE, IN_IMAGE, PULL_EXISTS] >>
            qpat_x_assum ‘bv ∈ GFin _’ mp_tac >>
            bsimp [GFin_def, SUBSET_UNIV] >>
            CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
            bsimp [SUBSET_DEF, PULL_EXISTS, IN_IMAGE] >>
            rpt strip_tac >>
            first_assum drule >> bsimp [PULL_EXISTS]) >>
      bsimp [])
  >- (irule_at Any EQ_REFL >> first_assum ACCEPT_TAC)
  >- (bsimp [GmapO', I_o_ID] >>
      rename [‘av ∈ GFin A’] >>
      ‘Gmap (LINV h0 A o h0) av = Gmap I av’
        suffices_by simp[GmapID, GmapO'] >>
      irule GmapCONG >>
      qpat_x_assum ‘_ ∈ GFin _’ mp_tac >>
      bsimp [GFin_def, SUBSET_UNIV, o_THM,
                            I_THM] >>
      CONV_TAC (LAND_CONV pred_setLib.SET_SPEC_CONV) >>
      bsimp [SUBSET_DEF, PULL_EXISTS])
QED

Type Galgty[pp] = “:('b1 Galgty0,'b1)Gidx -> 'b1 Galgty0”
Definition GCons_def:
  GCons = SND $ Gbigprod : ('b1 Galgty,'b1)Galg
End

Definition IGalg_def:
  IGAlg = Gminset GCons
End

Theorem IGAlg_isalg:
  Galg (IGAlg, GCons)
Proof
  REWRITE_TAC [IGalg_def, Gminset_is_alg]
QED

Theorem Ghom_arbification:
  Ghom h (A,s) (B,t) ⇒
  ∃j. Ghom j (A,s) (B,t) ∧ ∀x. x ∉ A ⇒ j x = ARB
Proof
  strip_tac >>
  qexists_tac ‘λx. if x ∈ A then h x else ARB’ >> simp_tac bool_ss [] >>
  pop_assum mp_tac >> simp_tac bool_ss [Ghom_def, GFin_def, Galg_def] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [SUBSET_UNIV] >> rpt strip_tac >>
  RULE_ASSUM_TAC GSYM >> bsimp [] >>
  AP_TERM_TAC >> irule GmapCONG >> bsimp [] >>
  qpat_x_assum ‘_ ⊆ _’ mp_tac >> simp_tac bool_ss [SUBSET_DEF]
QED

val gcons_t = “GCons : ('b1 Galgty,'b1) G -> 'b1 Galgty”

Theorem Ginitiality0:
  ∀(t:('a1,'b1)G -> 'a1) (G:'a1 set).
    Galg(G,t) ⇒
    ∃!h. Ghom h (IGAlg,^gcons_t) (G,t) ∧ ∀x. x ∉ IGAlg ⇒ h x = ARB
Proof
  rpt strip_tac >> simp_tac bool_ss [EXISTS_UNIQUE_THM] >> reverse conj_tac
  >- (rpt strip_tac >> REWRITE_TAC[FUN_EQ_THM] >> qx_gen_tac ‘a’ >>
      Cases_on ‘a ∈ IGAlg’ >> bsimp[] >>
      RULE_ASSUM_TAC (REWRITE_RULE [IGalg_def]) >>
      dxrule_all minsub_gives_unique_Ghoms >> simp_tac bool_ss []) >>
  irule Ghom_arbification >>
  simp[IGalg_def] >>
  ‘Ghom I (Gminset ^gcons_t, ^gcons_t) (FST Gbigprod,^gcons_t)’
    by (irule minsub_I_subGalg >> REWRITE_TAC[Gbigprod_isalg, GCons_def, PAIR])>>
  dxrule_then (irule_at (Pos hd)) Ghoms_compose >>
  ‘Ghom I (Gminset t, t) (G,t)’ by (irule minsub_I_subGalg >> metis_tac[]) >>
  pop_assum $ C (resolve_then (Pos last) (irule_at (Pos hd))) Ghoms_compose >>
  ‘Galg (Gminset t, t)’ by REWRITE_TAC [Gminset_is_alg] >>
  resolve_then (Pos hd) (drule_then strip_assume_tac)
               Ginst_bound Gcopy_alg_back >>
  rename [‘Ghom h (A0,s) (Gminset t, t)’] >>
  first_assum $ C (resolve_then (Pos last) (irule_at (Pos hd))) Ghoms_compose >>
  REWRITE_TAC[PAIR,GCons_def] >>
  irule_at (Pos hd) Gbigprod_proj >> qpat_x_assum ‘Ghom _ (A0,s) _’ mp_tac >>
  simp_tac bool_ss [Ghom_def]
QED

Theorem Ginhabited:
  ∃w. IGAlg w
Proof
  ‘Galg (IGAlg, GCons)’ by REWRITE_TAC[IGAlg_isalg] >>
  drule Galg_nonempty >> simp_tac bool_ss [EXTENSION, IN_DEF, EMPTY_DEF]
QED

Theorem Galg_Fin:
  Galg (A,s) ⇒ Galg (GFin A : ('a1,'b1) G set, Gmap s)
Proof
  strip_tac >>
  simp_tac bool_ss [Galg_def, GFin_def, SUBSET_DEF, PULL_EXISTS] >>
  CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
  simp_tac bool_ss [IN_UNIV, GmapIMAGE, IN_IMAGE, PULL_EXISTS] >>
  rpt strip_tac >>
  rename [‘s vf ∈ A’, ‘vf ∈ Gset vff’] >>
  first_assum $ drule_then assume_tac >>
  irule (iffLR $ BRULE [GFin_def, PULL_EXISTS] Galg_def) >>
  ASM_REWRITE_TAC[] >> CONV_TAC pred_setLib.SET_SPEC_CONV >>
  ASM_REWRITE_TAC[SUBSET_DEF, IN_UNIV]
QED

Theorem IN_GFin_chained:
  x ∈ GFin A ∧ y ∈ Gset x ⇒ y ∈ A
Proof
  bsimp [GFin_def, IN_GSPEC_IFF, SUBSET_DEF]
QED

Theorem Ghom_arbify:
  Ghom (arbify A f) (A,s : ('a1,'b1)G -> 'a1)
                   (B,t : ('c1,'b1)G -> 'c1) ⇔
    Ghom f (A,s) (B,t)
Proof
  simp_tac bool_ss [Ghom_def, arbify_def] >> Cases_on ‘Galg (A,s)’ >>
  bsimp [] >>
  drule_then assume_tac (iffLR Galg_def) >> bsimp [] >>
  iff_tac >> rpt strip_tac >> bsimp [] >>
  RULE_ASSUM_TAC GSYM >> bsimp [] >> AP_TERM_TAC >>
  irule GmapCONG >> drule_then assume_tac IN_GFin_chained >>
  bsimp [arbify_def]
QED

Theorem Giso0:
  BIJ ^gcons_t (GFin IGAlg) IGAlg
Proof
  ‘Galg (IGAlg, ^gcons_t)’ by REWRITE_TAC[IGAlg_isalg] >>
  drule_then assume_tac Galg_Fin >>
  drule_then mp_tac Ginitiality0 >>
  simp_tac bool_ss [EXISTS_UNIQUE_ALT] >> strip_tac >>
  rename[‘Ghom _ (IGAlg,GCons) _ ∧ _ ⇔ H = _’] >>
  ‘Ghom H (IGAlg,^gcons_t) (GFin IGAlg, Gmap GCons)’
    by (pop_assum (qspec_then ‘H’ mp_tac) >> simp_tac bool_ss []) >>
  ‘Ghom GCons (GFin IGAlg, Gmap GCons) (IGAlg,^gcons_t)’
    by (bsimp [Ghom_def, iffLR Galg_def]) >>
  rev_drule_then (drule_then assume_tac) Ghoms_compose >>
  rev_drule_then (strip_assume_tac o SRULE [EXISTS_UNIQUE_ALT]) Ginitiality0 >>
  ‘Ghom (arbify IGAlg (^gcons_t o H)) (IGAlg,GCons) (IGAlg,GCons)’
    by ASM_REWRITE_TAC[Ghom_arbify] >>
  ‘∀x. x ∉ IGAlg ⇒ arbify IGAlg (GCons o H) x = ARB’
    by simp_tac bool_ss [arbify_def] >>
  ‘Ghom (arbify IGAlg I) (IGAlg,^gcons_t) (IGAlg,GCons)’
    by (bsimp [Ghom_arbify, Ghom_def, GmapID, I_THM])>>
  ‘∀x. x ∉ (IGAlg:'b1 Galgty -> bool) ⇒ arbify IGAlg I x = ARB’
    by simp_tac bool_ss [arbify_def] >>
  ‘arbify IGAlg (^gcons_t o H) = arbify IGAlg I’ by metis_tac[] >>
  bsimp[BIJ_IFF_INV] >> conj_tac
  >- bsimp [iffLR Galg_def] >>
  qexists_tac ‘H’ >> conj_tac
  >- (qpat_x_assum ‘Ghom H _ _’ mp_tac >> bsimp [Ghom_def]) >>
  conj_asm2_tac
  >- (qpat_x_assum ‘Ghom H _ _’ mp_tac >>
      bsimp [Ghom_def, GmapO', I_o_ID, o_THM] >> strip_tac >>
      qx_gen_tac ‘a’ >> strip_tac >>
      ‘H (GCons a) = Gmap (GCons o H) a’ by bsimp [] >>
      pop_assum SUBST1_TAC >>
      ‘Gmap (GCons o H) a = Gmap I a’ suffices_by simp_tac bool_ss [GmapID']>>
      irule GmapCONG >> drule_then assume_tac IN_GFin_chained >>
      bsimp [o_THM, I_THM]) >>
  pop_assum mp_tac >>
  simp_tac bool_ss [Once FUN_EQ_THM, arbify_def, I_THM, o_THM] >> metis_tac[]
QED

val itype2 = newtypeTools.rich_new_type{
  tyname = "nty2", exthm = Ginhabited,
  ABS = "nty2_ABS", REP = "nty2_REP"
  }

Definition NCONS2_def:
  NCONS2 (x : ('b1 nty2, 'b1)G) = nty2_ABS $ GCons $ Gmap nty2_REP x
End

Theorem NCONS2_isalg:
  Galg (UNIV, NCONS2)
Proof
  simp[Galg_def]
QED

Theorem Ghom_nty2_ABS:
  Ghom nty2_ABS (IGAlg,GCons) (UNIV,NCONS2)
Proof
  bsimp[Ghom_def, NCONS2_isalg, IGAlg_isalg, IN_UNIV] >>
  bsimp[NCONS2_def, GmapO', I_o_ID] >>
  rpt strip_tac >> rpt AP_TERM_TAC >>
  CONV_TAC (RHS_CONV $ REWR_CONV $ GSYM GmapID') >>
  irule GmapCONG >>
  bsimp[I_THM, o_THM] >> rpt strip_tac >>
  irule $ #repabs_pseudo_id itype2 >> drule_all IN_GFin_chained >>
  simp_tac bool_ss [IN_DEF]
QED

Theorem Ghom_nty2_REP:
  Ghom nty2_REP (UNIV, NCONS2) (IGAlg:'b1 Galgty -> bool, GCons)
Proof
  simp_tac bool_ss [Ghom_def, NCONS2_isalg, IGAlg_isalg] >> conj_tac
  >- simp_tac bool_ss [IN_DEF, # termP_term_REP itype2] >>
  simp_tac bool_ss [NCONS2_def] >> rpt strip_tac >>
  ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  irule (#repabs_pseudo_id itype2) >>
  ‘Galg (IGAlg : 'b1 Galgty set,GCons)’ by simp[IGAlg_isalg] >>
  drule_then assume_tac (iffLR Galg_def) >>
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] >> pop_assum irule >>
  simp_tac bool_ss [GFin_def, IN_GSPEC_IFF, GmapIMAGE, PULL_EXISTS, IN_IMAGE,
                    SUBSET_DEF, IN_UNIV] >>
  simp_tac bool_ss [IN_DEF, #termP_term_REP itype2]
QED

Theorem Ginitiality_hom:
  Galg(B,t:('a1,'b1) G -> 'a1) ⇒ ∃!h. Ghom h (UNIV,NCONS2) (B,t)
Proof
  strip_tac >>
  simp_tac bool_ss [EXISTS_UNIQUE_THM] >>
  drule_then (strip_assume_tac o BRULE [EXISTS_UNIQUE_ALT])
             Ginitiality0 >>
  rename [‘Ghom _ _ _ ∧ _ ⇔ H = _’] >>
  ‘Ghom H (IGAlg,^gcons_t) (B,t)’ by metis_tac[] >> conj_tac
  >- metis_tac[Ghoms_compose, Ghom_nty2_REP] >>
  qx_genl_tac [‘h1’, ‘h2’] >> strip_tac >>
  ‘Ghom (arbify IGAlg (h1 o nty2_ABS)) (IGAlg,^gcons_t) (B,t) ∧
   Ghom (arbify IGAlg (h2 o nty2_ABS)) (IGAlg,^gcons_t) (B,t)’
    by (simp_tac bool_ss[Ghom_arbify] >>
        metis_tac[Ghoms_compose, Ghom_nty2_ABS]) >>
  ‘arbify IGAlg (h1 o nty2_ABS) = arbify IGAlg (h2 o nty2_ABS)’
    by metis_tac[arbify_def] >>
  pop_assum mp_tac >> ONCE_REWRITE_TAC [FUN_EQ_THM] >>
  simp_tac bool_ss [arbify_def] >>
  strip_tac >> qx_gen_tac ‘a’ >>
  qspec_then ‘a’ (SUBST1_TAC o SYM) (#absrep_id itype2) >>
  pop_assum $ qspec_then ‘nty2_REP a’ mp_tac >>
  simp_tac bool_ss [#termP_term_REP itype2, IN_DEF, o_THM]
QED

Theorem Ginitiality =
        Ginitiality_hom |> Q.INST [‘B’ |-> ‘UNIV’]
                       |> BRULE [Ghom_def, Galg_def, GFin_def,
                                 SUBSET_UNIV, IN_UNIV, GSPEC_T]
                       |> GSYM |> Q.GEN ‘t’
Definition D1_def:
  D1 x = NCONS2 (INL x)
End

Definition D2_def:
  D2 x xs = NCONS2 (INR (x,xs))
End

Theorem FORALL_UNCURRIED:
  (∀f: 'a # 'b -> 'c. P f) =
  (∀f: 'a -> 'b -> 'c. P (UNCURRY f))
Proof
  rw[EQ_IMP_THM] >> metis_tac[UNCURRY_CURRY_THM]
QED

Theorem better_Ginitiality =
        Ginitiality
          |> SRULE [sumTheory.FORALL_SUM, FORALL_SUMALG, FORALL_PROD,
                    GSYM D1_def, GSYM D2_def, FORALL_UNCURRIED]

Type NTY[pp] = “:('b1 nty2, 'b1) nty”

val better_MAP = SRULE[sumTheory.FORALL_SUM, GSYM C1_def, GSYM C2_def] MAP_def

Theorem exu[local]:
  (∃!x. P x) ⇔ ∃x. P x ∧ ∀y. P y ⇒ x = y
Proof
  metis_tac[]
QED

Theorem combined_initiality0:
  ∀(f1:'d -> 'c) (f2:('b -> ('d # 'c) option) -> 'c)
   (g1:'c -> 'd) (g2:'c -> 'd -> 'd).
  ∃!(h,k).
    (∀a. h (C1 a) = f1 (k a)) ∧
    (∀b. h (C2 b) = f2 (OPTION_MAP (k ## h) o b)) ∧
    (∀c. k (D1 c) = g1 (h c)) ∧
    (∀d1 d2. k (D2 d1 d2) = g2 (h d1) (k d2))
Proof
  rpt gen_tac >>
  simp[exu, ELIM_UNCURRY, EXISTS_PROD, FORALL_PROD] >>
  qspecl_then [‘f1’, ‘f2’]
              (qx_choose_then ‘eval’ (strip_assume_tac o CONJUNCT1) o
               SRULE [exu])
              better_initiality >>
  qspecl_then [‘g1 o eval’, ‘g2 o eval’]
              (qx_choose_then ‘k’ strip_assume_tac o
               SRULE [exu])
              better_Ginitiality >>
  qexistsl [‘eval o MAP k’, ‘k’] >>
  simp[better_MAP, Excl "o_ASSOC'", o_ASSOC, optMap_O, pairMap_O] >>
  rpt gen_tac >> strip_tac >>
  rename [‘h' (C1 _) = f1 (k' _)’] >>
  ‘h' = eval o MAP k'’
    by (qspecl_then [‘f1 o k'’, ‘λf. f2 (OPTION_MAP (k' ## I) o f)’]
              strip_assume_tac
              (cj 2 $ SRULE[EXISTS_UNIQUE_THM]
                    $ INST_TYPE [“:'b1” |-> beta] better_initiality) >>
        pop_assum irule >>
        simp[better_MAP, Excl "o_ASSOC'", o_ASSOC, optMap_O, pairMap_O]) >>
  gvs[] >>
  ‘k = k'’ by simp[] >>
  gvs[]
QED

(* hide nty1 entirely *)
val mtyrec = newtypeTools.rich_new_type {
  ABS = "mkM", REP = "repM",
  exthm = prove(“∃x:'b NTY. (λy. T) x”, simp_tac bool_ss []),
  tyname = "mty"}

(* which requires tweaking nty2 *)
val ptyrec = newtypeTools.rich_new_type {
  ABS = "mkP", REP = "repP",
  exthm = prove(“∃y: 'b nty2. (λz. T) y”, simp_tac bool_ss []),
  tyname = "pty"}

Definition M1_def:
  M1 n = mkM (C1 (repP n))
End

Definition M2_def:
  M2 (f:'b -> ('b pty # 'b mty) option) =
  mkM (C2 (OPTION_MAP (repP ## repM) o f))
End

Definition P1_def:
  P1 n = mkP (D1 (repM n))
End

Definition P2_def:
  P2 m p = mkP (D2 (repM m) (repP p))
End

Theorem o_REPEQ:
  (f o repM = f' ⇔ f = f' o mkM) ∧
  (g o repP = g' ⇔ g = g' o mkP) ∧
  repP o mkP = I ∧ repM o mkM = I
Proof
  simp[FUN_EQ_THM, EQ_IMP_THM, #absrep_id mtyrec, #absrep_id ptyrec] >>
  metis_tac[#repabs_pseudo_id mtyrec, #repabs_pseudo_id ptyrec]
QED

Theorem combined_initiality:
  ∀(f1:'d -> 'c) (f2:('b -> ('d # 'c) option) -> 'c)
   (g1:'c -> 'd) (g2:'c -> 'd -> 'd).
  ∃!(h,k).
    (∀p. h (M1 p) = f1 (k p)) ∧
    (∀b. h (M2 b) = f2 (OPTION_MAP (k ## h) o b)) ∧
    (∀m. k (P1 m) = g1 (h m)) ∧
    (∀m p. k (P2 m p) = g2 (h m) (k p))
Proof
  rpt gen_tac >>
  qspecl_then [‘f1’, ‘f2’, ‘g1’, ‘g2’] strip_assume_tac
              combined_initiality0 >>
  gvs[exu, ELIM_UNCURRY, EXISTS_PROD, FORALL_PROD] >>
  rename [‘h0 (C1 _) = f1 (k0 _)’] >>
  qexistsl [‘h0 o repM’, ‘k0 o repP’] >>
  simp[M1_def, M2_def, P1_def, P2_def,
       SIMP_RULE bool_ss [] (#repabs_pseudo_id mtyrec),
       SIMP_RULE bool_ss [] (#repabs_pseudo_id ptyrec),
       Excl "o_ASSOC'", o_ASSOC, optMap_O, pairMap_O,
       o_REPEQ
      ] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >> rw[] >~
  [‘mkM (C1 a) (* sg *)’]
  >- (first_x_assum $ qspec_then ‘mkP a’ mp_tac >>
      simp[#repabs_pseudo_id ptyrec]) >~
  [‘mkM (C2 b) (* sg *)’]
  >- (first_x_assum $ qspec_then ‘OPTION_MAP (mkP ## mkM) o b’ mp_tac >>
      simp[Excl "o_ASSOC'", o_ASSOC, optMap_O, pairMap_O, o_REPEQ, optMap_ID])>~
  [‘mkP (D1 c) (* sg *)’]
  >- metis_tac[#repabs_pseudo_id mtyrec] >>
  metis_tac[#repabs_pseudo_id mtyrec, #repabs_pseudo_id ptyrec]
QED

val _ = app delete_type ["nty", "nty2", "idx", "Gidx"]
val _ = app delete_const ["hom", "alg", "minset", "subalg", "KK", "Fin", "FIN"]
*)
