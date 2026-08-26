Theory bnfPrelims[bare]
Ancestors sum pair option pred_set cardinal quotient
Libs HolKernel Parse boolLib BasicProvers simpLib TotalDefn[qualified] QLib
     metisLib


fun sum_nm s : KernelSig.kernelname = {Thy = "sum", Name = s}
fun pair_nm s : KernelSig.kernelname = {Thy = "pair", Name = s}
fun pnm s : KernelSig.kernelname = {Thy = "bnfPrelims", Name = s}
val T = {Name = "TRUTH", Thy = "bool"} (* placeholder *)

(* ----------------------------------------------------------------------
    some bossLib emulation
   ---------------------------------------------------------------------- *)

fun simp ths = simpLib.ASM_SIMP_TAC (srw_ss()) ths
val metis_tac = METIS_TAC
val op >~ = Q.>~

(* ----------------------------------------------------------------------
    Utility results that all constructions will likely use
   ---------------------------------------------------------------------- *)

Theorem IMAGE_o_equal:
  IMAGE f o (=) = (=) o f
Proof
  simp[FUN_EQ_THM, IN_DEF, EQ_SYM_EQ]
QED

Theorem KlamF:
  K (λx. F) = K {}
Proof
  simp[FUN_EQ_THM]
QED

Theorem o_INTRO:
  (∀x. f (g x) = h x) ⇔ f o g = h
Proof
  simp[combinTheory.o_DEF, FUN_EQ_THM]
QED

Theorem UNION_CARDLE:
  INFINITE CC ∧ A ≼ CC ∧ B ≼ CC ⇒ A ∪ B ≼ CC
Proof
  strip_tac >>
  resolve_then Any irule UNION_LE_ADD_C cardleq_TRANS >>
  irule CARD_ADD2_ABSORB_LE >> simp[]
QED

Theorem IN_equal:
  x ∈ (=) y ⇔ x = y
Proof
  simp[IN_DEF, EQ_SYM_EQ]
QED

(* not generally safe as an unbounded rewrite *)
Theorem EQ_SING:
  $= x = {x}
Proof
  simp[EXTENSION, IN_equal]
QED

Theorem SING_CARDLE:
  ({x} ≼ A ⇔ A ≠ ∅) ∧ ((=) x ≼ A ⇔ A ≠ ∅)
Proof
  ‘(=) x = {x}’ by MATCH_ACCEPT_TAC EQ_SING >> simp[] >>
  simp[EQ_IMP_THM, INJ_DEF, cardleq_def, GSYM MEMBER_NOT_EMPTY] >>
  rpt strip_tac >~
  [‘∃f. f x ∈ A’, ‘a ∈ A (* a *)’]
  >- (qexists_tac ‘K a’ >> simp[]) >>
  first_assum $ irule_at Any
QED

Theorem IMAGE_KEMPTY_CARDLE:
  IMAGE (K ∅) A ≼ B ⇔ A = ∅ ∨ B ≠ ∅
Proof
  simp[EQ_IMP_THM, DISJ_IMP_THM] >> Cases_on ‘A = ∅’ >> simp[] >>
  Cases_on ‘B = ∅’ >> simp[] >>
  ‘IMAGE (K ∅) A = {∅}’
    by (simp[Once EXTENSION] >> simp[EQ_IMP_THM, PULL_EXISTS] >>
        RULE_ASSUM_TAC (REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) >>
        simp[]) >>
  simp[SING_CARDLE]
QED

Theorem UNIQUE_SKOLEM:
  (∀x. ∃!y. P x y) ⇔ ∃!f. ∀x. P x (f x)
Proof
  eq_tac >> simp[EXISTS_UNIQUE_THM] >> rpt strip_tac
  >- (qexists_tac ‘λx. @y. P x y’ >> simp[] >> gen_tac >> SELECT_ELIM_TAC >>
      METIS_TAC[])
  >- (simp[FUN_EQ_THM] >> METIS_TAC[])
  >- METIS_TAC[]
  >- (rename [‘P x a’, ‘P x b’, ‘a = b’] >>
      Cases_on ‘f x = a’
      >- (pop_assum (SUBST_ALL_TAC o SYM) >>
          first_x_assum $ qspecl_then [‘f’, ‘f (| x |-> b |)’] mp_tac >>
          simp[combinTheory.APPLY_UPDATE_THM] >>
          disch_then irule >> METIS_TAC[]) >>
      first_x_assum $ qspecl_then [‘f(|x|->a|)’, ‘f’] mp_tac >>
      simp[combinTheory.APPLY_UPDATE_THM, FUN_EQ_THM] >> METIS_TAC[])
QED

Overload BIMG = “(o) BIGUNION o IMAGE”

Theorem BIMG_EQUAL:
  BIMG $= = I
Proof
  ONCE_REWRITE_TAC[FUN_EQ_THM] >>
  simp[Once EXTENSION, PULL_EXISTS, IN_equal]
QED

Theorem BIMG_EQUAL_L:
  BIGUNION o IMAGE $= o f = f
Proof
  simp[Once FUN_EQ_THM] >>
  simp[Once EXTENSION, PULL_EXISTS, IN_equal]
QED

Theorem BIMG_K0:
  BIMG (K ∅) = K ∅
Proof
  simp[Once FUN_EQ_THM] >> qx_gen_tac ‘A’ >> Cases_on ‘A = {}’ >>
  simp[EXTENSION] >> METIS_TAC[MEMBER_NOT_EMPTY]
QED

Theorem BIMG_IMAGE:
  BIMG (λx. IMAGE f (g x)) A = IMAGE f (BIMG g A)
Proof
  simp[Once EXTENSION, PULL_EXISTS] >> METIS_TAC[]
QED

Theorem SKg_thm:
  S (K v) g = v o g
Proof
  simp[FUN_EQ_THM]
QED

Theorem UNION_EMPTY1:
  (UNION) {} = I
Proof
  simp[Once FUN_EQ_THM]
QED

Theorem BIMG_IMAGEo:
  BIMG (IMAGE f o g) = IMAGE f o BIMG g
Proof
  CONV_TAC (ONCE_REWRITE_CONV [FUN_EQ_THM]) >>
  simp[Once EXTENSION, PULL_EXISTS, AC CONJ_ASSOC CONJ_COMM] >>
  METIS_TAC[]
QED

Theorem IMAGE_IMAGE_lo:
  (f o IMAGE g) o IMAGE h = f o IMAGE (g o h)
Proof
  simp[FUN_EQ_THM, GSYM IMAGE_o]
QED

Theorem IMAGE_IMAGE_o = REWRITE_RULE [GSYM combinTheory.o_ASSOC] IMAGE_IMAGE_lo

Theorem IMAGE_IMAGE_ro:
  IMAGE g o (IMAGE h o f) = IMAGE (g o h) o f
Proof
  simp[FUN_EQ_THM, PULL_EXISTS]
QED

Theorem BIGUNION_o_IMAGE_IMAGE:
  BIGUNION o IMAGE (IMAGE f o g) = IMAGE f o BIGUNION o IMAGE g
Proof
  simp[Once FUN_EQ_THM]>> simp[Once EXTENSION, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem BIGUNION_o_IMAGE_IMAGEr:
  BIGUNION o (IMAGE (IMAGE f o g) o h) = IMAGE f o BIGUNION o IMAGE g o h
Proof
  simp[Once FUN_EQ_THM]>> simp[Once EXTENSION, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem IMAGE_BIGUNIONo:
  BIGUNION (IMAGE (IMAGE f o h) A) = IMAGE f (BIGUNION (IMAGE h A))
Proof
  simp[Once EXTENSION, PULL_EXISTS, AC CONJ_ASSOC CONJ_COMM] >>
  metis_tac[]
QED


(* ----------------------------------------------------------------------
    Results supporting the compositional derivation of a composite
    functor's nonemptiness witnesses, and of the fact that it is not
    constant (i.e., that its set function is not always empty).
   ---------------------------------------------------------------------- *)

Theorem K0_EMPTY:
  ∀x:'b. (K ∅ : 'b -> 'a set) x = ∅
Proof
  simp[]
QED

Theorem EMPTY_ALL:
  ∀s:'b -> 'a set. ∀w. w ∈ (∅ : 'b set) ⇒ s w = ∅
Proof
  simp[]
QED

Theorem SING_ALL:
  ∀(s:'b -> 'a set) a. s a = ∅ ⇒ ∀w. w ∈ {a} ⇒ s w = ∅
Proof
  simp[]
QED

Theorem BIMGo_EMPTY:
  ∀s st x W. st x ⊆ W ∧ (∀w. w ∈ W ⇒ s w = ∅) ⇒ (BIMG s o st) x = ∅
Proof
  simp[EXTENSION, PULL_EXISTS, SUBSET_DEF] >> metis_tac[NOT_IN_EMPTY]
QED

Theorem LU_EMPTY:
  ∀a b x. a x = ∅ ∧ b x = ∅ ⇒ S ($UNION o a) b x = ∅
Proof
  simp[combinTheory.S_THM]
QED

Theorem EQ_NONEMPTY:
  ∀x:'a. $= x ≠ ∅
Proof
  simp[EXTENSION, IN_equal] >> metis_tac[]
QED

Theorem BIMGo_NONEMPTY:
  ∀s st x t. t ∈ st x ∧ s t ≠ ∅ ⇒ (BIMG s o st) x ≠ ∅
Proof
  simp[EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Theorem LU_NONEMPTY1:
  ∀a b x. a x ≠ ∅ ⇒ S ($UNION o a) b x ≠ ∅
Proof
  simp[combinTheory.S_THM, EXTENSION] >> metis_tac[]
QED

Theorem LU_NONEMPTY2:
  ∀a b x. b x ≠ ∅ ⇒ S ($UNION o a) b x ≠ ∅
Proof
  simp[combinTheory.S_THM, EXTENSION] >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    record the sum type's Bounded Natural Functor nature
   ---------------------------------------------------------------------- *)

Theorem sumMap_def[unlisted] =
        SUM_MAP_def
        |> INST_TYPE [alpha |-> “:'a1”, beta |-> “:'a2”,
                      gamma |-> “:'c1”, delta |-> “:'c2”]

Theorem sumMap_ID[unlisted] =
        SUM_MAP_I
        |> INST_TYPE [alpha |-> “:'a1”, beta |-> “:'a2”]

Theorem sumMap_O[unlisted] =
        SUM_MAP_o
        |> INST_TYPE [alpha |-> “:'a1”, beta |-> “:'a2”,
                      gamma |-> “:'d1”, delta |-> “:'d2”,
                      “:'e” |-> “:'c1”, “:'f” |-> “:'c2”
                     ]
        |> Q.INST [‘f’ |-> ‘f1’, ‘g’ |-> ‘f2’,
                   ‘h’ |-> ‘g1’, ‘k’ |-> ‘g2’]

Theorem sumMapIMAGE1:
  ∀f1 f2 s.
    setL (SUM_MAP (f1:'a1 -> 'c1) (f2:'a2 -> 'c2) (s:'a1 + 'a2)) =
    IMAGE f1 (setL s)
Proof
  GEN_TAC >> GEN_TAC >> Cases_on ‘s’ >>
  SIMP_TAC (srw_ss()) [EXTENSION]
QED

Theorem sumMapIMAGE2:
  ∀f1 f2 s.
    setR (SUM_MAP (f1:'a1 -> 'c1) (f2:'a2 -> 'c2) (s:'a1 + 'a2)) =
    IMAGE f2 (setR s)
Proof
  GEN_TAC >> GEN_TAC >> Cases_on ‘s’ >>
  SIMP_TAC (srw_ss()) [EXTENSION]
QED

Theorem sumMapCONG =
        sumTheory.SUM_MAP_CONG
          |> INST_TYPE [alpha |-> “:'a1”, beta |-> “:'a2”,
                        gamma |-> “:'c1”, delta |-> “:'c2”]

Theorem sum_bnd1:
  ∀s : 'a + 'b. setL s ≼ univ(:num)
Proof
  GEN_TAC >> Cases_on ‘s’ >> simp[cardleq_def, INJ_DEF]
QED

Theorem sum_bnd2:
  ∀s : 'a + 'b. setR s ≼ univ(:num)
Proof
  GEN_TAC >> Cases_on ‘s’ >> simp[cardleq_def, INJ_DEF]
QED

Theorem sum_wit1:
  ∀(a1:'a1) (a2:'a2).
    setL ((K o INL) a1 a2 : 'a1 + 'a2) ⊆ {a1} ∧
    setR ((K o INL) a1 a2 : 'a1 + 'a2) ⊆ ∅
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

Theorem sum_wit2:
  ∀(a1:'a1) (a2:'a2).
    setL (K INR a1 a2 : 'a1 + 'a2) ⊆ ∅ ∧
    setR (K INR a1 a2 : 'a1 + 'a2) ⊆ {a2}
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

Theorem sum_inh1:
  ∀v:'a1. v ∈ setL (INL v : 'a1 + 'a2)
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

Theorem sum_inh2:
  ∀v:'a2. v ∈ setR (INR v : 'a1 + 'a2)
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

val _ = bnfBase.updateDB (
  {Name = "sum", Thy = "sum"},
  bnfBase.bI {
    bnd = “UNIV : num set”,
    bndthms = [pnm "sum_bnd1", pnm "sum_bnd2"],
    canontype = “:'a1 + 'a2”,

    map = “SUM_MAP : ('a1 -> 'c1) -> ('a2 -> 'c2) -> 'a1 + 'a2 -> 'c1 + 'c2”,
    mapID = pnm "sumMap_ID",
    mapO = pnm "sumMap_O",
    mapIMAGE = [pnm "sumMapIMAGE1", pnm "sumMapIMAGE2"],
    mapCONG = pnm "sumMapCONG",

    relator = “SUM_REL : ('a1 -> 'c1 -> bool) -> ('a2 -> 'c2 -> bool) ->
                         'a1 + 'a2 -> 'c1 + 'c2 -> bool”,
    set = [“setL : 'a1 + 'a2 -> 'a1 set”, “setR : 'a1 + 'a2 -> 'a2 set”],
    siblings = [],

    wits = [(“(K o INL) : 'a1 -> 'a2 -> 'a1 + 'a2”, pnm "sum_wit1"),
            (“K INR : 'a1 -> 'a2 -> 'a1 + 'a2”, pnm "sum_wit2")],
    inhabits = [(“INL : 'a1 -> 'a1 + 'a2”, pnm "sum_inh1"),
                (“INR : 'a2 -> 'a1 + 'a2”, pnm "sum_inh2")]
  }
)

(* ----------------------------------------------------------------------
    record the pair type's Bounded Natural Functor nature
   ---------------------------------------------------------------------- *)

Theorem pairMap_ID = PAIR_MAP_I |> INST_TYPE [alpha |-> “:'a1”, beta |-> “:'a2”]

Theorem pairMap_O:
  ((f1:'c1 -> 'd1) ## (f2 : 'c2 -> 'd2)) o
  ((g1:'a1 -> 'c1) ## (g2 : ('a2 -> 'c2))) =
  ((f1 o g1) ## (f2 o g2))
Proof
  simp[FUN_EQ_THM] >> Cases >> simp[]
QED

Theorem pairMapIMAGE1:
  ∀f1 f2 p. setFST (((f1 : 'a1 -> 'c1) ## (f2 : 'a2 -> 'c2)) p) =
            IMAGE f1 (setFST p)
Proof
  Cases_on ‘p’ >> simp[PAIR_MAP_SET, EXTENSION, EQ_SYM_EQ]
QED

Theorem pairMapIMAGE2:
  ∀f1 f2 p. setSND (((f1 : 'a1 -> 'c1) ## (f2 : 'a2 -> 'c2)) p) =
            IMAGE f2 (setSND p)
Proof
  Cases_on ‘p’ >> simp[PAIR_MAP_SET, EXTENSION, EQ_SYM_EQ]
QED

Theorem pairMapCONG:
  (∀a1:'a1. a1 ∈ setFST p ⇒ (f1 : 'a1 -> 'c1) a1 = g1 a1) ∧
  (∀a2:'a2. a2 ∈ setSND p ⇒ (f2 : 'a2 -> 'c2) a2 = g2 a2) ⇒
  (f1 ## f2) p = (g1 ## g2) p
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem pair_bnd1:
  ∀p : 'a1 # 'a2. setFST p ≼ univ(:num)
Proof
  Cases >> simp[cardleq_def, INJ_DEF]
QED

Theorem pair_bnd2:
  ∀p : 'a1 # 'a2. setSND p ≼ univ(:num)
Proof
  Cases >> simp[cardleq_def, INJ_DEF]
QED

Theorem pair_wit1:
  ∀(a1:'a1) (a2:'a2). setFST ($, a1 a2) ⊆ {a1} ∧ setSND ($, a1 a2) ⊆ {a2}
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

Theorem pair_inh1:
  ∀v:'a1. v ∈ setFST (flip $, (ARB:'a2) v)
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

Theorem pair_inh2:
  ∀v:'a2. v ∈ setSND ($, (ARB:'a1) v)
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

val _ = bnfBase.updateDB (
  {Thy = "pair", Name = "prod"},
  bnfBase.bI {
    canontype = “:'a1 # 'a2”,
    siblings = [],

    map = “pair$## : ('a1 -> 'c1) -> ('a2 -> 'c2) -> 'a1 # 'a2 -> 'c1 # 'c2”,
    set = [“setFST : 'a1 # 'a2 -> 'a1 set”, “setSND : 'a1 # 'a2 -> 'a2 set”],
    mapID = pnm "pairMap_ID",
    mapO = pnm "pairMap_O",
    mapIMAGE = [pnm "pairMapIMAGE1", pnm "pairMapIMAGE2"],
    mapCONG = pnm "pairMapCONG",
    relator = “pair$RPROD : ('a1 -> 'c1 -> bool) -> ('a2 -> 'c2 -> bool) ->
                            ('a1 # 'a2 -> 'c1 # 'c2 -> bool)”,
    bnd = “univ(:num)”,
    bndthms = [pnm "pair_bnd1", pnm "pair_bnd2"],

    wits = [(“$, : 'a1 -> 'a2 -> 'a1 # 'a2”, pnm "pair_wit1")],
    inhabits = [(“flip $, (ARB:'a2) : 'a1 -> 'a1 # 'a2”, pnm "pair_inh1"),
                (“$, (ARB:'a1) : 'a2 -> 'a1 # 'a2”, pnm "pair_inh2")]
  }
)

(* ----------------------------------------------------------------------
    record the function type's Bounded Natural Functor nature
      (in its 2nd arg, the range)
   ---------------------------------------------------------------------- *)

Overload fmap[local,inferior] = “$o”
Overload fset[local,inferior] =
  “combin$C IMAGE univ(:'b1) : ('b1 -> 'a1) -> 'a1 set”
Overload frel[local,inferior] =
  “quotient$===> $= : ('a1 -> 'c1 -> bool) ->
                      (('b1 -> 'a1) -> ('b1 -> 'c1) -> bool)”
Theorem funMap_ID:
  fmap (I:'a1 -> 'a1) = I : ('b1 -> 'a1) -> ('b1 -> 'a1)
Proof
  simp[FUN_EQ_THM]
QED

Theorem funMap_O:
  fmap (f1:'c1 -> 'd1) o fmap (g1:'a1 -> 'c1) =
  fmap (f1 o g1) : ('b1 -> 'a1) -> ('b1 -> 'd1)
Proof
  simp[FUN_EQ_THM]
QED

Theorem funMapIMAGE1:
  ∀(f : 'a1 -> 'c1) (fn : 'b1 -> 'a1). fset (fmap f fn) = IMAGE f (fset fn)
Proof
  simp[EXTENSION, PULL_EXISTS]
QED

Theorem funMapCONG:
  (∀a1. a1 ∈ fset (fn : 'b1 -> 'a1) ⇒ ((f1 : 'a1 -> 'c1) a1 = g1 a1)) ⇒
  fmap f1 fn = fmap g1 fn
Proof
  simp[EXTENSION, PULL_EXISTS, FUN_EQ_THM]
QED

Theorem fun_bnd1:
  ∀f : 'b1 -> 'a1. fset f ≼ univ(:'b1)
Proof
  simp[cardleq_def] >> gen_tac >> irule SURJ_IMP_INJ >>
  irule_at Any SURJ_IMAGE
QED

Theorem fun_wit1:
  ∀a1:'a1. fset (K a1 : 'b1 -> 'a1) ⊆ {a1}
Proof
  simp[SUBSET_DEF, PULL_EXISTS, IN_DEF]
QED

Theorem fun_inh1:
  ∀v:'a1. v ∈ fset (K v : 'b1 -> 'a1)
Proof
  simp[SUBSET_DEF, EXTENSION, IN_DEF]
QED

val _ = bnfBase.updateDB (
  {Thy = "min", Name = "fun"},
  bnfBase.bI {
    canontype = “:'b1 -> 'a1”,
    siblings = [],
    map = “combin$o : ('a1 -> 'c1) -> ('b1 -> 'a1) -> ('b1 -> 'c1)”,
    set = [“fset: ('b1 -> 'a1) -> 'a1 set”],
    mapID = pnm "funMap_ID",
    mapO = pnm "funMap_O",
    mapIMAGE = [pnm "funMapIMAGE1"],
    mapCONG = pnm "funMapCONG",
    relator = “quotient$===> $= : ('a1 -> 'c1 -> bool) ->
                                  (('b1 -> 'a1) -> ('b1 -> 'c1) -> bool)”,
    bnd = “univ(:'b1)”,
    bndthms = [pnm "fun_bnd1"],

    wits = [(“K : 'a1 -> 'b1 -> 'a1”, pnm "fun_wit1")],
    inhabits = [(“K : 'a1 -> 'b1 -> 'a1”, pnm "fun_inh1")]
  }
)

Theorem frel_thm[local]:
  frel (R:'a1 -> 'a2 -> bool) (f1:'b1 -> 'a1) (f2:'b1 -> 'a2) ⇔
    ∃f. f1 = fmap FST f ∧ f2 = fmap SND f ∧
        ∀x y. (x,y) ∈ fset f ⇒ R x y
Proof
  simp[FUN_REL, PULL_EXISTS] >> iff_tac
  >- (strip_tac >> Q.EXISTS_TAC ‘λb. (f1 b, f2 b)’ >> simp[FUN_EQ_THM]) >>
  SRW_TAC[][combinTheory.o_DEF] >> simp[] >> Q.RENAME_TAC [‘FST (f b)’] >>
  Cases_on ‘f b’ >> simp[] >> first_x_assum irule >>
  first_x_assum (irule_at Any o SYM)
QED

(* ----------------------------------------------------------------------
    record the option type's Bounded Natural Functor nature
   ---------------------------------------------------------------------- *)

Theorem optMap_ID:
  OPTION_MAP (I:'a1 -> 'a1) = I : 'a1 option -> 'a1 option
Proof
  simp[FUN_EQ_THM]
QED

Theorem optMap_O:
  OPTION_MAP (f1:'c1 -> 'd1) o OPTION_MAP (g1:'a1 -> 'c1) =
  OPTION_MAP (f1 o g1) : 'a1 option -> 'd1 option
Proof
  simp[FUN_EQ_THM] >> Cases >> simp[]
QED

Definition optSET_def:
  optSET NONE = {} ∧
  optSET (SOME x) = {x}
End

Theorem optMapIMAGE1:
  ∀(f : 'a1 -> 'c1) (x : 'a1 option).
    optSET (OPTION_MAP f x) = IMAGE f (optSET x)
Proof
  Cases_on ‘x’ >> simp[EXTENSION, PULL_EXISTS, optSET_def]
QED

Theorem optMapCONG:
  (∀a1. a1 ∈ optSET (x : 'a1 option) ⇒ ((f1 : 'a1 -> 'c1) a1 = g1 a1)) ⇒
  OPTION_MAP f1 x = OPTION_MAP g1 x
Proof
  Cases_on ‘x’ >> simp[optSET_def]
QED

Theorem opt_bnd1:
  ∀x : 'a1 option. optSET x ≼ univ(:num)
Proof
  Cases >> simp[cardleq_def, optSET_def, INJ_DEF]
QED

Theorem opt_wit1:
  ∀a1:'a1. optSET (K NONE a1 : 'a1 option) ⊆ ∅
Proof
  simp[optSET_def, SUBSET_DEF, EXTENSION, IN_DEF]
QED

Theorem opt_wit2:
  ∀a1:'a1. optSET (SOME a1) ⊆ {a1}
Proof
  simp[optSET_def, SUBSET_DEF, EXTENSION, IN_DEF]
QED

Theorem opt_inh1:
  ∀v:'a1. v ∈ optSET (SOME v)
Proof
  simp[optSET_def, SUBSET_DEF, EXTENSION, IN_DEF]
QED

val _ = bnfBase.updateDB (
  {Thy = "option", Name = "option"},
  bnfBase.bI {
    canontype = “:'a1 option”,
    siblings = [],
    map = “option$OPTION_MAP : ('a1 -> 'c1) -> 'a1 option -> 'c1 option”,
    set = [“optSET : 'a1 option -> 'a1 set”],
    mapID = pnm "optMap_ID",
    mapO = pnm "optMap_O",
    mapIMAGE = [pnm "optMapIMAGE1"],
    mapCONG = pnm "optMapCONG",
    relator = “option$OPTREL : ('a1 -> 'c1 -> bool) ->
                               ('a1 option -> 'c1 option -> bool)”,
    bnd = “univ(:num)”,
    bndthms = [pnm "opt_bnd1"],

    wits = [(“K NONE : 'a1 -> 'a1 option”, pnm "opt_wit1"),
            (“SOME : 'a1 -> 'a1 option”, pnm "opt_wit2")],
    inhabits = [(“SOME : 'a1 -> 'a1 option”, pnm "opt_inh1")]
  }
)

Theorem optrel_thm[local]:
  OPTREL (R:'a1 -> 'a2 -> bool) (x1:'a1 option) (x2:'a2 option) ⇔
    ∃x:('a1#'a2) option.
      x1 = OPTION_MAP FST x ∧ x2 = OPTION_MAP SND x ∧
      ∀a b. (a,b) ∈ optSET x ⇒ R a b
Proof
  Cases_on ‘x1’ >> Cases_on ‘x2’ >> simp[OPTREL_def, PULL_EXISTS, optSET_def] >>
  iff_tac
  >- (strip_tac >> Q.RENAME_TAC [‘a = FST _ ∧ b = SND _ ∧ _’] >>
      Q.EXISTS_TAC ‘(a,b)’ >> simp[]) >>
  simp[pairTheory.EXISTS_PROD]
QED

(* ----------------------------------------------------------------------
    Results supporting the compositional derivation of bounds for
    composite functors.

    A composite functor's set-function is built (see bnfLib) out of

       $=                     (at the functor's own argument)
       K ∅                    (at argument-free positions)
       BIMG s ∘ set           (descending through a component functor)
       S ($UNION ∘ s₁) s₂     (combining a component's various arguments)

    so a bound for the composite follows from bounds for the pieces, as
    long as the bound is infinite.  The results below are the four cases.
   ---------------------------------------------------------------------- *)

Theorem EQ_CARDLE:
  ∀B. B ≠ ∅ ⇒ ∀x:'a. $= x ≼ B
Proof
  simp[SING_CARDLE]
QED

Theorem CARDEQ_IMP_CARDLEQ:
  ∀s t. s ≈ t ⇒ s ≼ t
Proof
  metis_tac[cardleq_lteq]
QED

Theorem CARDLEQ_INFINITE:
  ∀s t. INFINITE s ∧ s ≼ t ⇒ INFINITE t
Proof
  metis_tac[CARD_LE_FINITE]
QED

Theorem INFINITE_NOT_EMPTY:
  ∀B. INFINITE B ⇒ B ≠ ∅
Proof
  metis_tac[FINITE_EMPTY]
QED

Theorem K0_CARDLE:
  ∀B x:'b. (K ∅ : 'b -> 'a set) x ≼ B
Proof
  simp[]
QED

Theorem LU_CARDLE:
  ∀B f1 f2.
    INFINITE B ∧ (∀x. f1 x ≼ B) ∧ (∀x. f2 x ≼ B) ⇒
    ∀x. S ($UNION o f1) f2 x ≼ B
Proof
  rpt gen_tac >> strip_tac >> simp[combinTheory.S_THM] >> gen_tac >>
  irule UNION_CARDLE >> simp[]
QED

Theorem BIMGo_CARDLE:
  ∀B g st.
    INFINITE B ∧ (∀y. g y ≼ B) ∧ (∀x. st x ≼ B) ⇒
    ∀x. (BIMG g o st) x ≼ B
Proof
  rpt gen_tac >> strip_tac >> simp[combinTheory.o_THM] >> gen_tac >>
  irule CARD_BIGUNION >> simp[PULL_EXISTS] >>
  irule IMAGE_cardleq_rwt >> simp[]
QED

(* ----------------------------------------------------------------------
    ... and the results used to see that a component functor's own bound
    is dominated by the composite's, which is always of the form
    univ(:num + τ₁ + ... + τₙ)
   ---------------------------------------------------------------------- *)

Theorem UNIV_CARD_LE_ADDR:
  univ(:'a) ≼ univ(:'a + 'b)
Proof
  simp[disjUNION_UNIV, CARD_LE_ADDR]
QED

Theorem UNIV_CARD_LE_ADDL:
  univ(:'b) ≼ univ(:'a + 'b)
Proof
  simp[disjUNION_UNIV, CARD_LE_ADDL]
QED

Theorem INFINITE_num_sum[simp]:
  INFINITE univ(:num + 'a)
Proof
  ‘INJ INL univ(:num) univ(:num + 'a)’ by simp[INJ_DEF] >>
  metis_tac[INFINITE_INJ, num_INFINITE]
QED

Theorem UNIV_NUM_NOT_EMPTY[simp]:
  univ(:num) ≠ ∅
Proof
  simp[EXTENSION]
QED

(* ----------------------------------------------------------------------
    Results supporting the compositional derivation of the map/set laws
    for a composite functor.  Each result handles one node of the
    composite's set-function (see bnfLib): the functor's own argument
    ($=), an argument-free position (K ∅), a descent through a component
    functor (BIMG s ∘ set), and the combination of a component's various
    arguments (S ($UNION ∘ s₁) s₂).
   ---------------------------------------------------------------------- *)

Theorem EQ_natural:
  ∀f:'a -> 'b. $= o f = IMAGE f o $=
Proof
  MATCH_ACCEPT_TAC (GSYM IMAGE_o_equal)
QED

Theorem K0_natural:
  ∀f:'a -> 'b.
    (K ∅ : 'c -> 'b set) o (I:'c -> 'c) = IMAGE f o (K ∅ : 'c -> 'a set)
Proof
  simp[FUN_EQ_THM]
QED

Theorem BIMG_o_natural:
  ∀stB stA sB sA mp h f.
    stB o mp = IMAGE h o stA ∧ sB o h = IMAGE f o sA ⇒
    (BIMG sB o stB) o mp = IMAGE f o (BIMG sA o stA)
Proof
  rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once FUN_EQ_THM, combinTheory.o_THM]) >>
  CONV_TAC (ONCE_REWRITE_CONV [FUN_EQ_THM]) >>
  simp[combinTheory.o_THM, IMAGE_IMAGE, combinTheory.o_DEF, IMAGE_BIGUNION]
QED

Theorem LU_natural:
  ∀aB aA bB bA mp f.
    aB o mp = IMAGE f o aA ∧ bB o mp = IMAGE f o bA ⇒
    S ($UNION o aB) bB o mp = IMAGE f o S ($UNION o aA) bA
Proof
  rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once FUN_EQ_THM, combinTheory.o_THM]) >>
  CONV_TAC (ONCE_REWRITE_CONV [FUN_EQ_THM]) >>
  simp[combinTheory.o_THM, combinTheory.S_THM, IMAGE_UNION]
QED

Theorem EQ_CONG:
  ∀f g x. (∀a. a ∈ $= x ⇒ f a = g a) ⇒ f x = g x
Proof
  simp[IN_DEF]
QED

Theorem BIMG_o_CONG_hyp:
  ∀sA stA x y f g.
    (∀a. a ∈ (BIMG sA o stA) x ⇒ f a = g a) ∧ y ∈ stA x ⇒
    ∀a. a ∈ sA y ⇒ f a = g a
Proof
  rpt strip_tac >> first_x_assum irule >> simp[PULL_EXISTS] >>
  metis_tac[]
QED

Theorem LU_CONG_hyp:
  ∀aA bA x f g.
    (∀a. a ∈ S ($UNION o aA) bA x ⇒ f a = g a) ⇒
    (∀a. a ∈ aA x ⇒ f a = g a) ∧ (∀a. a ∈ bA x ⇒ f a = g a)
Proof
  simp[combinTheory.S_THM] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED
