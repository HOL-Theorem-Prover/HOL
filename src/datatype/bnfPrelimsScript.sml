Theory bnfPrelims[bare]
Ancestors sum pair option pred_set cardinal quotient
Libs HolKernel Parse boolLib BasicProvers simpLib TotalDefn[qualified]

fun sum_nm s : KernelSig.kernelname = {Thy = "sum", Name = s}
fun pair_nm s : KernelSig.kernelname = {Thy = "pair", Name = s}
fun pnm s : KernelSig.kernelname = {Thy = "bnfPrelims", Name = s}
val T = {Name = "TRUTH", Thy = "bool"} (* placeholder *)

(* ----------------------------------------------------------------------
    some bossLib emulation
   ---------------------------------------------------------------------- *)

fun simp ths = simpLib.ASM_SIMP_TAC (srw_ss()) ths

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

Theorem sumMapCONG:
  (∀a1. a1 ∈ setL x ⇒ (f1 : 'a1 -> 'c1) a1 = g1 a1) ∧
  (∀a2. a2 ∈ setR x ⇒ (f2 : 'a2 -> 'c2) a2 = g2 a2) ⇒
  SUM_MAP f1 f2 x = SUM_MAP g1 g2 x
Proof
  Cases_on ‘x’ >> simp[]
QED

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

Theorem sum_gsetmap:
  sum$SUM_SET (f1:'c1 -> 'd set) (f2:'c2 -> 'd set)
  (SUM_MAP (g1:'a1 -> 'c1) (g2:'a2 -> 'c2) s) =
  sum$SUM_SET (f1 o g1) (f2 o g2) s
Proof
  Cases_on ‘s’ >> simp[EXTENSION, SUM_SET_def]
QED

Theorem sum_gsetIMAGE:
  IMAGE (f : 'c -> 'd)
    (sum$SUM_SET (g1 : 'a1 -> 'c set) (g2 : 'a2 -> 'c set) s) =
  sum$SUM_SET (IMAGE f o g1) (IMAGE f o g2) s
Proof
  Cases_on ‘s’ >> simp[SUM_SET_def]
QED


val _ = bnfBase.updateDB (
  “:'a1 + 'a2”,
  bnfBase.bI {
    siblings = [],

    map = “SUM_MAP : ('a1 -> 'c1) -> ('a2 -> 'c2) -> 'a1 + 'a2 -> 'c1 + 'c2”,
    mapID = pnm "sumMap_ID",
    mapO = pnm "sumMap_O",
    mapIMAGE = [pnm "sumMapIMAGE1", pnm "sumMapIMAGE2"],
    mapCONG = pnm "sumMapCONG",

    set = [“setL : 'a1 + 'a2 -> 'a1 set”, “setR : 'a1 + 'a2 -> 'a2 set”],
    gset =
    “sum$SUM_SET : ('a1 -> 'c set) -> ('a2 -> 'c set) -> 'a1 + 'a2 -> 'c set”,
    gsetmap = pnm "sum_gsetmap",
    gsetIMAGE = pnm "sum_gsetIMAGE",

    relator = “SUM_REL : ('a1 -> 'c1 -> bool) -> ('a2 -> 'c2 -> bool) ->
                         'a1 + 'a2 -> 'c1 + 'c2 -> bool”,
    bnd = “UNIV : num set”,
    bndthms = [pnm "sum_bnd1", pnm "sum_bnd2"]
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

Theorem pair_gsetmap:
  pair$PAIR_SET (f1 : 'c1 -> 'd set) (f2: 'c2 -> 'd set)
  (((g1 : 'a1 -> 'c1) ## (g2 : 'a2 -> 'c2)) p) =
  pair$PAIR_SET (f1 o g1) (f2 o g2) p
Proof
  Cases_on ‘p’ >> simp[PAIR_SET_def]
QED

Theorem pair_gsetIMAGE:
  IMAGE (f : 'c -> 'd) (PAIR_SET (g1 : 'a1 -> 'c set) (g2 : 'a2 -> 'c set) p) =
  PAIR_SET (IMAGE f o g1) (IMAGE f o g2) p
Proof
  Cases_on ‘p’ >> simp[PAIR_SET_def, EXTENSION, SF boolSimps.DNF_ss]
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

val _ = bnfBase.updateDB (
  “:'a1 # 'a2”,
  bnfBase.bI {
    siblings = [],
    map = “pair$## : ('a1 -> 'c1) -> ('a2 -> 'c2) -> 'a1 # 'a2 -> 'c1 # 'c2”,
    set = [“setFST : 'a1 # 'a2 -> 'a1 set”, “setSND : 'a1 # 'a2 -> 'a2 set”],
    mapID = pnm "pairMap_ID",
    mapO = pnm "pairMap_O",
    mapIMAGE = [pnm "pairMapIMAGE1", pnm "pairMapIMAGE2"],
    mapCONG = pnm "pairMapCONG",
    gset = “pair$PAIR_SET : ('a1 -> 'c set) -> ('a2 -> 'c set) ->
                            ('a1 # 'a2 -> 'c set)”,
    gsetmap = pnm "pair_gsetmap",
    gsetIMAGE = pnm "pair_gsetIMAGE",
    relator = “pair$RPROD : ('a1 -> 'c1 -> bool) -> ('a2 -> 'c2 -> bool) ->
                            ('a1 # 'a2 -> 'c1 # 'c2 -> bool)”,
    bnd = “univ(:num)”,
    bndthms = [pnm "pair_bnd1", pnm "pair_bnd2"]
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

Definition fun_gset_def:
  fun_gset (g1 : 'a1 -> 'c set) (f: 'b1 -> 'a1) =
  BIGUNION (IMAGE g1 (fset f))
End

Theorem fun_gsetmap:
  fun_gset (g1 : 'c1 -> 'd set) (fmap (f1 : 'a1 -> 'c1) (fn:'b1 -> 'a1)) =
  fun_gset (g1 o f1) fn
Proof
  simp[fun_gset_def, IMAGE_IMAGE]
QED

Theorem fun_gsetIMAGE:
  IMAGE (f : 'c -> 'd) (fun_gset (g1 : 'a1 -> 'c set) (fn:'b1 -> 'a1)) =
  fun_gset (IMAGE f o g1) fn
Proof
  simp[fun_gset_def, IMAGE_BIGUNION, IMAGE_IMAGE]
QED

val _ = bnfBase.updateDB (
  “:'b1 -> 'a1”,
  bnfBase.bI {
    siblings = [],
    map = “combin$o : ('a1 -> 'c1) -> ('b1 -> 'a1) -> ('b1 -> 'c1)”,
    set = [“fset: ('b1 -> 'a1) -> 'a1 set”],
    gset = “fun_gset : ('a1 -> 'c set) -> ('b1 -> 'a1) -> 'c set”,
    mapID = pnm "funMap_ID",
    mapO = pnm "funMap_O",
    mapIMAGE = [pnm "funMapIMAGE1"],
    mapCONG = pnm "funMapCONG",
    gsetmap = pnm "fun_gsetmap",
    gsetIMAGE = pnm "fun_gsetIMAGE",
    relator = “quotient$===> $= : ('a1 -> 'c1 -> bool) ->
                                  (('b1 -> 'a1) -> ('b1 -> 'c1) -> bool)”,
    bnd = “univ(:'b1)”,
    bndthms = [pnm "fun_bnd1"]
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

Definition opt_gset_def:
  opt_gset (f1:'a1 -> 'c set) (x:'a1 option) = BIGUNION (IMAGE f1 (optSET x))
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

Theorem opt_gsetmap:
  opt_gset (f1 : 'c1 -> 'd set) (OPTION_MAP (g1 : 'a1 -> 'c1) opt) =
  opt_gset (f1 o g1) opt
Proof
  Cases_on ‘opt’ >> simp[opt_gset_def, optSET_def]
QED

Theorem opt_gsetIMAGE:
  IMAGE (f : 'c -> 'd) (opt_gset (g1 : 'a1 -> 'c set) opt) =
  opt_gset (IMAGE f o g1) opt
Proof
  Cases_on ‘opt’ >> simp[opt_gset_def, optSET_def]
QED

Theorem opt_bnd1:
  ∀x : 'a1 option. optSET x ≼ univ(:num)
Proof
  Cases >> simp[cardleq_def, optSET_def, INJ_DEF]
QED

val _ = bnfBase.updateDB (
  “:'a1 option”,
  bnfBase.bI {
    siblings = [],
    map = “option$OPTION_MAP : ('a1 -> 'c1) -> 'a1 option -> 'c1 option”,
    set = [“optSET : 'a1 option -> 'a1 set”],
    gset = “opt_gset : ('a1 -> 'c set) -> 'a1 option -> 'c set”,
    mapID = pnm "optMap_ID",
    mapO = pnm "optMap_O",
    mapIMAGE = [pnm "optMapIMAGE1"],
    mapCONG = pnm "optMapCONG",
    gsetmap = pnm "opt_gsetmap",
    gsetIMAGE = pnm "opt_gsetIMAGE",
    relator = “option$OPTREL : ('a1 -> 'c1 -> bool) ->
                               ('a1 option -> 'c1 option -> bool)”,
    bnd = “univ(:num)”,
    bndthms = [pnm "opt_bnd1"]
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
