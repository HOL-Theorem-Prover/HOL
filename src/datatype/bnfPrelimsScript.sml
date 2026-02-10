Theory bnfPrelims[bare]
Ancestors sum pair option pred_set cardinal quotient
Libs HolKernel Parse boolLib BasicProvers simpLib

fun sum_nm s : KernelSig.kernelname = {Thy = "sum", Name = s}
fun pair_nm s : KernelSig.kernelname = {Thy = "pair", Name = s}
fun pnm s : KernelSig.kernelname = {Thy = "bnfPrelims", Name = s}
val T = {Name = "TRUTH", Thy = "bool"} (* placeholder *)

(* ----------------------------------------------------------------------
    some bossLib emulation
   ---------------------------------------------------------------------- *)

fun simp ths = simpLib.ASM_SIMP_TAC (srw_ss()) ths

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

val _ = bnfBase.updateDB (
  “:'a1 + 'a2”,
  bnfBase.bI {
    siblings = [],

    map = “SUM_MAP : ('a1 -> 'c1) -> ('a2 -> 'c2) -> 'a1 + 'a2 -> 'c1 + 'c2”,
    mapID = pnm "sumMap_ID",
    mapO = pnm "sumMap_O",
    mapIMAGE = [pnm "sumMapIMAGE1", pnm "sumMapIMAGE2"],

    set = [“setL : 'a1 + 'a2 -> 'a1 set”, “setR : 'a1 + 'a2 -> 'a2 set”],
    gset =
    “sum$SUM_SET : ('a1 -> 'c set) -> ('a2 -> 'c set) -> 'a1 + 'a2 -> 'c set”,

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
    gset = “pair$PAIR_SET : ('a1 -> 'c set) -> ('a2 -> 'c set) ->
                            ('a1 # 'a2 -> 'c set)”,
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

Theorem fun_bnd1:
  ∀f : 'b1 -> 'a1. fset f ≼ univ(:'b1)
Proof
  simp[cardleq_def] >> gen_tac >> irule SURJ_IMP_INJ >>
  irule_at Any SURJ_IMAGE
QED

val _ = bnfBase.updateDB (
  “:'b1 -> 'a1”,
  bnfBase.bI {
    siblings = [],
    map = “combin$o : ('a1 -> 'c1) -> ('b1 -> 'a1) -> ('b1 -> 'c1)”,
    set = [“λ(f : 'b1 -> 'a1). IMAGE f univ(:'b1) : 'a1 set”],
    gset = “λ(g : 'a1 -> 'c set) (f: 'b1 -> 'a1).
              BIGUNION (IMAGE (g o f) univ(:'b1)) : 'c set”,
    mapID = pnm "funMap_ID",
    mapO = pnm "funMap_O",
    mapIMAGE = [pnm "funMapIMAGE1"],
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
