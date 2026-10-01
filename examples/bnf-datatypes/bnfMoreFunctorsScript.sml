Theory bnfMoreFunctors
Ancestors
  bnfPrelims finite_map list pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase

(* ----------------------------------------------------------------------
    Register finite maps and lists as bounded natural functors, so that a
    datatype specification can recurse through them.

    These belong in src/finite_maps and src/list eventually; they are
    here while the package is being developed, because that keeps the
    core build out of it.
   ---------------------------------------------------------------------- *)

fun mnm s : KernelSig.kernelname = {Thy = "bnfMoreFunctors", Name = s}

Theorem FINITE_cle_num:
  ∀s:'a set. FINITE s ⇒ s ≼ univ(:num)
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[cardleq_lteq] >> disj1_tac >>
  simp[GSYM FINITE_CARD_LT]
QED

(* ----------------------------------------------------------------------
    finite maps, functorial in their range
   ---------------------------------------------------------------------- *)

Theorem fmapMap_ID:
  $o_f (I:'a1 -> 'a1) = (I : ('b1 |-> 'a1) -> ('b1 |-> 'a1))
Proof
  simp[FUN_EQ_THM, combinTheory.I_EQ_IDABS]
QED

Theorem fmapMap_O:
  $o_f (f1:'c1 -> 'd1) o $o_f (g1:'a1 -> 'c1) =
  ($o_f (f1 o g1) : ('b1 |-> 'a1) -> ('b1 |-> 'd1))
Proof
  simp[FUN_EQ_THM]
QED

Theorem fmapMapIMAGE1:
  ∀(f1:'a1 -> 'c1) (m:'b1 |-> 'a1). FRANGE (f1 o_f m) = IMAGE f1 (FRANGE m)
Proof
  simp[IMAGE_FRANGE]
QED

Theorem fmapMapCONG:
  (∀a1. a1 ∈ FRANGE (m : 'b1 |-> 'a1) ⇒ (f1:'a1 -> 'c1) a1 = g1 a1) ⇒
  f1 o_f m = g1 o_f m
Proof
  strip_tac >> irule o_f_cong >> simp[]
QED

Theorem fmap_bnd1:
  ∀m : 'b1 |-> 'a1. FRANGE m ≼ univ(:num)
Proof
  gen_tac >> irule FINITE_cle_num >> simp[]
QED

Theorem fmap_wit1:
  ∀a1:'a1. FRANGE (K FEMPTY a1 : 'b1 |-> 'a1) ⊆ ∅
Proof
  simp[]
QED

Theorem fmap_inh1:
  ∀v:'a1. v ∈ FRANGE ((FUPDATE FEMPTY o $, (ARB:'b1)) v)
Proof
  simp[FRANGE_FUPDATE]
QED

val _ = bnfBase.updateDB (
  {Thy = "finite_map", Name = "fmap"},
  bnfBase.bI {
    canontype = “:'b1 |-> 'a1”,
    siblings = [],

    map = “$o_f : ('a1 -> 'c1) -> ('b1 |-> 'a1) -> ('b1 |-> 'c1)”,
    set = [“FRANGE : ('b1 |-> 'a1) -> 'a1 set”],
    mapID = mnm "fmapMap_ID",
    mapO = mnm "fmapMap_O",
    mapIMAGE = [mnm "fmapMapIMAGE1"],
    mapCONG = mnm "fmapMapCONG",

    relator = “fmap_rel : ('a1 -> 'c1 -> bool) ->
                          ('b1 |-> 'a1) -> ('b1 |-> 'c1) -> bool”,
    bnd = “univ(:num)”,
    bndthms = [mnm "fmap_bnd1"],

    wits = [(“K FEMPTY : 'a1 -> ('b1 |-> 'a1)”, mnm "fmap_wit1")],
    inhabits = [(“(FUPDATE FEMPTY o $, (ARB:'b1)) : 'a1 -> ('b1 |-> 'a1)”,
                 mnm "fmap_inh1")]
  }
)

(* ----------------------------------------------------------------------
    lists
   ---------------------------------------------------------------------- *)

Theorem listMap_ID:
  MAP (I:'a1 -> 'a1) = (I : 'a1 list -> 'a1 list)
Proof
  simp[FUN_EQ_THM]
QED

Theorem listMap_O:
  MAP (f1:'c1 -> 'd1) o MAP (g1:'a1 -> 'c1) = MAP (f1 o g1)
Proof
  simp[FUN_EQ_THM, MAP_MAP_o]
QED

Theorem listMapIMAGE1:
  ∀(f1:'a1 -> 'c1) l. set (MAP f1 l) = IMAGE f1 (set l)
Proof
  simp[LIST_TO_SET_MAP]
QED

Theorem listMapCONG:
  (∀a1. a1 ∈ set (l:'a1 list) ⇒ (f1:'a1 -> 'c1) a1 = g1 a1) ⇒
  MAP f1 l = MAP g1 l
Proof
  strip_tac >> irule MAP_CONG >> simp[]
QED

Theorem list_bnd1:
  ∀l : 'a1 list. set l ≼ univ(:num)
Proof
  gen_tac >> irule FINITE_cle_num >> simp[]
QED

Theorem list_wit1:
  ∀a1:'a1. set (K [] a1 : 'a1 list) ⊆ ∅
Proof
  simp[]
QED

Theorem list_inh1:
  ∀v:'a1. v ∈ set (flip CONS [] v)
Proof
  simp[]
QED

val _ = bnfBase.updateDB (
  {Thy = "list", Name = "list"},
  bnfBase.bI {
    canontype = “:'a1 list”,
    siblings = [],

    map = “list$MAP : ('a1 -> 'c1) -> 'a1 list -> 'c1 list”,
    set = [“list$LIST_TO_SET : 'a1 list -> 'a1 set”],
    mapID = mnm "listMap_ID",
    mapO = mnm "listMap_O",
    mapIMAGE = [mnm "listMapIMAGE1"],
    mapCONG = mnm "listMapCONG",

    relator = “LIST_REL : ('a1 -> 'c1 -> bool) -> 'a1 list -> 'c1 list -> bool”,
    bnd = “univ(:num)”,
    bndthms = [mnm "list_bnd1"],

    wits = [(“K [] : 'a1 -> 'a1 list”, mnm "list_wit1")],
    inhabits = [(“(flip CONS []) : 'a1 -> 'a1 list”, mnm "list_inh1")]
  }
)
