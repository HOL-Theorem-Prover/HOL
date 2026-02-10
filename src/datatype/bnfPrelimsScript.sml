Theory bnfPrelims[bare]
Ancestors sum pair option pred_set cardinal
Libs HolKernel Parse boolLib BasicProvers simpLib

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

fun sum_nm s : KernelSig.kernelname = {Thy = "sum", Name = s}
fun pnm s : KernelSig.kernelname = {Thy = "bnfPrelims", Name = s}
val T = {Name = "TRUTH", Thy = "bool"} (* placeholder *)

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
