Theory bnfPrelims[bare]
Ancestors sum pair option pred_set
Libs HolKernel Parse boolLib

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

fun sum_nm s : KernelSig.kernelname = {Thy = "sum", Name = s}
fun pnm s : KernelSig.kernelname = {Thy = "bnfPrelims", Name = s}
val T = {Name = "TRUTH", Thy = "bool"} (* placeholder *)

val _ = bnfBase.updateDB (
  “:'a1 + 'a2”,
  bnfBase.bI {
    siblings = [],

    map = (“SUM_MAP : ('a1 -> 'c1) -> ('a2 -> 'c2) -> 'a1 + 'a2 -> 'c1 + 'c2”,
           pnm "sumMap_def"),
    mapID = pnm "sumMap_ID",
    mapO = pnm "sumMap_O",
    mapIMAGE = [sum_nm "SUM_MAP_SET", sum_nm "SUM_MAP_SET"],

    set = [(“setL”, T), (“setR”, T)],
    gset = (“sum$SUM_SET”, T),

    relator = (“SUM_REL”, sum_nm "SUM_REL_def"),
    bnd = “UNIV : num set”
  }
)
