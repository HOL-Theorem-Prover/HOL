open PFTMerge

val () = merge {
  inputs = List.map(fn s => s^".pft.bin") [
   "bool", "marker", "num", "sat", "combin",
   "relation", "prim_rec", "quotient", "pair",
   "arithmetic"],
  targets = [ThyAll ("arithmetic",false)],
  output = "merged.pft.bin",
  binary = true
};
