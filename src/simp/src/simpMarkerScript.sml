Theory simpMarker[bare]
Ancestors
  marker
Libs
  HolKernel Parse boolLib OpenTheoryMap

val Split_def = new_definition ("Split_def", “Split (x:bool) = x”)
val _ = remove_ovl_mapping "Split" {Name="Split",Thy="simpMarker"}

val ExcludeX_def = new_definition ("ExcludeX_def", “ExcludeX (x:'a) = T”)
val _ = remove_ovl_mapping "ExcludeX" {Name="ExcludeX",Thy="simpMarker"}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const={Thy="simpMarker",Name="Split"}, name=(["Unwanted"],"id")}
