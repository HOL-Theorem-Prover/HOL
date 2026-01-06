signature pegLib =
sig

include Abbrev

val add_peg_compset : computeLib.compset -> computeLib.compset
val derive_compset_distincts : hol_type -> thm
val derive_lookup_ths :
    {pegth : thm, ntty : hol_type, simp : thm list -> conv} ->
    {lookups : thm list, fdom_thm : thm, applieds : thm list}

end
