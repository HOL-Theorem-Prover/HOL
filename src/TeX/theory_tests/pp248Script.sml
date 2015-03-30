open HolKernel boolLib foo248Theory bagTheory
val _ = new_theory"pp248"
val _ = TeX_notation{hol="<:", TeX=("\\ensuremath{\\lessdot}",1)}
val _ = export_theory()
