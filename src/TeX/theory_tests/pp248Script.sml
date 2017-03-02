open HolKernel boolLib foo248Theory bag248Theory
val _ = new_theory"pp248"
val _ = TeX_notation{hol="<:", TeX=("\\ensuremath{\\le}",1)}
val _ = TeX_notation{hol="⋲", TeX=("\\ensuremath{\\lessdot}",1)} (* UOK *)
val _ = export_theory()
