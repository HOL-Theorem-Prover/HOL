Theory refuteHarvestTheorem
Ancestors
  refuteHarvestRep

open refuteHarvestTypeTheory refuteHarvestAbsTheory
     refuteHarvestRepTheory

Theorem refute_harvest_split_absrep:
  (!x. refute_harvest_split_abs (refute_harvest_split_rep x) = x) /\
  (!n. (\n. n < 2) n =
       (refute_harvest_split_rep (refute_harvest_split_abs n) = n))
Proof
  simp [refute_harvest_split_abs_def, refute_harvest_split_rep_def,
        refute_harvest_split_home_absrep_1,
        refute_harvest_split_home_absrep_2]
QED
