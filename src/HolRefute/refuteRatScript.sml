Theory refuteRat
Ancestors
  refute rat

Definition of_frac_def:
  of_frac q = rat$abs_rat q
End

Theorem of_frac_frac[compute]:
  of_frac (frac a b) = rat$abs_rat (frac$abs_frac (norm_frac a b))
Proof
  simp [of_frac_def, frac_def]
QED
