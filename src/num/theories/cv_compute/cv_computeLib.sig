signature cv_computeLib =
sig
  include Abbrev
  val cv_compute : thm list -> term -> thm
end

