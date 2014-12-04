signature constrFamiliesLib =
sig
  include Abbrev

  val gen_case_expand_thm : thm -> thm -> thm
end
