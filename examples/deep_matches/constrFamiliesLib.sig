signature constrFamiliesLib =
sig
  include Abbrev

  val gen_case_expand_thm : thm -> thm -> thm

  val get_case_expand_thm : term * ((term list * term) list) ->
     thm

end
