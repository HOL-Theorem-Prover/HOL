signature inline =
sig
  include Abbrev
  val threshold : int ref
  val unroll_limit : int ref

  val size : term -> int
  val identify_small_fun : term -> term
  val once_expand_anonymous : thm -> thm
  val expand_anonymous : thm -> thm
  val mk_inline_rules : thm list -> thm list
  val expand_named : thm list -> thm -> thm
  val optimize : thm -> thm
  val optimize_norm : thm list -> thm -> thm
end