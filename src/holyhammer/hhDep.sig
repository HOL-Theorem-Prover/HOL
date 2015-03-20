signature hhDep =
sig

  val thm_of_depid    : Dep.depid -> (string * Thm.thm)
  val thm_of_depconj  : Dep.depconj -> Thm.thm

  val exists_depid    : Dep.depid -> bool
  val exists_depconj  : Dep.depconj -> bool

  val dcl_of_thm      : Thm.thm -> Dep.depconj list
  val deptree_of_thm  : Thm.thm -> Dep.deptree

  (* specific to holyhammer *)
  val hh_fetch_conj   : (Thm.thm * string) -> Thm.thm
  val string_of_dcl   : Dep.depconj list -> string

end
