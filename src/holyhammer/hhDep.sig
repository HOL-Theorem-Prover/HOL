signature hhDep =
sig

  val thm_of_depid    : Dep.depid -> (string * Thm.thm)
  val exists_depid    : Dep.depid -> bool

end
