signature HM_Cline =
sig

type t = {
  no_basis2002 : bool,
  mosmldir : string option,
  core : HM_Core_Cline.t
}

val option_descriptions : t HM_Core_Cline.cline_result GetOpt.opt_descr list
val fupd_core : (HM_Core_Cline.t -> HM_Core_Cline.t) -> (t -> t)
val default_options : t

end
