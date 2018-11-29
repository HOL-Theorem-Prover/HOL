signature HM_Cline =
sig

type t = {
  holstate : string option,
  multithread : int option,
  poly : string option,
  polymllibdir : string option,
  poly_not_hol : bool,
  relocbuild : bool,
  time_limit : Time.time option,
  core : HM_Core_Cline.t
}

val option_descriptions : t HM_Core_Cline.cline_result GetOpt.opt_descr list
val fupd_core : (HM_Core_Cline.t -> HM_Core_Cline.t) -> (t -> t)
val default_options : t

end
