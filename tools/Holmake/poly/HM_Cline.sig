signature HM_Cline =
sig

type t = {
  holstate : string option,
  poly : string option,
  polymllibdir : string option,
  poly_not_hol : bool,
  time_limit : Time.time option,
  relocbuild : bool,
  core : HM_Core_Cline.t
}

val option_descriptions : t HM_Core_Cline.cline_result GetOpt.opt_descr list

val default_options : t

end
