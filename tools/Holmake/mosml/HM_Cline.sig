signature HM_Cline =
sig

type t = {
  no_basis2002 : bool,
  mosmldir : string option,
  core : HM_Core_Cline.t
}

val option_descriptions : ((string -> unit) * t -> t) GetOpt.opt_descr list

val default_options : t

end
