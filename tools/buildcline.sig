signature buildcline =
sig

  type t = buildcline_dtype.t
  val initial : t

  type 'a cline_result = { update : (string -> unit) * 'a -> 'a }
  val cline_opt_descrs : t cline_result GetOpt.opt_descr list

end
