signature decompileLib =
sig

  val decomp : string -> bool -> string -> Thm.thm

  val decomp_only : string -> bool -> string list -> Thm.thm

end
