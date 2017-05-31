signature tactictoe =
sig

  val hhs_debug : bool ref
  val tactictoe : term -> unit
  val bare_tactictoe : term -> unit

end
