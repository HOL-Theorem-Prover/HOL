signature BoundedRewrites =
sig

  datatype control = UNBOUNDED | BOUNDED of int ref
  type thm = Thm.thm
  type controlled_thm = thm * control

  val dest_tagged_rewrite : thm -> controlled_thm
  val MK_BOUNDED : thm -> int -> thm
  val DEST_BOUNDED : thm -> thm * int
  val Ntimes : thm -> int -> thm
  val Once : thm -> thm

end
