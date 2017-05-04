signature Thm =
sig

  include FinalThm where type tag = Tag.tag
                     and type hol_type = KernelTypes.hol_type
                     and type term = KernelTypes.term
		     and type thm = KernelTypes.thm
  val to_kt          : thm -> KernelTypes.thm
end
