structure alignmentSyntax :> alignmentSyntax =
struct

open Abbrev HolKernel alignmentTheory

val s = HolKernel.syntax_fns1 "alignment"
val (byte_align_tm, mk_byte_align, dest_byte_align, is_byte_align) =
   s "byte_align"
val (byte_aligned_tm, mk_byte_aligned, dest_byte_aligned, is_byte_aligned) =
   s "byte_aligned"

val s = HolKernel.syntax_fns2 "alignment"
val (align_tm, mk_align, dest_align, is_align) = s "align"
val (aligned_tm, mk_aligned, dest_aligned, is_aligned) = s "aligned"

end
