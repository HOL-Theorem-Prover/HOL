signature alignmentSyntax =
sig

   include Abbrev

   val align_tm: term
   val aligned_tm: term
   val byte_align_tm: term
   val byte_aligned_tm: term

   val dest_align: term -> term * term
   val dest_aligned: term -> term * term
   val dest_byte_align: term -> term
   val dest_byte_aligned: term -> term

   val is_align: term -> bool
   val is_aligned: term -> bool
   val is_byte_align: term -> bool
   val is_byte_aligned: term -> bool

   val mk_align: term * term -> term
   val mk_aligned: term * term -> term
   val mk_byte_align: term -> term
   val mk_byte_aligned: term -> term

end
