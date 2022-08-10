signature Diff =
sig
   val basic_diffs :unit -> Thm.thm list
   val temp_add_diffs : Thm.thm list -> unit
   val DIFF_CONV : Abbrev.conv

   (* A variant of DIFF_CONV based on `has_vector_derivative` *)
   val HAS_VECTOR_DERIVATIVE_CONV : Abbrev.conv
end
