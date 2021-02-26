signature Diff =
sig
   val basic_diffs :unit -> Thm.thm list
   val temp_add_diffs : Thm.thm list -> unit
   val DIFF_CONV : Abbrev.conv
end
