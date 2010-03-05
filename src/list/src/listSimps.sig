signature listSimps =
sig
     val LIST_ss : simpLib.ssfrag
     val LIST_EQ_ss : simpLib.ssfrag

     val NORM_CONS_APPEND_CONV : Conv.conv
     val LIST_EQ_SIMP_CONV : Conv.conv

     val list_rws : computeLib.compset -> unit
     val list_compset : unit -> computeLib.compset
end
