signature listSimps =
sig
     val LIST_ss  : simpLib.ssfrag
     val list_rws : computeLib.compset -> unit
     val list_compset : unit -> computeLib.compset
end
