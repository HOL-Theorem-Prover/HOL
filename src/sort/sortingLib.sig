signature sortingLib =
sig

val add_sorting_compset : computeLib.compset -> unit
  (* need to use
       val cs = listLib.list_compset()
       val _ = pairLib.add_pair_compset cs;
       val _ = sortingLib.add_sorting_compset cs;
     at bare minimum, plus whatever is needed to evaluate any ordering
     relation
   *)

end
