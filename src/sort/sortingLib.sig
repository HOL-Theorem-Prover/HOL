signature sortingLib =
sig

val add_sorting_compset : computeLib.compset -> computeLib.compset
  (* need to use
       val cs = listLib.list_compset
                |> pairLib.add_pair_compset
                |> sortingLib.add_sorting_compset
     at bare minimum, plus whatever is needed to evaluate any ordering
     relation
   *)

end
