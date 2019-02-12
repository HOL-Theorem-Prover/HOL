open HolKernel Parse boolLib testutils

local
val sorteval = let
  val cs = listLib.list_compset()
  val _ = pairLib.add_pair_compset cs;
  val _ = sortingLib.add_sorting_compset cs;
in
  computeLib.CBV_CONV cs
end
val sort = ``QSORT $<``

fun sorttest ns =
    let
      fun mk xs =
          listSyntax.mk_list(map (numSyntax.mk_numeral o Arbnum.fromInt) xs,
                             numSyntax.num)
    in
      convtest("QSORT $< [" ^ String.concatWith "," (map Int.toString ns) ^ "]",
               sorteval, mk_comb(sort, mk ns),
               mk (Listsort.sort Int.compare ns))
    end
in

val _ = List.app sorttest [
      [], [1], [10,2,101,4,5],
      List.tabulate(20, fn n => n),
      List.rev (List.tabulate(20, fn n => n)),
      Random.rangelist (0,100) (20, Random.newgen())
    ]
end
