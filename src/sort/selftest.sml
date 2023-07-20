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


val _ = convtest("PERM_NO_ELIM_NORMALISE_CONV",
                 permLib.PERM_NO_ELIM_NORMALISE_CONV,
                 “PERM (x:'a::l1++y::l2++l3) (y::l3++z::l2++l4)”,
                 “PERM (x:'a::y::(l1++l2++l3)) (y::z::(l2++l3++l4))”)

val _ = convtest("PERM_ELIM_DUPLICATES_CONV",
                 permLib.PERM_ELIM_DUPLICATES_CONV,
                 “PERM (x:'a::l1++y::l2++l3) (y::l3++z::l2++l4)”,
                 “PERM (x:'a::l1) ([z]++l4)”)
