structure sortingLib :> sortingLib =
struct

  open computeLib sortingTheory

  val add_sorting_compset =
      extend_compset [
        Defs [
          PARTITION_DEF, PART_DEF, QSORT_DEF
        ]
      ]

end
