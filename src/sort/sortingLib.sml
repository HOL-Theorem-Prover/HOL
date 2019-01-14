structure sortingLib :> sortingLib =
struct

  open computeLib sortingTheory

  val add_sorting_compset =
      extend_compset [
        Defs [
          PARTIION_DEF, PART_DEF, QSORT_DEF
        ]
      ]

end
