structure sortingLib :> sortingLib =
struct

  open computeLib sortingTheory

  fun add_sorting_compet cs =
      extend_compset [
        Defs [
          PARTIION_DEF, PART_DEF, QSORT_DEF
        ]
      ]

end
