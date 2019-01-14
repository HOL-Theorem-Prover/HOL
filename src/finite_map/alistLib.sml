structure alistLib :> alistLib =
struct

open computeLib alistTheory


fun add_alist_compset cs =
    extend_compset [
      Defs [
        alist_to_fmap_def,
        ALOOKUP_def
      ]
    ]



end
