structure alistLib :> alistLib =
struct

open computeLib alistTheory


val add_alist_compset =
    extend_compset [
      Defs [
        alist_to_fmap_def,
        ALOOKUP_def
      ]
    ]

end
