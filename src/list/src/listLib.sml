structure listLib :> listLib =
struct


open listTheory
fun list_compset () = let
  open computeLib reduceLib
  val base = num_compset()
in
  add_thms [APPEND,APPEND_NIL, FLAT, HD, TL,
            LENGTH, MAP, MAP2, NULL_DEF, MEM, EXISTS_DEF,
            EVERY_DEF, ZIP, UNZIP, FILTER, FOLDL, FOLDR,
            FOLDL, REVERSE_DEF, EL_compute, ALL_DISTINCT,
            computeLib.lazyfy_thm list_case_compute,
            list_size_def,FRONT_DEF,LAST_DEF,
            CONS_11, NOT_CONS_NIL, NOT_NIL_CONS] base;
  base
end



end;
