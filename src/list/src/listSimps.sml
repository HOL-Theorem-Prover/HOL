structure listSimps :> listSimps =
struct

open simpLib listTheory;

(*---------------------------------------------------------------------------
        For the simplifier.
 ---------------------------------------------------------------------------*)
val LIST_ss = listTheory.list_rwts

 val list_rws = computeLib.add_thms
     [ APPEND,APPEND_NIL, FLAT, HD, TL, LENGTH, MAP, MAP2,
       NULL_DEF, CONS_11, NOT_CONS_NIL, NOT_NIL_CONS,
       MEM, EXISTS_DEF, EVERY_DEF,
       ZIP, UNZIP,
       REVERSE_DEF, (* might want to think about more efficient
                       version of this *)
       FILTER, FOLDL, FOLDR, FOLDL, EL_compute,
       computeLib.lazyfy_thm list_case_compute,
       list_size_def];

end (* struct *)

