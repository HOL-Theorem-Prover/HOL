structure listSimps :> listSimps =
struct

open simpLib listTheory;

(*---------------------------------------------------------------------------
        For the simplifier.
 ---------------------------------------------------------------------------*)
val list_ss = rewrites
       [APPEND, APPEND_11, EL, EVERY_DEF, FLAT, HD, LENGTH, MAP, MAP2,
        MEM, NULL_DEF, REVERSE_DEF, SUM, TL, APPEND_ASSOC, CONS, CONS_11,
        LENGTH_APPEND, LENGTH_MAP, MAP_APPEND, NOT_CONS_NIL,
        NOT_NIL_CONS, MAP_EQ_NIL, APPEND_NIL, CONS_ACYCLIC,
        list_case_def, APPEND_eq_NIL, ZIP, UNZIP,
        EVERY_APPEND, EXISTS_APPEND];


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

