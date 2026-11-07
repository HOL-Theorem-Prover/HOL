Theory lazyAncD[bare]
Ancestors
  lazyAncC lazyAncO
Libs
  HolKernel lazyAncestryLib

(* Reads the stored values of lazyAncC (merging the diamond) and of
   lazyAncO (whose recorded ancestry leaves out lazyAncB2), checking
   that each delta is applied exactly once *)
val _ = !lazy_applied = 0 orelse raise Fail "lazyAncL: values not lazy"

fun check name expected (e, l) =
    if e = l andalso
       Option.map (Listsort.sort String.compare) l = SOME expected
    then ()
    else raise Fail ("lazyAncD: unexpected value for " ^ name)
fun db thy = (#DB eager {thyname = thy}, #DB lazy {thyname = thy})
val _ = check "lazyAncC" ["a1", "a2", "b1", "b2"] (db "lazyAncC")
val _ = check "lazyAncO" ["a1", "a2", "b1", "o"] (db "lazyAncO")
val _ = check "global" ["a1", "a2", "b1", "b2", "o"]
              (SOME (#get_global_value eager ()),
               SOME (#get_global_value lazy ()))
