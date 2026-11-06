Theory lazyAncC[bare]
Ancestors
  lazyAncB1 lazyAncB2
Libs
  HolKernel lazyAncestryLib

(* The lazy instance has applied no delta for the theories loaded, while
   the eager one has, and the two agree on every value *)
val _ = !lazy_applied = 0 orelse raise Fail "lazyAncL: values not lazy"

fun same name (e, l) =
    e = l orelse
    raise Fail (name ^ ": eager and lazy values differ")
val thys = ["lazyAncA", "lazyAncB1", "lazyAncB2"]
val _ = List.app (fn thy => same thy (#DB eager {thyname = thy},
                                      #DB lazy {thyname = thy})) thys
val _ = !lazy_applied > 0 orelse raise Fail "lazyAncL: DB applied nothing"
val _ = same "merge" (#merge eager thys, #merge lazy thys)
val _ = same "global" (#get_global_value eager (), #get_global_value lazy ())
val _ = case #DB lazy {thyname = "lazyAncB2"} of
            SOME ["b2", "a2", "a1"] => ()
          | _ => raise Fail "lazyAncL: unexpected value for lazyAncB2"
