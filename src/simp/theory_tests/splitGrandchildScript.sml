Theory splitGrandchild[bare]
Ancestors splitChild
Libs HolKernel Parse boolLib splitLib

(* A [split] rule an ancestor retracted is not a split rule here *)
val _ =
    if Lib.mem "splitParent$bool_split"
               (map #1 (splitLib.named_split_thms ()))
    then raise Fail "splitParent$bool_split is still a split rule"
    else ()
