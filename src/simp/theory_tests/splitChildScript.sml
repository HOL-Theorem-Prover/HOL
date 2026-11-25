Theory splitChild[bare]
Ancestors splitParent
Libs HolKernel Parse boolLib splitLib

(* A [split] rule of an ancestor is a split rule here *)
val _ =
    if Lib.mem "splitParent$bool_split"
               (map #1 (splitLib.named_split_thms ()))
    then ()
    else raise Fail "splitParent$bool_split is not a split rule"
