Theory compDeltaB
Ancestors
  compDeltaA

val th = EVAL “cdrf 1”
val _ = rhs (concl th) ~~ lhs (concl th) orelse
        raise Fail "cdrf still evaluates after A's del_persistent_consts"

(* B puts cdrf's definition back *)
val _ = computeLib.add_persistent_funs ["compDeltaBase.cdrf_def"]

val th = EVAL “cdrf 1”
val _ = rhs (concl th) ~~ “2n” orelse
        raise Fail "cdrf doesn't evaluate after add_persistent_funs"
