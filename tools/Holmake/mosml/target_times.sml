structure target_times :> target_times =
struct

type map = (string, real) Binarymap.dict

fun load _ = Binarymap.mkDict String.compare

fun theory_cost _ _ = 0.0

fun merge_from_log _ = ()

end
