structure target_times :> target_times =
struct

type map = (string, real) Binarymap.dict

fun load _ = Binarymap.mkDict String.compare

fun load_seeds _ = Binarymap.mkDict String.compare

fun cost _ _ = 0.0

fun merge_entries _ = ()

end
