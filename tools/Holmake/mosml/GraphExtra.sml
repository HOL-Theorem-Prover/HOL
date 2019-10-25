structure GraphExtra :> GraphExtra =
struct

type t = unit
val extra_deps = fn t => []
val get_extra = fn _ => ()
val toString = fn () => "*"
fun canIgnore d t = false

end
