structure Future :> Future =
struct


type 'a future = 'a Susp.susp

val fork = Susp.delay
val join = Susp.force
fun value v = Susp.delay (fn () => v)
fun joins l = List.map join l

end
