(*  Title:      Pure/Concurrent/counter.ML
    Author:     Makarius

Synchronized counter for unique identifiers > 0.

NB: ML ticks forwards, JVM ticks backwards.
*)

signature COUNTER =
sig
  val make: unit -> unit -> int
end;

structure Counter: COUNTER =
struct

fun make () =
  let
    val counter = Synchronized.var "counter" 0;
    fun next () =
      Synchronized.change_result counter
        (fn i =>
          let val j = i + (if Thread_Data.is_virtual then 3 else 2)
          in (j, j) end);
  in next end;

end;
