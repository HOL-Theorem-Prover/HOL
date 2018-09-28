(*  Title:      Pure/Concurrent/unsynchronized.ML
    Author:     Makarius

Raw ML references as unsynchronized state variables.
*)

signature UNSYNCHRONIZED =
sig
  datatype ref = datatype ref
  val := : 'a ref * 'a -> unit
  val ! : 'a ref -> 'a
  val change: 'a ref -> ('a -> 'a) -> unit
  val change_result: 'a ref -> ('a -> 'b * 'a) -> 'b
  val inc: int ref -> int
  val dec: int ref -> int
  val setmp: 'a ref -> 'a -> ('b -> 'c) -> 'b -> 'c
end;

structure Unsynchronized: UNSYNCHRONIZED =
struct

datatype ref = datatype ref;

val op := = op :=;
val ! = !;

fun change r f = r := f (! r);
fun change_result r f = let val (x, y) = f (! r) in r := y; x end;

fun inc i = (i := ! i + (1: int); ! i);
fun dec i = (i := ! i - (1: int); ! i);

fun setmp flag value f x =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val orig_value = ! flag;
      val _ = flag := value;
      val result = Exn.capture (restore_attributes f) x;
      val _ = flag := orig_value;
    in Exn.release result end) ();

end;
