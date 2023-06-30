structure Unsynchronized :> Unsynchronized =
struct

datatype ref = datatype ref;

val op := = op :=;
val ! = !;

fun change r f = r := f (! r);
fun change_result r f = let val (x, y) = f (! r) in r := y; x end;

fun inc i = (i := ! i + (1: int); ! i);
fun dec i = (i := ! i - (1: int); ! i);

fun setmp flag value f x =
    let
      val orig_value = ! flag;
      val _ = flag := value;
      val result = Exn.capture f x;
      val _ = flag := orig_value;
    in Exn.release result
    end


end
