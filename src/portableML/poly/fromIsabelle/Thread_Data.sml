(*  Title:      Pure/Concurrent/thread_data.ML
    Author:     Makarius

Thread-local data -- physical version without context management.
*)

signature THREAD_DATA =
sig
  type 'a var
  val var: unit -> 'a var
  val get: 'a var -> 'a option
  val put: 'a var -> 'a option -> unit
  val setmp: 'a var -> 'a option -> ('b -> 'c) -> 'b -> 'c
  val is_virtual: bool
end;

structure Thread_Data: THREAD_DATA =
struct

abstype 'a var = Var of 'a option Universal.tag
with

fun var () : 'a var = Var (Universal.tag ());

fun get (Var tag) =
  (case Thread.Thread.getLocal tag of
    SOME data => data
  | NONE => NONE);

fun put (Var tag) data = Thread.Thread.setLocal (tag, data);

fun setmp v data f x =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val orig_data = get v;
      val _ = put v data;
      val result = Exn.capture (restore_attributes f) x;
      val _ = put v orig_data;
    in Exn.release result end) ();

end;

val is_virtual = false;

end;
