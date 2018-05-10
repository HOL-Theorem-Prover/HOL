(*  Title:      Pure/Concurrent/synchronized.ML
    Author:     Fabian Immler and Makarius

Synchronized variables.
*)

signature SYNCHRONIZED =
sig
  type 'a var
  val var: string -> 'a -> 'a var
  val value: 'a var -> 'a
  val timed_access: 'a var -> ('a -> Time.time option) -> ('a -> ('b * 'a) option) -> 'b option
  val guarded_access: 'a var -> ('a -> ('b * 'a) option) -> 'b
  val change_result: 'a var -> ('a -> 'b * 'a) -> 'b
  val change: 'a var -> ('a -> 'a) -> unit
end;

structure Synchronized: SYNCHRONIZED =
struct

(* state variable *)

abstype 'a var = Var of
 {name: string,
  lock: Mutex.mutex,
  cond: ConditionVar.conditionVar,
  var: 'a Unsynchronized.ref}
with

fun var name x = Var
 {name = name,
  lock = Mutex.mutex (),
  cond = ConditionVar.conditionVar (),
  var = Unsynchronized.ref x};

fun value (Var {name, lock, var, ...}) =
  Multithreading.synchronized name lock (fn () => ! var);


(* synchronized access *)

fun timed_access (Var {name, lock, cond, var}) time_limit f =
  Multithreading.synchronized name lock (fn () =>
    let
      fun try_change () =
        let val x = ! var in
          (case f x of
            NONE =>
              (case Multithreading.sync_wait (time_limit x) cond lock of
                Exn.Res true => try_change ()
              | Exn.Res false => NONE
              | Exn.Exn exn => Exn.reraise exn)
          | SOME (y, x') =>
              Thread_Attributes.uninterruptible (fn _ => fn () =>
                (var := x'; ConditionVar.broadcast cond; SOME y)) ())
        end;
    in try_change () end);

fun guarded_access var f = the (timed_access var (fn _ => NONE) f);


(* unconditional change *)

fun change_result var f = guarded_access var (SOME o f);
fun change var f = change_result var (fn x => ((), f x));

end;

end;
