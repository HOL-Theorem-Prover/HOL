(*  Title:      Pure/Concurrent/single_assignment.ML
    Author:     Makarius

Single-assignment variables with locking/signalling.
*)

signature SINGLE_ASSIGNMENT =
sig
  type 'a var
  val var: string -> 'a var
  val peek: 'a var -> 'a option
  val await: 'a var -> 'a
  val assign: 'a var -> 'a -> unit
end;

structure Single_Assignment: SINGLE_ASSIGNMENT =
struct

abstype 'a var = Var of
 {name: string,
  lock: Mutex.mutex,
  cond: ConditionVar.conditionVar,
  var: 'a SingleAssignment.saref}
with

fun var name = Var
 {name = name,
  lock = Mutex.mutex (),
  cond = ConditionVar.conditionVar (),
  var = SingleAssignment.saref ()};

fun peek (Var {var, ...}) = SingleAssignment.savalue var;

fun await (v as Var {name, lock, cond, ...}) =
  Multithreading.synchronized name lock (fn () =>
    let
      fun wait () =
        (case peek v of
          NONE =>
            (case Multithreading.sync_wait NONE cond lock of
              Exn.Res _ => wait ()
            | Exn.Exn exn => Exn.reraise exn)
        | SOME x => x);
    in wait () end);

fun assign (v as Var {name, lock, cond, var}) x =
  Multithreading.synchronized name lock (fn () =>
    (case peek v of
      SOME _ => raise Fail ("Duplicate assignment to " ^ name)
    | NONE =>
        Thread_Attributes.uninterruptible (fn _ => fn () =>
         (SingleAssignment.saset (var, x); ConditionVar.broadcast cond)) ()));

end;

end;
