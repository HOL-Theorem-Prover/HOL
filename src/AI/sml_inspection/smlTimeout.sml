(* ========================================================================== *)
(* FILE          : smlTimeout.sml                                             *)
(* DESCRIPTION   : Timing out PolyML functions.                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure smlTimeout :> smlTimeout =
struct

open HolKernel Abbrev boolLib aiLib Thread

val ERR = mk_HOL_ERR "smlTimeout"

(* -------------------------------------------------------------------------
   Interrupt a thread and wait for it to terminate to continue.
   ------------------------------------------------------------------------- *)

(* todo: include small waiting time in the loop to reduce busing waiting
   using condition wait *)
fun interruptkill worker =
  let
    val _ = Thread.interrupt worker handle Thread _ => ()
    fun loop n =
      if not (Thread.isActive worker) then () else
        if n > 0
        then loop (n-1)
        else (print_endline "Warning: thread killed"; Thread.kill worker)
  in
    loop 100000000
  end

(* -------------------------------------------------------------------------
   Timeout with busy main thread
   ------------------------------------------------------------------------- *)

exception FunctionTimeout

datatype 'a result = Res of 'a | Exn of exn

fun capture f x = Res (f x)
  handle Interrupt => raise Interrupt | e => Exn e

fun release (Res y) = y
  | release (Exn x) = raise x

val attrib_async = [Thread.InterruptState Thread.InterruptAsynchOnce,
  Thread.EnableBroadcastInterrupt true]

val attrib_sync = [Thread.InterruptState Thread.InterruptSynch,
  Thread.EnableBroadcastInterrupt true]

fun timeLimit t f x =
  let
    val m = Mutex.mutex ()
    val curattrib = Thread.getAttributes ()
    val _ = Thread.setAttributes attrib_sync
    val _ = Mutex.lock m
    val c = ConditionVar.conditionVar ()
    val resultref = ref NONE
    fun worker_fun () =
      (
      resultref := SOME (capture f x);
      Thread.setAttributes attrib_sync;
      Mutex.lock m; ConditionVar.signal c; Mutex.unlock m
      )
    val worker = Thread.fork (worker_fun, attrib_async)
    val b = ConditionVar.waitUntil (c,m,Time.now () + t)
    val _ = Mutex.unlock m
    val _ = Thread.setAttributes curattrib
    val _ = if b then () else interruptkill worker
    val result = case !resultref of
        NONE => Exn FunctionTimeout
      | SOME (Exn Interrupt) => Exn FunctionTimeout
      | SOME s => s
  in
    release result
  end

fun timeout t f x = timeLimit (Time.fromReal t) f x

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun timeout_tactic t tac g =
  SOME (fst (timeout t (TC_OFF tac) g))
  handle Interrupt => raise Interrupt | _ => NONE

end (* struct *)

(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "smlTimeout"; open smlTimeout;

fun f () = 5;
add_time (timeout 1.0 f) ();



fun g () = (timeout 0.01 loop ()) handle FunctionTimeout => ();
add_time List.tabulate (1000, fn _ => g ());
add_time g ();

fun loop () = loop ();
fun zero () = loop () handle Interrupt => zero ();
val g : goal = ([],``!x. x = x``);
fun f1 g  = (zero (); SOME (fst (STRIP_TAC g)));
fun f2 g  = (SOME (fst (STRIP_TAC g)));
fun f3 g  = (loop (); SOME (fst (STRIP_TAC g)));
val (_,t) = add_time (timeout_ext 0.1 f1) g;
val (_,t) = add_time (timeout_ext 0.1 f2) g;
val (_,t) = add_time (timeout_ext 0.1 f3) g;
val (_,t) = add_time (timeout_ext 0.1 f1) g;
val (_,t) = add_time (timeout_ext 0.1 f2) g;
val (_,t) = add_time (timeout_ext 0.1 f3) g;
stop_global_worker ();



val (_,t) = add_time f g;

fun f x = List.tabulate (10, fn _ => timeout 5.0 STRIP_TAC x);
val (_,t) = add_time f ([],``!x.x=x``);

*)

