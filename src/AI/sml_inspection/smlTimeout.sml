(* ========================================================================== *)
(* FILE          : smlTimeout.sml                                             *)
(* DESCRIPTION   : Timing out PolyML functions.                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure smlTimeout :> smlTimeout =
struct

open HolKernel Abbrev boolLib aiLib Thread

exception FunctionTimeout
datatype 'a result = Res of 'a | Exn of exn

fun capture f x = Res (f x) handle e => Exn e

fun release (Res y) = y
  | release (Exn x) = raise x

fun timeLimit t f x =
  let
    val resultref = ref NONE
    val worker = Thread.fork (fn () => resultref := SOME (capture f x), [])
    val watcher = Thread.fork (fn () =>
      (OS.Process.sleep t; interruptkill worker), [])
    fun self_wait () =
      (
      if Thread.isActive worker then self_wait () else
    case !resultref of
      NONE => Exn FunctionTimeout
    | SOME s => s
      )
    val result = self_wait ()
  in
    release result
  end

fun timeout t f x = timeLimit (Time.fromReal t) f x

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun timeout_tactic t tac g =
  SOME (fst (timeout t (TC_OFF tac) g))
  handle Interrupt => raise Interrupt | _ => NONE


end (* struct *)

(* test
  load "smlTimeout"; open smlTimeout;
  fun loop () = loop ();
  fun wait100 () = OS.Process.sleep (Time.fromReal 100.0);
  timeout 1.0 wait100 ();
  timeout 1.0 loop (); (* killed *)

  val worker = Thread.fork (fn () => ignore (METIS_TAC (map snd (DB.thms "arithmetic")) ([],``1=2``)),[Thread.InterruptState Thread.InterruptAsynch]);
  fun loop () = loop ();
  val worker = Thread.fork (fn () => loop (),[Thread.InterruptState Thread.InterruptAsynch]);
*)





