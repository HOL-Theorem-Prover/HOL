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

val attrib = [Thread.InterruptState Thread.InterruptAsynch,
  Thread.EnableBroadcastInterrupt true]

fun timeLimit t f x =
  let
    val resultref = ref NONE
    val worker = Thread.fork (fn () => resultref := SOME (capture f x), attrib)
    fun collect_result () =
      case !resultref of
        NONE => Exn FunctionTimeout
      | SOME (Exn Interrupt) => Exn FunctionTimeout
      | SOME result => result
  in
    OS.Process.sleep t;
    interruptkill worker;
    release (collect_result ())
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
  timeout 10.0 loop ();
  fun f () = timeout 0.1 loop () handle FunctionTimeout => ();
  List.tabulate (1000,fn _ => f ());
*)

