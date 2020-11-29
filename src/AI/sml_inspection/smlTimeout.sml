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

fun interruptkill worker =
   if not (Thread.isActive worker) then () else
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
   Timeout with busy waiting watcher and main thread
   ------------------------------------------------------------------------- *)

exception FunctionTimeout

datatype 'a result = Res of 'a | Exn of exn

fun capture f x = Res (f x) handle e => Exn e

fun release (Res y) = y
  | release (Exn x) = raise x

val attrib = [Thread.InterruptState Thread.InterruptAsynchOnce,
  Thread.EnableBroadcastInterrupt true]

fun timeLimit t f x =
  let
    val resultref = ref NONE
    fun worker_fun () = resultref := SOME (capture f x)
    val worker = Thread.fork (worker_fun, attrib)
    fun watcher_fun x =
      let 
        val rt = Timer.startRealTimer () 
        fun loop () = 
          if not (Thread.isActive worker) then () else 
          if Time.toReal (Timer.checkRealTimer rt) > t 
          then interruptkill worker
          else loop ()
      in
        loop ()
      end
    val watcher = Thread.fork (watcher_fun, [])
    fun self_wait () =
      if Thread.isActive worker then self_wait () else
      case !resultref of
        NONE => Exn FunctionTimeout
      | SOME (Exn Interrupt) => Exn FunctionTimeout
      | SOME s => s
    val result = self_wait ()
  in
    release result
  end

fun timeout t f x = timeLimit t f x

val (TC_OFF : tactic -> tactic) = trace ("show_typecheck_errors", 0)

fun timeout_tactic t tac g =
  SOME (fst (timeout t (TC_OFF tac) g))
  handle Interrupt => raise Interrupt | _ => NONE

end (* struct *)

(* tests
  load "aiLib"; open aiLib;
  load "smlTimeout"; open smlTimeout;
  
  fun loop () = loop ()
  fun g () = (timeout 0.01 loop ()) handle FunctionTimeout => (); 
  fun f () = 5
  
  timeout 0.0 loop ();
  add_time List.tabulate (1000, fn _ => g ());
  add_time (timeout 1.0 f) ();
  add_time g ();
*)

