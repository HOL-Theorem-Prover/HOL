(* ----------------------------------------------------------------------
   Timeout. Re-using part of isabelle Library. (Thanks Makarius)
   ---------------------------------------------------------------------- *)

(* modified now 
val polyml_folder = "/home/gauthier/polyml.5.5.1"
val pure_folder = "/home/gauthier/Isabelle2013-2/src/Pure"
(* exceptions *)
use (pure_folder ^ "/" ^ "General/exn.ML");
*)
(* multithreading *)
(*
use (pure_folder ^ "/" ^ "ML-Systems/multithreading.ML");
use (pure_folder ^ "/" ^ "ML-Systems/multithreading_polyml.ML");
*)

structure hhsTimeout :> hhsTimeout =
struct

exception TacTimeOut;

datatype 'a result = Res of 'a | Exn of exn;

fun capture f x = Res (f x) handle e => Exn e
                                 
fun release (Res y) = y
  | release (Exn _) = raise TacTimeOut

open Thread;

fun timeLimit time f x =
  let
    val result_ref = ref NONE
    val short_time = (Time.fromReal (Time.toReal time / 20.0))
    val worker =
      let 
        fun worker_call () = result_ref := SOME (capture f x)
      in
        Thread.fork (fn () => worker_call (),[])
      end
    val watchdog = 
      let 
        fun watchdog_call () = 
        (
        OS.Process.sleep time;
        if Thread.isActive worker 
          then (
                Thread.interrupt worker; 
                OS.Process.sleep time;
                if Thread.isActive worker 
                then Thread.kill worker
                else () 
              )                
          else ()
        )
      in
        Thread.fork (fn () => watchdog_call (),[])
      end      
    fun self_wait () = 
      (
      OS.Process.sleep short_time;
      if Thread.isActive worker 
        then self_wait ()      
        else 
          case !result_ref of 
            NONE => Exn TacTimeOut
          | SOME s => s
      )
    val result = self_wait ()
  in
    release result
  end

fun timeOut t f x = timeLimit (Time.fromReal t) f x

end

(* 
  fun loop () = (OS.Process.sleep (Time.fromReal 1.0));
  val _ = timeLimit (Time.fromReal 1.0) loop ();
*)
