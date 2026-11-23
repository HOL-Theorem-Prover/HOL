(* ADD_INDEX_CONV caches index theorems per word type in a shared compset.
   For each word size that no earlier test used, several threads prove a goal
   about it at once, so they race to add its index theorems.  Poly/ML only. *)
open HolKernel Parse boolLib bossLib;
open testutils

val _ = new_theory "scratch"

val widths = List.tabulate (30, fn i => 200 + i)
val nthreads = 8

val _ = tprint "BBLAST_PROVE on threads sharing a fresh word size"

val failed = ref 0
val arrived = ref 0
val lock = Mutex.mutex ()
fun locked f = (Mutex.lock lock; f (); Mutex.unlock lock)
fun note_failure () = locked (fn () => failed := !failed + 1)
fun arrive () = locked (fn () => arrived := !arrived + 1)

fun goal w =
  Parse.Term [QUOTE ("!x : word8. !y. (w2w x : bool[" ^ Int.toString w ^
                     "]) = w2w y ==> x = y")]

fun attempt w =
  let
    val g = goal w
    val go = ref false
    val _ = arrived := 0
    fun prove () =
      (arrive ();
       while not (!go) do ();
       ignore (blastLib.BBLAST_PROVE g))
      handle _ => note_failure ()
    val threads =
      List.tabulate
        (nthreads,
         fn _ => Standard_Thread.fork
                   {name = "BBLAST_PROVE", stack_limit = NONE,
                    interrupts = false} prove)
    val _ = while !arrived < nthreads do ()
    val _ = go := true
  in
    List.app Standard_Thread.join threads
  end

val _ = List.app attempt widths

val _ =
  if !failed = 0 then OK ()
  else die (Int.toString (!failed) ^ " proofs failed")

val _ = OS.Process.exit OS.Process.success
