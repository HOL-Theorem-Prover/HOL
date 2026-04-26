(* Poly/ML implementation of PolyRuntime.
   Provides thread-based tactic timeout, heap save, and SML string evaluation.
   Only compiled for Poly/ML builds. *)
structure PolyRuntime :> PolyRuntime =
struct

exception TacticTimeout of real

(* --- Tactic timeout using Thread + Mutex + ConditionVar --- *)

datatype 'a timeout_result = Res of 'a | Exn of exn

fun capture_result f x = Res (f x) handle Interrupt => raise Interrupt | e => Exn e
fun release_result (Res y) = y | release_result (Exn x) = raise x

fun tactic_timeout (t: real) (f: 'a -> 'b) (x: 'a) : 'b =
  if t <= 0.0 then f x
  else let
    val m = Mutex.mutex ()
    val c = ConditionVar.conditionVar ()
    val result_ref = ref NONE
    val curattrib = Thread.getAttributes ()
    val async_attrib = [Thread.InterruptState Thread.InterruptAsynchOnce,
                        Thread.EnableBroadcastInterrupt true]
    val sync_attrib = [Thread.InterruptState Thread.InterruptSynch,
                       Thread.EnableBroadcastInterrupt true]
    fun interruptkill worker =
      (Thread.interrupt worker handle Thread _ => ();
       let fun loop n =
             if not (Thread.isActive worker) then ()
             else if n > 0 then loop (n - 1)
             else (print "Warning: thread killed\n"; Thread.kill worker)
       in loop 100000000 end)
    fun worker_fun () =
      (result_ref := SOME (capture_result f x);
       Thread.setAttributes sync_attrib;
       Mutex.lock m; ConditionVar.signal c; Mutex.unlock m)
    val _ = Thread.setAttributes sync_attrib
    val _ = Mutex.lock m
    val worker = Thread.fork (worker_fun, async_attrib)
    val deadline = Time.now () + Time.fromReal t
    val finished = ConditionVar.waitUntil (c, m, deadline)
    val _ = Mutex.unlock m
    val _ = Thread.setAttributes curattrib
    val _ = if finished then () else interruptkill worker
  in
    case !result_ref of
      NONE => raise TacticTimeout t
    | SOME (Exn Interrupt) => raise TacticTimeout t
    | SOME result => release_result result
  end

(* --- Heap save using PolyML.SaveState --- *)

fun save_heap path = let
  val depth = length (PolyML.SaveState.showHierarchy ())
in
  PolyML.SaveState.saveChild (path, depth)
end

(* --- SML string evaluation using PolyML.compiler --- *)

fun eval_sml_string s = let
  val chars = ref (String.explode (s ^ ";\n"))
  fun reader () = case !chars of
    [] => NONE
  | c :: rest => (chars := rest; SOME c)
in
  while not (null (!chars)) do
    PolyML.compiler (reader, [PolyML.Compiler.CPFileName "<fragment>"]) ()
end

end (* struct *)
