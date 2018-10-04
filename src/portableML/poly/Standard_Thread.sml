(*  Title:      Pure/Concurrent/standard_thread.ML
    Author:     Makarius

Standard thread operations.
*)

signature STANDARD_THREAD =
sig
  val is_self: Thread.thread -> bool
  val get_name: unit -> string option
  val the_name: unit -> string
  type params = {name: string, stack_limit: int option, interrupts: bool}
  val attributes: params -> Thread.threadAttribute list
  val fork: params -> (unit -> unit) -> Thread.thread
  val join: Thread.thread -> unit
  val interrupt_unsynchronized: Thread.thread -> unit
end;

structure Standard_Thread: STANDARD_THREAD =
struct

(* self *)

fun is_self thread = Thread.equal (Thread.self (), thread);


(* unique name *)

local
  val name_var = Thread_Data.var () : string Thread_Data.var;
  val count = Counter.make ();
in

fun get_name () = Thread_Data.get name_var;

fun the_name () =
  (case get_name () of
    NONE => raise Fail "Unknown thread name"
  | SOME name => name);

fun set_name base =
  Thread_Data.put name_var (SOME (base ^ "/" ^ Int.toString (count ())));

end;


(* fork *)

type params = {name: string, stack_limit: int option, interrupts: bool};

fun attributes ({stack_limit, interrupts, ...}: params) =
  Thread.MaximumMLStack stack_limit ::
  Thread_Attributes.convert_attributes
    (if interrupts then Thread_Attributes.public_interrupts else Thread_Attributes.no_interrupts);

fun fork (params: params) body =
  Thread.fork (fn () =>
    Exn.trace General.exnMessage print (fn () =>
      (set_name (#name params); body ())
        handle exn => if Exn.is_interrupt exn then () (*sic!*) else Exn.reraise exn),
    attributes params);


(* join *)

fun join thread =
  while Thread.isActive thread
  do OS.Process.sleep (Time.fromReal 0.1);


(* interrupt *)

fun interrupt_unsynchronized thread =
  Thread.interrupt thread handle Thread _ => ();

end;
