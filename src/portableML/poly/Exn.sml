(*  Title:      Pure/General/exn.ML
    Author:     Makarius

Support for exceptions.
*)

structure Exn: Exn =
struct

(* location *)

val polyml_location = PolyML.Exception.exceptionLocation;

val reraise = PolyML.Exception.reraise;


(* user errors *)

exception ERROR of string;

fun error msg = raise ERROR msg;

fun cat_error "" msg = error msg
  | cat_error msg "" = error msg
  | cat_error msg1 msg2 = error (msg1 ^ "\n" ^ msg2);


(* exceptions as values *)

datatype 'a result =
  Res of 'a |
  Exn of exn;

fun get_res (Res x) = SOME x
  | get_res _ = NONE;

fun get_exn (Exn exn) = SOME exn
  | get_exn _ = NONE;

fun capture f x = Res (f x) handle e => Exn e;

fun release (Res y) = y
  | release (Exn e) = reraise e;

fun map_res f (Res x) = Res (f x)
  | map_res f (Exn e) = Exn e;

fun maps_res f = (fn Res x => x | Exn e => Exn e) o map_res f;

fun map_exn f (Res x) = Res x
  | map_exn f (Exn e) = Exn (f e);


(* interrupts *)

exception Interrupt = Thread.Thread.Interrupt;

fun interrupt () = raise Interrupt;

fun is_interrupt Interrupt = true
  | is_interrupt (IO.Io {cause, ...}) = is_interrupt cause
  | is_interrupt _ = false;

val interrupt_exn = Exn Interrupt;

fun is_interrupt_exn (Exn exn) = is_interrupt exn
  | is_interrupt_exn _ = false;

fun interruptible_capture f x =
  Res (f x) handle e => if is_interrupt e then reraise e else Exn e;


(* concatenated exceptions *)

exception EXCEPTIONS of exn list;


(* low-level trace *)

fun trace exn_message output e =
  PolyML.Exception.traceException
    (e, fn (trace, exn) =>
      let
        val title = "Exception trace - " ^ exn_message exn;
        val () = output (String.concatWith "\n" (title :: trace));
      in reraise exn end);

end;
