(* ------------------------------------------------------------------------- *)
(* Bring certain declarations to the top-level.                              *)
(* ------------------------------------------------------------------------- *)

structure FileSys = OS.FileSys;
structure Path = OS.Path;
structure Process = OS.Process;

type ppstream = PP.ppstream;

exception Interrupt = SML90.Interrupt;
exception Io = IO.Io;

(* ------------------------------------------------------------------------- *)
(* Sort out infixities                                                       *)
(* ------------------------------------------------------------------------- *)

infix 0 before;

(* ------------------------------------------------------------------------- *)
(* Quotations a la Mosml                                                     *)
(* ------------------------------------------------------------------------- *)

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;

(* ------------------------------------------------------------------------- *)
(* A quit function                                                           *)
(* ------------------------------------------------------------------------- *)

fun quit () : unit = OS.Process.exit OS.Process.success;

(* ------------------------------------------------------------------------- *)
(* Dummy versions of Mosml declarations to stop MLton barfing                *)
(* ------------------------------------------------------------------------- *)

val quotation = ref true;
val quietdec  = ref true;
val loadPath  = ref ([] : string list);
val load      = fn (_ : string) => ();
val installPP = fn (_ : ppstream -> 'a -> unit) => ();
