(* ------------------------------------------------------------------------- *)
(* An MLton patch.                                                           *)
(* ------------------------------------------------------------------------- *)

structure OS =
   struct
      open OS
         
      structure Path =
         struct
            open Path

            val mkAbsolute = fn (path, relativeTo) =>
               mkAbsolute {path = path, relativeTo = relativeTo}
            val mkRelative = fn (path, relativeTo) =>
               mkRelative {path = path, relativeTo = relativeTo}
         end
   end

(* ------------------------------------------------------------------------- *)
(* Bring certain declarations to the top-level.                              *)
(* ------------------------------------------------------------------------- *)

structure FileSys = OS.FileSys;
structure Path = OS.Path;
structure Process = OS.Process;

type ppstream = PP.ppstream;

exception Interrupt = SML90.Interrupt;

(* ------------------------------------------------------------------------- *)
(* Sort out infixities.                                                      *)
(* ------------------------------------------------------------------------- *)

infix 0 before;

(* ------------------------------------------------------------------------- *)
(* Quotations a la Mosml.                                                    *)
(* ------------------------------------------------------------------------- *)

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;

(* ------------------------------------------------------------------------- *)
(* Dummy versions of Mosml declarations to stop MLton barfing.               *)
(* ------------------------------------------------------------------------- *)

val quotation = ref false;
val quietdec  = ref false;
val loadPath  = ref ([] : string list);
val load      = fn (_ : string) => ();
val installPP = fn (_ : ppstream -> 'a -> unit) => ();
