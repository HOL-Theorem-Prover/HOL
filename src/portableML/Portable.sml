(* ===================================================================== *)
(* FILE          : Portable.sml                                          *)
(* DESCRIPTION   : Structure for SML System dependent functions.         *)
(*                 (Please look at the structures Portable_* as well)    *)
(* AUTHOR        : Ken Larsen, University of Cambridge (or DTU)          *)
(*                 based on code by                                      *)
(*                 Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 19 September, 1997                                    *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)
(* Copyright 1997 by University of Cambridge *)

(* Share and Enjoy *)

structure Portable = 
struct

val string_to_int  = Int.fromString;
val real_to_string = Real.toString
val implode        = Portable_String.concat;
val explode        = map Portable_String.str o Portable_String.explode;

val say       = TextIO.print
val linewidth = ref 72 (* ### POTENTIAL ### *) 

val getEnv = Process.getEnv
val cd     = FileSys.chDir
val pwd    = FileSys.getDir


val listDir = Mosml.listDir (* ### POTENTIAL ### *)

fun system s = if Process.system s = Process.success then 0 else 1
val getArgs  = CommandLine.arguments
val argv     = getArgs

fun file_exists_for_reading s = FileSys.access(s,[FileSys.A_READ])

fun exit() = Process.exit Process.success

exception Io of string;

type instream      = TextIO.instream 
type outstream     = TextIO.outstream 
val std_out        = TextIO.stdOut
val stdin          = TextIO.stdIn
fun open_in file   = TextIO.openIn file 
                     handle General.Io{cause=SysErr(s,_),...} => raise (Io s)
                                   (* handle OS.SysErr (s,_) => raise Io s; *)
fun open_out file  = TextIO.openOut file 
                     handle General.Io{cause=SysErr(s,_),...} => raise (Io s)
                                   (* handle OS.SysErr (s,_) => raise Io s; *)
val output         = TextIO.output
fun outputc strm s = output(strm,s)
val close_in       = TextIO.closeIn
val close_out      = TextIO.closeOut
val flush_out      = TextIO.flushOut
val input_line     = TextIO.inputLine
val end_of_stream  = TextIO.endOfStream


fun pointer_eq(x,y) = x=y
(* ((Unsafe.cast x:int) = (Unsafe.cast y:int)) *)

end (* structure Portable *)
