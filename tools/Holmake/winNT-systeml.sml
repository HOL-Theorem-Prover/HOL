structure Systeml :> Systeml = struct

(* This is the WINDOWS implementation of the Systeml functionality.
   It is the very first thing compiled by the HOL build process so it
   absolutely can not depend on any other HOL source code. *)

fun dquote s = concat ["\"", s, "\""]
fun concat_wspaces munge acc strl =
    case strl of
      [] => concat (List.rev acc)
    | [x] => concat (List.rev (munge x :: acc))
    | (x::xs) => concat_wspaces munge (" " :: munge x :: acc) xs
open Process

fun systeml l = let
  val command = "call "^concat_wspaces dquote [] l
in
  Process.system command
end

val protect = dquote

fun xable_string s = s^".exe"
fun mk_xable file =   (* returns the name of the executable *)
    let val exe = file^".exe"
        val _ = FileSys.remove exe handle _ => ()
    in
      FileSys.rename{old=file, new=exe};
      exe
    end

fun normPath s = Path.toString(Path.fromString s)

fun fullPath slist =
    normPath (List.foldl (fn (p1,p2) => Path.concat(p2,p1))
                         (hd slist) (tl slist))

val HOLDIR =
val MOSMLDIR =
val OS =
val DEPDIR =
val GNUMAKE =

local
  fun fopen file = (FileSys.remove file handle _ => (); TextIO.openOut file)
  fun munge s = String.translate (fn #"/" => "\\" | c => str c) s
  fun q s = "\""^munge s^"\""
in
fun emit_hol_script target qend =
 let val ostrm = fopen(target^".bat")
     fun output s = TextIO.output(ostrm, s)
     val sigobj = q (fullPath [HOLDIR, "sigobj"])
     val std_prelude = q (fullPath [HOLDIR, "std.prelude"])
     val mosml = q (fullPath [MOSMLDIR, "bin", "mosml"])
 in
    output "@echo off\n";
    output  "rem The bare hol98 script\n\n";
    output (String.concat["call ", mosml, " -P full -I ", sigobj, " ",
                          std_prelude, " %* ", q qend, "\n"]);
    TextIO.closeOut ostrm;
    target
 end


fun emit_hol_unquote_script target qend =
 let val ostrm = fopen(target^".bat")
     fun output s = TextIO.output(ostrm, s)
     val qfilter = q (fullPath [HOLDIR, "bin", "unquote"])
     val sigobj = q (fullPath [HOLDIR, "sigobj"])
     val std_prelude = q (fullPath [HOLDIR, "std.prelude"])
     val mosml = q (fullPath [MOSMLDIR, "bin", "mosml"])
     val qinit = q (fullPath [HOLDIR, "tools", "unquote-init.sml"])
 in
    output  "@echo off\n";
    output  "rem The hol98 script (with quote preprocessing)\n\n";
    output  (String.concat ["call ", qfilter, " | ", mosml,
                          " -P full -I ", sigobj, " ",
                            std_prelude, " ", qinit, " %* ",
                            q qend, "\n"]);
    TextIO.closeOut ostrm;
    target
 end
end (* local *)


end; (* struct *)


