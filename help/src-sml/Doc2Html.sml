(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*  Invoked with, e.g.,                                                      *)
(*                                                                           *)
(*     Doc2Html "/home/kxs/kanan/help/Docfiles"                              *)
(*              "/home/kxs/kanan/help/Docfiles/html";                        *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)
structure Doc2Html = struct

open Systeml
infix ++
val  op++ = OS.Path.concat

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

(* with GNU parallel available at shell level, better to do

 ls *.md | parallel --eta pandoc {} -s -o ../Docfiles/HTML/{/.}.html --lua-filter=HOLDIR ++ "/help/src-sml/internal-to-external.lua"

*)

fun get_first f [] = NONE
  | get_first f (h::t) = case f h of NONE => get_first f t | x => x

fun which arg =
  let
    open OS.FileSys Systeml
    val sepc = if isUnix then #":" else #";"
    fun check p =
      let
        val fname = OS.Path.concat(p, arg)
      in
        if access (fname, [A_READ, A_EXEC]) then SOME fname else NONE
      end
    fun smash NONE = "" | smash (SOME s) = s
  in
    case OS.Process.getEnv "PATH" of
        SOME path =>
        let
          val paths = (if isUnix then [] else ["."]) @
                      String.fields (fn c => c = sepc) path
        in
          smash (get_first check paths)
        end
    | NONE => if isUnix then "" else smash (check ".")
  end


fun trans pdexe htmldir docdir docfile = let
  val docbase = OS.Path.base docfile
  val docpath = docdir ++ docfile
  val outfile =
      OS.Path.joinBaseExt{base = htmldir ++ docbase, ext = SOME "html"}
  val filter = HOLDIR ++ "help/src-sml/internal-to-external.lua"
  val res =
      Systeml.systeml [pdexe, docpath, "-s", "-o", outfile,
                       "--lua-filter="^filter]
in
  if OS.Process.isSuccess res then ()
  else die "pandoc call failed"
end handle e => die ("Exception raised: " ^ General.exnMessage e)

fun find_mdfiles dirname = let
  val dirstrm = OS.FileSys.openDir dirname
  fun loop A =
      case OS.FileSys.readDir dirstrm of
          NONE => (OS.FileSys.closeDir dirstrm; A)
        | SOME s => (
          case OS.Path.ext s of
              SOME "md" => loop (s::A)
            | _ => loop A
        )
in
  loop []
end

fun docdir_to_htmldir pdexe docdir htmldir = let
  open OS.FileSys
  val docfiles = find_mdfiles docdir
in
  case which "parallel" of
      "" =>
      let
        val (tick, finish) = Flash.initialise ("Directory "^docdir^": ",
                                               length docfiles)
      in
        List.app (fn fname => (trans pdexe htmldir docdir fname; tick()))
                 docfiles;
        finish();
        OS.Process.exit OS.Process.success
      end
    | s =>
      let
        val tmp = OS.FileSys.tmpName ()
        val ostrm = TextIO.openOut tmp
        fun loop lines =
            case lines of
                [] => TextIO.closeOut ostrm
              | h::t => (TextIO.output(ostrm, (docdir ++ h) ^ "\n"); loop t)
        val _ = loop docfiles
        val command =
          "parallel --halt now,fail=1 --eta --arg-file " ^ tmp ^
          " pandoc {} -s -o " ^ htmldir ^ "/{/.}.html --lua-filter=" ^
          (HOLDIR ++ "help/src-sml/internal-to-external.lua")
      in
        print (command ^ "\n");
        OS.Process.exit (OS.Process.system command)
      end
end

fun main () = let
  val pdexe =
      case which "pandoc" of
          "" => (TextIO.output(TextIO.stdErr,
                               "Can't find pandoc in PATH; doing nothing\n");
                 OS.Process.exit OS.Process.success)
        | s => s
in
  case CommandLine.arguments () of
      [docdir,htmldir] =>
        (docdir_to_htmldir pdexe docdir htmldir
          handle e => die ("docdir exception: " ^ General.exnMessage e))
    | otherwise =>
      print ("Usage:\n  " ^
             CommandLine.name() ^ " <docdir> <htmldir>\n")
end

end;
