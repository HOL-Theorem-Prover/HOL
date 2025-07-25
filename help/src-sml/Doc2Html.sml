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

fun docdir_to_htmldir pdexe docdir htmldir =
 let open OS.FileSys
     val docfiles = find_mdfiles docdir
     val (tick, finish) = Flash.initialise ("Directory "^docdir^": ",
                                            length docfiles)
 in
   List.app (fn fname => (trans pdexe htmldir docdir fname; tick())) docfiles;
   finish();
   OS.Process.exit OS.Process.success
 end

fun main () =
  case CommandLine.arguments ()
     of [pandoc_exe,docdir,htmldir] =>
        docdir_to_htmldir pandoc_exe docdir htmldir
      | otherwise =>
        print ("Usage:\n  " ^
               CommandLine.name() ^
               " <path-to-pandoc-executable> <docdir> <htmldir>\n")

end;
