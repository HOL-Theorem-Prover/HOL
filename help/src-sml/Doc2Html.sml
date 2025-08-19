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

fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
fun die s = (warn s; OS.Process.exit OS.Process.failure)

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


fun transHTML pdexe htmldir docdir docfile = let
  val docbase = OS.Path.base docfile
  val docpath = docdir ++ docfile
  val outfile =
      OS.Path.joinBaseExt{base = htmldir ++ docbase, ext = SOME "html"}
  val filter = HOLDIR ++ "help/src-sml/internal-to-external.lua"
  val res =
      Systeml.systeml [pdexe, docpath, "-s", "-c", "doc.css", "-o", outfile,
                       "--lua-filter="^filter]
in
  if OS.Process.isSuccess res then ()
  else die "pandoc call failed"
end handle e => die ("Exception raised: " ^ General.exnMessage e)

fun transTXT pdexe docdir docfile = let
  val docbase = OS.Path.base docfile
  val docpath = docdir ++ docfile
  val outfile = OS.Path.joinBaseExt{base = docdir ++ docbase, ext = SOME "txt"}
  val res = Systeml.systeml [pdexe, docpath, "-t", "plain", "-o", outfile]
in
  if OS.Process.isSuccess res then ()
  else die "pandoc call failed"
end handle e => die ("Exception raised: " ^ General.exnMessage e)

fun transBOTH pdexe htmldir docdir docfile = (
  transHTML pdexe htmldir docdir docfile;
  transTXT pdexe docdir docfile
)

fun find_mdfiles dirname = let
  val dirstrm = OS.FileSys.openDir dirname
  fun loop A =
      case OS.FileSys.readDir dirstrm of
          NONE => (OS.FileSys.closeDir dirstrm;
                   Listsort.sort String.compare A)
        | SOME s => (
          case OS.Path.ext s of
              SOME "md" => loop (s::A)
            | SOME "smd" => loop (s::A)
            | _ => loop A
        )
in
  loop []
end

fun do_commands cmds =
    case cmds of
        [] => OS.Process.success
      | c::cs =>
        let
          val _ = print (c ^ "\n")
          val res = OS.Process.system c
        in
          if OS.Process.isSuccess res then do_commands cs
          else res
        end


fun docdir_to_htmldir pdexe docdir docfiles htmldir = let
  open OS.FileSys
  val docfiles = find_mdfiles docdir
in
  case which "parallel" of
      "" =>
      let
        val (tick, finish) = Flash.initialise ("Directory "^docdir^": ",
                                               length docfiles)
      in
        List.app (fn fname => (transBOTH pdexe htmldir docdir fname; tick()))
                 docfiles;
        finish();
        OS.Process.success
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
        val command1 =
          "parallel --halt now,fail=1 --eta --arg-file " ^ tmp ^
          " pandoc {} -s -c doc.css -o " ^ htmldir ^ "/{/.}.html --lua-filter=" ^
          (HOLDIR ++ "help/src-sml/internal-to-external.lua")
        val command2 =
          "parallel --halt now,fail=1 --eta --arg-file " ^ tmp ^
          " pandoc {} -t plain -o " ^ docdir ^ "/{/.}.txt"
      in
        do_commands [command1, command2]
      end
end


fun hash_files dir flist = let
  val old = OS.FileSys.getDir()
  val _ = OS.FileSys.chDir dir
  val temp = OS.FileSys.tmpName()
  val ostrm = TextIO.openOut temp
  fun recurse flist =
    case flist of
        [] => (TextIO.closeOut ostrm;
               OS.FileSys.chDir old;
               SHA1_ML.sha1_file{filename=temp})
      | f::fs =>
        let
          val h = SHA1_ML.sha1_file {filename=f}
        in
          TextIO.output(ostrm, f ^ " " ^ h ^ "\n");
          recurse fs
        end
in
  recurse flist
end

fun mkhash_fname dir = dir ++ "mdhash"

fun recorded_hash dir = let
  val hashfname = mkhash_fname dir
in
  if OS.FileSys.access(hashfname, [OS.FileSys.A_READ]) then
      let val strm = TextIO.openIn hashfname
          val line1 = TextIO.inputLine strm
          val _ = TextIO.closeIn strm
          open Substring
      in
        case line1 of
            NONE => NONE
          | SOME s => SOME (string (dropr Char.isSpace (full s)))
      end
  else NONE
end

fun record_hash h dir = let
  val hashfname = mkhash_fname dir
  val ostrm = TextIO.openOut hashfname
in
  TextIO.output(ostrm, h);
  TextIO.closeOut ostrm
end



fun maybe_dogeneration pdexe docdir htmldir = let
  val docfiles = find_mdfiles docdir
  val actual_hash = hash_files docdir docfiles
  val genresult =
      case recorded_hash docdir of
          NONE => docdir_to_htmldir pdexe docdir docfiles htmldir
        | SOME s =>
          if s = actual_hash then
            (warn ("Derived file generation skipped because of presence of\n\
                   \matching hash in " ^ mkhash_fname docdir);
             OS.Process.exit OS.Process.success)
          else
            docdir_to_htmldir pdexe docdir docfiles htmldir;
in
  if OS.Process.isSuccess genresult then
    record_hash actual_hash docdir
  else die "Generation of derived files failed"
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
        (maybe_dogeneration pdexe docdir htmldir
          handle e => die ("docdir exception: " ^ General.exnMessage e))
    | otherwise =>
      print ("Usage:\n  " ^
             CommandLine.name() ^ " <docdir> <htmldir>\n")
end

end;
