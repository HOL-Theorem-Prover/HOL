(* program to output iss file *)
(* to compile this structure, cd to the tools directory, and
     mosmlc -o make_iss.exe -I Holmake -I ..\sigobj make_iss.sml
*)
structure make_iss = struct

structure FileSys = OS.FileSys

val holdir = Globals.HOLDIR
val systeml = Systeml.systeml

val sysname = Globals.release ^ " " ^ Int.toString Globals.version
val _ = print "Changing to hol directory\n"
val _ = FileSys.chDir holdir

fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);

fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

fun die s = (print s; Process.exit Process.failure)

local
  open FileSys
  fun traverse P dir = let
    val dir0 = getDir ()
    val _ = chDir dir
    val ds = openDir "."
    fun dodir found_a_keeper acc =
      case readDir ds of
        NONE => (found_a_keeper, acc)
      | SOME s =>
          if isDir s then dodir found_a_keeper (s::acc)
          else
            if P s then
              (remove s; dodir found_a_keeper acc)
            else
              dodir true acc
    val (found_a_keeper, subdirectories) = dodir false []
    val _ = closeDir ds
    val found_anything_to_keep =
        foldl (fn (d,b) => traverse P d orelse b) found_a_keeper subdirectories
    val _ = chDir dir0
  in
    if not found_anything_to_keep then (rmDir dir; false) else true
  end
  fun is_not_docfile s =
      String.size s < 6 orelse
      String.extract(s, String.size s - 4, NONE) <> ".doc"
  fun is_html_or_adoc s =
      String.size s >= 6 andalso let
        val suff = String.extract(s, String.size s - 5, NONE)
      in
        suff = ".html" orelse suff = ".adoc"
      end
in
  val _ = print "Purging source directory\n"
  val _ = traverse is_not_docfile "src"
      handle OS.SysErr(s,_) => die ("OS error: "^s)
  val _ = print "Purging help directory of HTML and .adoc files\n"
  val _ = traverse is_html_or_adoc "help"
      handle OS.SysErr(s,_) => die ("OS error: "^s)
end

val _ = FileSys.chDir holdir
val _ = print "Removing other unnecessary files: ";
val _ = FileSys.remove (fullPath ["help", "HOL.Help"])
    handle Interrupt => raise Interrupt | _ => ()
val _ = print "help/HOL.Help, "
val _ = (FileSys.chDir "help", FileSys.chDir "src")
val _ = systeml [fullPath [holdir, "bin", "Holmake"], "cleanAll"]
val _ = print "cleanable stuff in help/src\n\n"

val _ = print "Compiling win-config.exe"
val _ = FileSys.chDir (fullPath [holdir, "tools"])
val _ = if systeml ["mosmlc", "-I", "Holmake", "-o", "win-config.exe",
                    "win-config.sml"] = Process.success then ()
        else (print "Compilation failed!\n"; Process.exit Process.failure)
val _ = FileSys.chDir holdir


val header = "\
\[Setup]\n\
\AppName            = HOL\n\
\AppVerName         = HOL 4 - "^sysname^"\n\
\AppVersion         = "^sysname^"\n\
\AppUpdatesURL      = http://hol.sf.net\n\
\AppPublisher       = HOL Developers\n\
\DefaultDirName     = {pf}\\Hol\n\
\DefaultGroupName   = HOL\n\
\Compression        = bzip\n\
\OutputBaseFilename = HOL-install\n";

fun mem s [] = false | mem s (h::t) = s = h orelse mem s t

fun traverse worklist acc excludes =
  case worklist of
    [] => acc
  | (dir::rest) => let
      open FileSys
      val ds = openDir dir
      fun alldirs filefound worklist =
        case readDir ds of
          NONE => (filefound, worklist)
        | SOME f0 => let
            val f = Path.concat(dir, f0)
          in
            if isDir f then
              if not (mem f0 excludes) then
                alldirs filefound (f::worklist)
              else
                alldirs filefound worklist
            else alldirs true worklist
          end
      val (filefound, newworklist) = alldirs false rest
      val _ = closeDir ds
    in
      traverse newworklist ((dir,filefound)::acc) excludes
    end handle OS.SysErr(s,_) => die ("OS error: "^s)

fun initial_directories excludes = let
  open FileSys
  val ds = openDir "."
  fun readf filefound acc =
    case readDir ds of
      NONE => (filefound, acc)
    | SOME f =>
        if isDir f then
          if not (mem f excludes) then
            readf filefound (f::acc)
          else
            readf filefound acc
        else readf true acc
  val (filefound, result) = readf false []
  val _ = closeDir ds
in
  (filefound, List.rev result)
end handle OS.SysErr(s,_) => die ("OS error: "^s)

fun alldirs excludes = let
  val (filefound, ids) = initial_directories excludes
in
  (filefound, List.rev (traverse ids [] excludes))
end handle OS.SysErr(s,_) => die ("OS error: "^s)

fun trans #"/" = "\\" | trans x = str x
fun dir_string dirname = String.concat ["Name: \"{app}\\",
                                        String.translate trans dirname,
                                        "\"\n"]
fun file_string (dirname0, b) = let
  val dirname = String.translate trans dirname0
in
  if b then
    SOME (String.concat ["Source : \"", dirname, "\\*\"; DestDir : \"{app}\\",
                         dirname, "\"\n"])
  else NONE
end

val icon_section = "\
\[Icons]\n\
\Name : \"{group}\\HOL\" ; FileName : \"{app}\\bin\\hol.bat\" ; WorkingDir: \"{app}\"\n\
\Name : \"{group}\\``HOL``\" ; FileName : \"{app}\\bin\\hol.unquote.bat\" ; WorkingDir: \"{app}\"\n\
\Name : \"{userdesktop}\\HOL\" ; FileName : \"{app}\\bin\\hol.unquote.bat\" ; WorkingDir: \"{app}\"\n"

val run_section = "\
\[Run]\n\
\Filename: \"{app}\\tools\\win-config.exe\"; Parameters: \"\"\"{app}\"\"\"\n";

val _ = let
  val (toplevelfiles, dirs) = alldirs [".HOLMK", "CVS"]
  val outstream = TextIO.openOut "hol98.iss"
  fun print s = TextIO.output(outstream, s)
in
  print header;
  print "\n[Dirs]\n";
  app print (map (dir_string o #1) dirs);
  print "\n[Files]\n";
  if toplevelfiles then print "Source : \"*\"; DestDir : \"{app}\"\n" else ();
  app print (List.mapPartial file_string dirs);
  print "\n";
  print icon_section;
  print "\n";
  print run_section;
  TextIO.closeOut outstream
end handle OS.SysErr(s,_) => die ("OS error: "^s)

end (* structure *)
