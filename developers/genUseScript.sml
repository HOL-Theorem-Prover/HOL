
use "../tools/Holmake/HFS_NameMunge.sig";
use "../tools/Holmake/poly/HFS_NameMunge.sml";
use "../tools/Holmake/HOLFS_dtype.sml";
use "../tools/Holmake/HOLFileSys.sig";
use "../tools/Holmake/HOLFileSys.sml";
use "../tools/Holmake/AttributeSyntax.sig";
use "../tools/Holmake/AttributeSyntax.sml";
use "../tools/Holmake/GetOpt.sig";
use "../tools/Holmake/GetOpt.sml";
use "../tools-poly/poly/Binaryset.sig";
use "../tools-poly/poly/Binaryset.sml";
use "../tools-poly/poly/Binarymap.sig";
use "../tools-poly/poly/Binarymap.sml";
use "../tools/Holmake/Systeml.sig";
use "../tools-poly/Holmake/Systeml.sml";
use "../tools/Holmake/holpathdb.sig";
use "../tools/Holmake/holpathdb.sml";

val _ = holpathdb.extend_db {vname = "HOLDIR", path = Systeml.HOLDIR}

infix |>
fun x |> f = f x

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

fun mkBuffer () = let
  val buf = ref ([] : string list)
  fun push s = buf := s :: !buf
  fun read () = let
    val contents = String.concat (List.rev (!buf))
  in
    buf := [contents];
    contents
  end
  fun reset() = buf := []
in
  (push, read, reset)
end;

val _ = use "../tools/Holmake/HolLex.sml";
val _ = use "../tools/Holmake/HolParser.sig";
val _ = use "../tools/Holmake/HolParser.sml";
val _ = use "../tools/Holmake/Holdep_tokens.sig"
val _ = use "../tools/Holmake/Holdep_tokens.sml";


infix ^^
val op^^ = OS.Path.concat

fun addIfReadable src fname rest =
  if OS.FileSys.access(fname, [OS.FileSys.A_READ]) then (src,fname)::rest
  else rest

fun ToplevelLoad {worklist, alreadySeen, acc} (src,s) =
  let
    val basefname = if OS.Path.isRelative s then Systeml.HOLDIR ^^ "sigobj" ^^ s
                    else s
    val uo = basefname ^ ".uo"
    val ui = basefname ^ ".ui"
  in
    {worklist = worklist |> addIfReadable src uo |> addIfReadable src ui,
     alreadySeen = Binaryset.add(alreadySeen, s),
     acc = acc}
  end

fun load1 (S as {worklist, alreadySeen, acc}) (src,s) =
  let
    fun doSource () =
      {worklist = worklist,
       alreadySeen = Binaryset.add(alreadySeen, s),
       acc = s::acc}
    fun doUOI () =
      let
        val instrm = TextIO.openIn s
        fun recurse acc lnum =
          case TextIO.inputLine instrm of
              NONE => (TextIO.closeIn instrm ; acc)
            | SOME line =>
              let
                val newfile = String.substring(line, 0, size line - 1)
                                  |> holpathdb.subst_pathvars
              in
                recurse ((s ^ ":" ^ Int.toString lnum, newfile) :: acc)
                        (lnum + 1)
              end
      in
        {worklist = List.rev (recurse [] 1) @ worklist,
         alreadySeen = Binaryset.add(alreadySeen, s),
         acc = acc}
      end
  in
    if Binaryset.member(alreadySeen, s) then S
    else
      case OS.Path.ext s of
          SOME "sig" => doSource()
        | SOME "sml" => doSource()
        | SOME "uo" => doUOI()
        | SOME "ui" => doUOI()
        | _ => ToplevelLoad S (src,s)
  end

fun dowork {worklist, alreadySeen, acc} =
  case worklist of
      [] => List.rev acc
    | h :: rest =>
        dowork (load1 {worklist = rest, alreadySeen = alreadySeen, acc = acc} h)

type config = {dohelp : bool, prefix : string, prelude : string,
               suffix : string}

val default_config = {dohelp = false, prefix = "", prelude = "", suffix = ""}

val HOLprelude =
    "local val dir = OS.FileSys.getDir()\n\
    \val _ = OS.FileSys.chDir \"" ^ Systeml.HOLDIR ^^ "tools-poly" ^ "\";\n" ^
    "val _ = use \"poly/poly-init2.ML\";\n\
    \val _ = OS.FileSys.chDir dir in end;\n\
    \use \"" ^ Systeml.HOLDIR ^^ "tools" ^^ "Holmake" ^^
    "FunctionalRecordUpdate.sml" ^ "\";\n\
    \val use = QUse.use;\n"

fun turnOnHelp _ = {dohelp = true, prefix = "", prelude = "", suffix = ""}
fun turnOnHOL {dohelp,...} = {dohelp = dohelp, prefix = "use \"",
                              suffix = "\";",
                              prelude = HOLprelude}
fun setPrefix s {prefix,dohelp,suffix,prelude} =
  {prefix = s, dohelp = dohelp, suffix = suffix, prelude = prelude}
fun setSuffix s {prefix,dohelp,suffix,prelude} =
  {prefix = prefix, dohelp = dohelp, suffix = s, prelude = prelude}

val options : (config -> config) GetOpt.opt_descr list = let
  open GetOpt
in
  [{short = "h", long = ["help"],
    help = "Show some help information",
    desc = NoArg (fn () => turnOnHelp)},
   {short = "", long = ["hol"],
    help = "Generate a poly-usable source file",
    desc = NoArg (fn () => turnOnHOL)},
   {short = "p", long = ["prefix"],
    help = "String to be emitted before each line of output",
    desc = ReqArg (setPrefix, "prefix")},
   {short = "s", long = ["suffix"],
    help = "String emitted after each line of output (before \\n)",
    desc = ReqArg (setPrefix, "prefix")}
  ]
end


fun usage() =
  print (GetOpt.usageInfo {
            header = "Usage:\n  "^CommandLine.name()^
                     " [options] fname\n\nOptions:",
            options = options});

val optionConfig = {argOrder = GetOpt.RequireOrder,
                    errFn = die,
                    options = options}

fun main () =
  let
    val (optChanges,fnames) =
        GetOpt.getOpt optionConfig (CommandLine.arguments())
        handle e => die (General.exnMessage e)
    val config = List.foldl (fn (f,acc) => f acc) default_config optChanges
  in
    if #dohelp config then
      (usage(); OS.Process.exit OS.Process.success)
    else
      case fnames of
          [fname] =>
          let
            val deps = Holdep_tokens.file_deps fname
                       handle e => die (General.exnMessage e)
            val result =
                dowork {worklist =
                        Binarymap.foldr
                          (fn (s,_,acc) => ("toplevel", s) :: acc)
                          []
                          deps,
                        acc = [], alreadySeen = Binaryset.empty String.compare}
          in
            print (#prelude config) ;
            List.app
              (fn s => print (#prefix config ^ s ^ #suffix config ^ "\n"))
              result
          end
        | _ => (usage(); die "")
  end
