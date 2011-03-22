structure Holmake_tools :> Holmake_tools =
struct


open Systeml

structure Path = OS.Path
structure FileSys = OS.FileSys

fun normPath s = OS.Path.toString(OS.Path.fromString s)
fun itlist f L base =
   let fun it [] = base | it (a::rst) = f a (it rst) in it L end;
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);
fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => OS.Path.concat (chunk,path)) slist);

type output_functions = {warn : string -> unit, info : string -> unit,
                         tgtfatal : string -> unit,
                         diag : string -> unit}

fun output_functions {quiet_flag: bool, debug:bool} = let
  val execname = CommandLine.name()
  open TextIO
  fun msg strm s = (output(strm, execname ^ ": "^s^"\n"); flushOut strm)
  fun donothing _ = ()
  val warn = if not quiet_flag then msg stdErr else donothing
  val info = if not quiet_flag then msg stdOut else donothing
  val tgtfatal = msg stdErr
  val diag = if debug then msg stdErr else donothing
in
  {warn = warn, diag = diag, tgtfatal = tgtfatal, info = info}
end

fun do_lastmade_checks (ofns : output_functions) {no_lastmakercheck} = let
  val {warn,diag,...} = ofns
  val mypath = find_my_path()
  val _ = diag ("running "^mypath )
  fun write_lastmaker_file () = let
    val outstr = TextIO.openOut ".HOLMK/lastmaker"
  in
    TextIO.output(outstr, mypath ^ "\n");
    TextIO.closeOut outstr
  end handle IO.Io _ => ()

  fun check_distrib () = let
    open FileSys
    val _ = diag "Looking to see if I am in a HOL distribution."
    fun checkdir () =
        access ("sigobj", [A_READ, A_EXEC]) andalso
        isDir "sigobj" andalso
        access ("bin/Holmake", [A_READ, A_EXEC])
    fun traverse () = let
      val d = getDir()
    in
      if checkdir() then
        SOME (Path.concat (d, "bin/Holmake"))
      else if Path.isRoot d then NONE
      else (chDir Path.parentArc; traverse())
    end
    val start = getDir()
  in
    traverse() before chDir start
  end

  fun lmfile() =
      if not no_lastmakercheck andalso
         FileSys.access (".HOLMK/lastmaker", [FileSys.A_READ])
      then let
          val _ = diag "Found a lastmaker file to look at."
          val istrm = TextIO.openIn ".HOLMK/lastmaker"
        in
          case TextIO.inputLine istrm of
            NONE => (warn "Empty Last Maker file";
                     TextIO.closeIn istrm;
                     write_lastmaker_file())
          | SOME s => let
              open Substring
              val path = string (dropr Char.isSpace (full s))
              val _ = TextIO.closeIn istrm
            in
              if FileSys.access (path, [FileSys.A_READ, FileSys.A_EXEC])
              then
                if mypath = path then ()
                else
                  (warn ("*** Switching to execute "^path);
                   Systeml.exec(path,
                                path::"--nolmbc"::CommandLine.arguments()))
              else (warn "Garbage in Last Maker file";
                    write_lastmaker_file())
            end
        end
      else write_lastmaker_file()
in
  case check_distrib() of
    NONE => let
    in
      diag "Not in a HOL distribution";
      lmfile()
    end
  | SOME p =>
    if p = mypath then diag "In the right HOL distribution"
    else if no_lastmakercheck then
      diag "In the wrong distribution, but --nolmbc takes precedence."
    else
      (warn ("*** Switching to execute "^p);
       Systeml.exec (p, p::"--nolmbc"::CommandLine.arguments()))
end

datatype CodeType =
         Theory of string
       | Script of string
       | Other of string

datatype File =
         SML of CodeType
       | SIG of CodeType
       | UO of CodeType
       | UI of CodeType
       | Unhandled of string

fun string_part0 (Theory s) = s
  | string_part0 (Script s) = s
  | string_part0 (Other s) = s
fun string_part (UO c)  = string_part0 c
  | string_part (UI c)  = string_part0 c
  | string_part (SML c) = string_part0 c
  | string_part (SIG c) = string_part0 c
  | string_part (Unhandled s) = s

fun isProperSuffix s1 s2 =
    if size s1 < size s2 andalso String.isSuffix s1 s2 then
      SOME (String.substring(s2,0,size s2 - size s1))
    else NONE

fun toCodeType s = let
  val possprefix = isProperSuffix "Theory" s
in
  if (isSome possprefix) then Theory (valOf possprefix)
  else let
    val possprefix = isProperSuffix "Script" s
  in
    if isSome possprefix then Script (valOf possprefix)
    else Other s
  end
end

fun toFile s0 = let
  val {base = s, ext} = OS.Path.splitBaseExt s0
in
  case ext of
    SOME "sml" => SML (toCodeType s)
  | SOME "sig" => SIG (toCodeType s)
  | SOME "uo"  => UO (toCodeType s)
  | SOME "ui"  => UI (toCodeType s)
  |    _       => Unhandled s0
end

fun codeToString c =
  case c of
    Theory s => s ^ "Theory"
  | Script s => s ^ "Script"
  | Other s  => s

fun fromFile f =
  case f of
    UO c  => codeToString c ^ ".uo"
  | UI c  => codeToString c ^ ".ui"
  | SIG c => codeToString c ^ ".sig"
  | SML c => codeToString c ^ ".sml"
  | Unhandled s => s

fun file_compare (f1, f2) = String.compare (fromFile f1, fromFile f2)

fun primary_dependent f =
    case f of
      UO c => SOME (SML c)
    | UI c => SOME (SIG c)
    | SML (Theory s) => SOME (SML (Script s))
    | SIG (Theory s) => SOME (SML (Script s))
    | _ => NONE

fun read_files ds P action =
    case OS.FileSys.readDir ds of
      NONE => OS.FileSys.closeDir ds
    | SOME nextfile =>
      (if P nextfile then action nextfile else ();
       read_files ds P action)


fun clean_dir {extra_cleans} = let
  val cdstream = OS.FileSys.openDir "."
  fun to_delete f =
      case (toFile f) of
        UO _ => true
      | UI _ => true
      | SIG (Theory _) => true
      | SML (Theory _) => true
      | _ => false
  fun quiet_remove s = OS.FileSys.remove s handle e => ()
in
  read_files cdstream to_delete quiet_remove;
  app quiet_remove extra_cleans
end

exception DirNotFound
fun clean_depdir {depdirname} = let
  val depds = OS.FileSys.openDir DEPDIR handle
      OS.SysErr _ => raise DirNotFound
in
  read_files depds
             (fn _ => true)
             (fn s => OS.FileSys.remove (fullPath [DEPDIR, s]));
  OS.FileSys.rmDir DEPDIR;
  true
end handle OS.SysErr (mesg, _) => let
           in
             print ("make cleanDeps failed with message: "^mesg^"\n");
             false
           end
         | DirNotFound => true

end (* struct *)
