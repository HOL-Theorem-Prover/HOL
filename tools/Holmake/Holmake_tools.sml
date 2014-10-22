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

val spacify = String.concatWith " "
fun nspaces f n = if n <= 0 then () else (f " "; nspaces f (n - 1))
fun collapse_bslash_lines s = let
  val charlist = explode s
  fun trans [] = []
    | trans (#"\\"::(#"\n"::rest)) = trans rest
    | trans (x::xs) = x :: trans xs
in
  implode (trans charlist)
end

fun realspace_delimited_fields s = let
  open Substring
  fun inword cword words ss =
      case getc ss of
        NONE => List.rev (implode (List.rev cword) :: words)
      | SOME (c,ss') => let
        in
          case c of
            #" " => outword (implode (List.rev cword) :: words) ss'
          | #"\\" => let
            in
              case getc ss' of
                NONE => List.rev (implode (List.rev (c::cword)) :: words)
              | SOME (c',ss'') => inword (c'::cword) words ss''
            end
          | _ => inword (c::cword) words ss'
        end
  and outword words ss =
      case getc ss of
        NONE => List.rev words
      | SOME(c, ss') => let
        in
          case c of
            #" " => outword words ss'
          | _ => inword [] words ss
        end
in
  outword [] (full s)
end

type output_functions = {warn : string -> unit, info : string -> unit,
                         tgtfatal : string -> unit,
                         diag : string -> unit}

fun die_with message = let
  open TextIO
in
  output(stdErr, message ^ "\n");
  flushOut stdErr;
  OS.Process.exit OS.Process.failure
end

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

fun exists_readable s = OS.FileSys.access(s, [OS.FileSys.A_READ])

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
                   warn ("*** (Honouring last Holmake call in this directory)");
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
       warn ("*** (As we are in/under its HOLDIR)");
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

val nice_dir =
    case OS.Process.getEnv "HOME" of
        SOME h => (fn s => if String.isPrefix h s then
                             "~" ^ String.extract(s,size h,NONE)
                           else s)
      | NONE => (fn s => s)

fun xterm_log s =
    ignore (OS.Process.system ("/bin/bash -c 'echo -ne \"\\033]0;" ^ s ^ "\\007\"'"))

val terminal_log =
    if Systeml.isUnix then xterm_log
    else (fn s => ())


fun maybe_recurse {warn,no_prereqs,hm,visited,includes,dir,local_build=k,
                   cleantgt} =
let
  val {abspath=dir,relpath} = dir
  val k = fn () => (terminal_log ("Holmake: "^nice_dir dir); k())
  val tgts = case cleantgt of SOME s => [s] | NONE => []
  fun recurse visited (newdir,nm) =
      if Binaryset.member(visited, newdir) then SOME visited
      else let
          val newrelpath =
              if Path.isAbsolute nm then NONE
              else
                case relpath of
                  NONE => NONE
                | SOME d => SOME (Path.mkCanonical (Path.concat(d, nm)))
          val nm = case newrelpath of NONE => newdir | SOME d => d
          val _ = warn ("Recursively calling Holmake in "^nm)
          val _ = terminal_log ("Holmake: "^nice_dir nm)
        in
          hm {relpath=newrelpath,abspath=newdir} visited [] tgts
          before
          (warn ("Finished recursive invocation in "^nm);
           terminal_log ("Holmake: "^nice_dir dir);
           FileSys.chDir dir)
        end
  fun do_em accg [] = if k() then SOME accg else NONE
    | do_em accg (x::xs) = let
      in
        case recurse accg x of
          SOME g' => do_em g' xs
        | NONE => NONE
      end
  val visited = Binaryset.add(visited, dir)
in
  if no_prereqs then
    if k() then SOME visited else NONE
  else let
      fun foldthis (dir, m) =
          Binarymap.insert(m, FileSys.fullPath dir, dir)
          handle OS.SysErr _ =>
                 (warn ("Includes path "^dir^" looks bogus");
                  m)
      val possible_calls = List.foldr foldthis
                                      (Binarymap.mkDict String.compare)
                                      includes

    in
      do_em visited (Binarymap.listItems possible_calls)
    end
end

fun generate_all_plausible_targets first_target = let
  val extra_targets = case first_target of NONE => [] | SOME s => [toFile s]
  fun find_files ds P =
    case OS.FileSys.readDir ds of
      NONE => (OS.FileSys.closeDir ds; [])
    | SOME fname => if P fname then fname::find_files ds P
                               else find_files ds P
  val cds = OS.FileSys.openDir "."
  fun not_a_dot f = not (String.isPrefix "." f)
  fun ok_file f =
    case (toFile f) of
      SIG _ => true
    | SML _ => true
    | _ => false
  val src_files = find_files cds (fn s => ok_file s andalso not_a_dot s)
  fun src_to_target (SIG (Script s)) = UO (Theory s)
    | src_to_target (SML (Script s)) = UO (Theory s)
    | src_to_target (SML s) = (UO s)
    | src_to_target (SIG s) = (UI s)
    | src_to_target _ = raise Fail "Can't happen"
  val initially = map (src_to_target o toFile) src_files @ extra_targets
  fun remove_sorted_dups [] = []
    | remove_sorted_dups [x] = [x]
    | remove_sorted_dups (x::y::z) = if x = y then remove_sorted_dups (y::z)
                                     else x :: remove_sorted_dups (y::z)
in
  remove_sorted_dups (Listsort.sort file_compare initially)
end

end (* struct *)
