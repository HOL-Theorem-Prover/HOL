structure Holmake_tools :> Holmake_tools =
struct


open Systeml

structure Path = OS.Path
structure FileSys = OS.FileSys

val DEFAULT_OVERLAY = "Overlay.ui"

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

val kernelid_fname = Path.concat(HOLDIR, ".kernelidstr")
fun checkterm pfx s =
  case OS.Process.getEnv "TERM" of
      NONE => s
    | SOME term =>
      if String.isPrefix "xterm" term then
        pfx ^ s ^ "\027[0m"
      else
        s

val bold = checkterm "\027[1m"
val boldred = checkterm "\027[31m\027[1m"
val boldgreen = checkterm "\027[32m\027[1m"
val boldyellow = checkterm "\027[33m\027[1m"
val red = checkterm "\027[31m"
val dim = checkterm "\027[2m"
val CLR_EOL = "\027[0K" (* ANSI clear to EOL code *)



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

type output_functions = {warn : string -> unit,
                         info : string -> unit,
                         chatty : string -> unit,
                         tgtfatal : string -> unit,
                         diag : string -> unit}

fun die_with message = let
  open TextIO
in
  output(stdErr, message ^ "\n");
  flushOut stdErr;
  OS.Process.exit OS.Process.failure
end

fun shorten_name name =
  if OS.Path.file name = "Holmake" then "Holmake" else name

fun output_functions {usepfx,chattiness=n} = let
  val execname = if usepfx then shorten_name (CommandLine.name()) ^ ": " else ""
  open TextIO
  fun msg strm s =
    if s = "" then ()
    else
      let
        val ss = Substring.full s
        val (pfx_ss,sfx_ss) = Substring.splitl Char.isSpace ss
        val pfx = Substring.string pfx_ss
        val sfx = Substring.string sfx_ss
      in
        output(strm, pfx ^ execname ^ sfx^"\n");
        flushOut strm
      end
  fun donothing _ = ()
  val warn = if n >= 1 then msg stdErr else donothing
  val info = if n >= 1 then msg stdOut else donothing
  val chatty = if n >= 2 then msg stdOut else donothing
  val tgtfatal = msg stdErr
  val diag = if n >= 3 then msg stdErr else donothing
in
  {warn = warn, diag = diag, tgtfatal = tgtfatal, info = info, chatty = chatty}
end

fun exists_readable s = OS.FileSys.access(s, [OS.FileSys.A_READ])

fun check_distrib toolname = let
  val fpath = fullPath
  open FileSys
  fun checkdir () =
    access ("sigobj", [A_READ, A_EXEC]) andalso
    isDir "sigobj" andalso
    access (fpath ["bin", "Holmake"], [A_READ, A_EXEC])
  fun traverse () = let
    val d = getDir()
  in
    if checkdir() then SOME (fpath [d, "bin", toolname])
    else if Path.isRoot d then NONE
    else (chDir Path.parentArc; traverse())
  end
  val start = getDir()
in
  traverse() before chDir start
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
  diag "Looking to see if I am in a HOL distribution.";
  case check_distrib "Holmake" of
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

datatype ArticleType =
         RawArticle of string
       | ProcessedArticle of string

datatype File =
         SML of CodeType
       | SIG of CodeType
       | UO of CodeType
       | UI of CodeType
       | ART of ArticleType
       | Unhandled of string

(* file lists are dependencies *)
datatype buildcmds = Compile of File list
                   | BuildScript of string * File list
                   | BuildArticle of string * File list
                   | ProcessArticle of string

fun string_part0 (Theory s) = s
  | string_part0 (Script s) = s
  | string_part0 (Other s) = s
fun string_part1 (RawArticle s) = s
  | string_part1 (ProcessedArticle s) = s
fun string_part (UO c)  = string_part0 c
  | string_part (UI c)  = string_part0 c
  | string_part (SML c) = string_part0 c
  | string_part (SIG c) = string_part0 c
  | string_part (ART c) = string_part1 c
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

fun toArticleType s = let
  val possprefix = isProperSuffix ".ot" s
in
  if (isSome possprefix) then ProcessedArticle (valOf possprefix)
  else RawArticle s
end

fun toFile s0 = let
  val {base = s, ext} = OS.Path.splitBaseExt s0
in
  case ext of
    SOME "sml" => SML (toCodeType s)
  | SOME "sig" => SIG (toCodeType s)
  | SOME "uo"  => UO (toCodeType s)
  | SOME "ui"  => UI (toCodeType s)
  | SOME "art" => ART (toArticleType s)
  |    _       => Unhandled s0
end

fun codeToString c =
  case c of
    Theory s => s ^ "Theory"
  | Script s => s ^ "Script"
  | Other s  => s

fun articleToString c =
  case c of
    RawArticle s => s
  | ProcessedArticle s => s ^ ".ot"

fun fromFile f =
  case f of
    UO c  => codeToString c ^ ".uo"
  | UI c  => codeToString c ^ ".ui"
  | SIG c => codeToString c ^ ".sig"
  | SML c => codeToString c ^ ".sml"
  | ART c => articleToString c ^ ".art"
  | Unhandled s => s

fun fromFileNoSuf f =
  case f of
    UO c  => codeToString c
  | UI c  => codeToString c
  | SIG c => codeToString c
  | SML c => codeToString c
  | ART a => articleToString a
  | Unhandled s => s

fun member m [] = false
  | member m (x::xs) = if x = m then true else member m xs
fun set_union s1 s2 =
  case s1 of
    [] => s2
  | (e::es) => let
      val s' = set_union es s2
    in
      if member e s' then s' else e::s'
    end
fun delete m [] = []
  | delete m (x::xs) = if m = x then delete m xs else x::delete m xs
fun set_diff s1 s2 = foldl (fn (s2e, s1') => delete s2e s1') s1 s2
fun remove_duplicates [] = []
  | remove_duplicates (x::xs) = x::(remove_duplicates (delete x xs))



fun file_compare (f1, f2) = String.compare (fromFile f1, fromFile f2)

fun primary_dependent f =
    case f of
      UO c => SOME (SML c)
    | UI c => SOME (SIG c)
    | SML (Theory s) => SOME (SML (Script s))
    | SIG (Theory s) => SOME (SML (Script s))
    | ART (RawArticle s) => SOME (SML (Script s))
    | ART (ProcessedArticle s) => SOME (ART (RawArticle s))
    | _ => NONE

fun read_files ds P action =
    case OS.FileSys.readDir ds of
      NONE => OS.FileSys.closeDir ds
    | SOME nextfile =>
      (if P nextfile then action nextfile else ();
       read_files ds P action)

fun quiet_remove s = OS.FileSys.remove s handle e => ()

fun clean_dir {extra_cleans} = let
  val cdstream = OS.FileSys.openDir "."
  fun to_delete f =
      case (toFile f) of
        UO _ => true
      | UI _ => true
      | SIG (Theory _) => true
      | SML (Theory _) => true
      | SML (Script s) =>
          (case OS.Path.ext s of SOME "art" => true | _ => false)
      | ART _ => true
      | _ => false
in
  read_files cdstream to_delete quiet_remove;
  app quiet_remove extra_cleans
end

fun clean_forReloc {holheap} =
  if Systeml.ML_SYSNAME = "poly" then
    case holheap of SOME s => quiet_remove s | _ => ()
  else ()

exception DirNotFound
fun clean_depdir {depdirname} = let
  val depds = OS.FileSys.openDir depdirname handle
      OS.SysErr _ => raise DirNotFound
in
  read_files depds
             (fn _ => true)
             (fn s => OS.FileSys.remove (fullPath [depdirname, s]));
  OS.FileSys.rmDir depdirname;
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
  ignore (OS.Process.system ("/bin/sh -c 'printf \"\\033]0;" ^ s ^ "\\007\"'"))

val terminal_log =
    if Systeml.isUnix then xterm_log
    else (fn s => ())

structure hmdir =
struct

type t = {absdir : string, relpath : string option}

fun op+ (d, e) = Path.mkCanonical (Path.concat(d, e))

fun curdir () = {relpath = SOME (OS.Path.currentArc),
                 absdir = OS.FileSys.getDir()}

fun compare ({absdir = d1, ...} : t, {absdir = d2, ...} : t) =
    String.compare (d1, d2)

fun toString {relpath,absdir} =
    case relpath of
        NONE => absdir
      | SOME p => p

fun toAbsPath {relpath,absdir} = absdir

fun fromPath {origin,path} =
    if Path.isAbsolute path then {relpath = NONE, absdir = path}
    else
      {relpath = SOME path, absdir = origin + path}

fun extendp {base = {relpath, absdir}, extension} = let
  val relpath_str = case relpath of NONE => "NONE"
                                  | SOME s => "SOME("^s^")"
in
  if Path.isAbsolute extension then {relpath = NONE, absdir = extension}
  else
      case relpath of
          NONE => {absdir = absdir + extension, relpath = NONE}
        | SOME p => {relpath = SOME (p + extension),
                     absdir = absdir + extension}
end

fun extend {base, extension} =
    extendp {base = base, extension = toString extension}

fun sort l = let
  fun foldthis1 ({absdir,relpath}, acc) =
      case Binarymap.peek (acc, absdir) of
          NONE => Binarymap.insert(acc, absdir, relpath)
        | SOME NONE => Binarymap.insert(acc, absdir, relpath)
        | _ => acc
  val m = foldl foldthis1 (Binarymap.mkDict String.compare) l
  fun foldthis2 (abs,rel,acc) = {absdir = abs, relpath = rel} :: acc
in
  Binarymap.foldr foldthis2 [] m
end

end (* hmdir struct *)

fun process_hypat_options s = let
  open Substring
  val ss = full s
  fun recurse (noecho, ignore_error, ss) =
      if noecho andalso ignore_error then
        {noecho = true, ignore_error = true,
         command = string (dropl (fn c => c = #"@" orelse c = #"-") ss)}
      else
        case getc ss of
          NONE => {noecho = noecho, ignore_error = ignore_error,
                   command = ""}
        | SOME (c, ss') =>
          if c = #"@" then recurse (true, ignore_error, ss')
          else if c = #"-" then recurse (noecho, true, ss')
          else { noecho = noecho, ignore_error = ignore_error,
                 command = string ss }
in
  recurse (false, false, ss)
end

local
  fun split p = let val {base, ext} = OS.Path.splitBaseExt p in (base, ext) end
in
  fun target_string l =
    let
      val (names, e) = ListPair.unzip (List.map split l)
      val exts = List.mapPartial (fn x => x) e
      val n = List.length exts
    in
      case names of
         [] => ""
       | [_] => List.hd l
       | h :: t => if List.all (fn x => x = h) t andalso List.length e = n
                     then if n = 2 andalso String.isSuffix "Theory" h
                            then h
                          else h ^ ".{" ^ String.concatWith "," exts ^ "}"
                   else String.concatWith " " l
    end
end

type include_info = {includes : string list, preincludes : string list }
type 'dir holmake_dirinfo = {visited : hmdir.t Binaryset.set, includes : 'dir list,
                             preincludes : 'dir list}
type 'dir holmake_result = 'dir holmake_dirinfo option

(* ----------------------------------------------------------------------

    maybe_recurse

    this function doesn't handle all recursion, just one level's
    worth. In other words, the master Holmake calls this function, and
    this then arranges the recursive calls into the various include
    directories that need to happen. The holmake that gets called in
    those directories (via the hm parameter) will in turn call this
    function for recursion at that level in the "tree".

    The local_build/k parameter is how the maybe_recurse function
    finishes off; this parameter is called when all of the necessary
    recursion has been performed and work should be done in the
    current ("local") directory.

    Finally, what of the dirinfo?

    This record includes
          origin: the absolute path to the very first directory
        includes: the includes that the local directory knows about
                  (which will have come from the command-line or
                  INCLUDES lines in the local Holmakefile
     preincludes: similarly
         visited: a set of visited directories (with directories
                  expressed as absolute paths)

    The includes and preincludes are clearly useful when it comes time to
    do any local work, but also specify how the recursion is to happen.

    Now, the recursion into those directories may result in extra
    includes and preincludes.
   ---------------------------------------------------------------------- *)
fun maybe_recurse {warn,diag,no_prereqs,hm,dirinfo,dir,local_build=k,cleantgt} =
let
  val {includes,preincludes,visited} = dirinfo
  val _ = diag ("maybe_recurse: includes = [" ^
                String.concatWith ", " includes ^ "]")
  val _ = diag ("maybe_recurse: preincludes = [" ^
                String.concatWith ", " preincludes ^ "]")
  val k = fn ii => (terminal_log ("Holmake: "^nice_dir (hmdir.toString dir));
                    k ii)
  val tgts = case cleantgt of SOME s => [s] | NONE => []
  fun recurse (acc as {visited,includes,preincludes}) newdir = let
  in
    if Binaryset.member(visited, newdir) then SOME acc
    else let
      val _ = warn ("Recursively calling Holmake in " ^ hmdir.toString newdir)
      val _ = terminal_log ("Holmake: "^nice_dir (hmdir.toString newdir))
      val result =
          case hm {dir = newdir, visited = visited, targets = tgts} of
              NONE => NONE
            | SOME {visited,includes = inc0, preincludes = pre0} =>
              SOME {visited = visited,
                    includes = hmdir.sort (includes @ inc0),
                    preincludes = hmdir.sort (preincludes @ pre0)}
    in
      warn ("Finished recursive invocation in "^hmdir.toString newdir);
      terminal_log ("Holmake: "^nice_dir (hmdir.toString dir));
      FileSys.chDir (hmdir.toAbsPath dir);
      case result of
          SOME{includes=incs,preincludes=pre,...} =>
          (diag ("Recursively computed includes = " ^
                 String.concatWith ", " (map hmdir.toString incs));
           diag ("Recursively computed pre-includes = " ^
                 String.concatWith ", " (map hmdir.toString pre)))
        | NONE => ();
      result
    end
  end
  fun do_em (accg as {includes,preincludes,...}) dirs =
      case dirs of
          [] =>
          let
            val f = map hmdir.toAbsPath
          in
            if k {includes=f includes,preincludes=f preincludes} then SOME accg
            else NONE
          end
        | x::xs =>
          let
          in
            case recurse accg x of
                SOME result => do_em result xs
              | NONE => NONE
          end
  val visited = Binaryset.add(visited, dir)
  fun canon i = hmdir.extendp {base = dir, extension = i}
  val canonl = map canon
in
  if no_prereqs then
    if k {includes = #includes dirinfo, preincludes = #preincludes dirinfo} then
      SOME {visited = visited, includes = map canon includes,
            preincludes = map canon preincludes}
    else NONE
  else let
      fun f idirs = map canon idirs
      val possible_calls = hmdir.sort (f (preincludes @ includes))
    in
      do_em {visited = visited, includes = f includes, preincludes = f preincludes}
            possible_calls
    end
end

fun find_files ds P =
  let
    fun recurse acc =
      case OS.FileSys.readDir ds of
          NONE => (OS.FileSys.closeDir ds; List.rev acc)
        | SOME fname => if P fname then recurse (fname::acc)
                        else recurse acc
  in
    recurse []
  end

fun generate_all_plausible_targets warn first_target =
    case first_target of
        SOME s => [toFile s]
      | NONE =>
        let
          val cds = OS.FileSys.openDir "."
          fun not_a_dot f = not (String.isPrefix "." f)
          fun ok_file f =
              case (toFile f) of
                  SIG (Theory _) => false
                | SIG _ => true
                | SML (Script s) =>
                  (case OS.Path.ext s of
                       SOME "art" => false
                       (* can be generated as temporary by opentheory
                          machinery *)
                     | SOME _ =>
                         (warn ("Theory names (e.g., "^f^
                                ") can't include '.' characters");
                          false)
                     | NONE => true)
                | SML (Theory _) => false
                | SML _ => true
                | _ => false
          val src_files = find_files cds (fn s => ok_file s andalso not_a_dot s)
          fun src_to_target (SIG (Script s)) = UO (Theory s)
            | src_to_target (SML (Script s)) = UO (Theory s)
            | src_to_target (SML s) = (UO s)
            | src_to_target (SIG s) = (UI s)
            | src_to_target _ = raise Fail "Can't happen"
          val initially = map (src_to_target o toFile) src_files
          fun remove_sorted_dups [] = []
            | remove_sorted_dups [x] = [x]
            | remove_sorted_dups (x::y::z) = if x = y then remove_sorted_dups (y::z)
                                             else x :: remove_sorted_dups (y::z)
        in
          remove_sorted_dups (Listsort.sort file_compare initially)
        end

(* dependency analysis *)
exception HolDepFailed
fun runholdep {ofs, extras, includes, arg, destination} = let
  val {chatty, diag, warn, ...} : output_functions = ofs
  val _ = chatty ("Analysing "^fromFile arg)
  fun buildables s = let
    val f = toFile s
    val files =
        case f of
          SML (ss as Script t) => [UI ss, UO ss, SML (Theory t),
                                   SIG (Theory t), UI (Theory t),
                                   UO (Theory t), ART (RawArticle t), f]
        | SML ss => [UI ss, UO ss, f]
        | SIG ss => [UI ss, f]
        | ART (RawArticle s) => [ART (ProcessedArticle s), f]
        | x => [x]
  in
    map fromFile files
  end
  val buildable_extras = List.concat (map buildables extras)
  val _ = diag ("Running Holdep on "^fromFile arg^" with includes = [" ^
                String.concatWith ", " includes ^ "], assumes = [" ^
                String.concatWith ", " buildable_extras ^"]")
  val holdep_result =
    Holdep.main {assumes = buildable_extras, diag = diag,
                 includes = includes, fname = fromFile arg}
    handle Holdep.Holdep_Error s =>
             (warn "Holdep failed: s"; raise HolDepFailed)
         | Interrupt => raise Interrupt
         | e => (warn ("Holdep exception: "^General.exnMessage e);
                 raise HolDepFailed)
  fun myopen s =
    if FileSys.access(DEPDIR, []) then
      if FileSys.isDir DEPDIR then TextIO.openOut s
      else die_with ("Want to put dependency information in directory "^
                     DEPDIR^", but it already exists as a file")
    else
     (chatty ("Trying to create directory "^DEPDIR^" for dependency files");
      FileSys.mkDir DEPDIR;
      TextIO.openOut s
     )
  open TextIO
  val outstr = myopen (normPath destination)
in
  output(outstr, Holdep.encode_for_HOLMKfile holdep_result);
  closeOut outstr
end

(* pull out a list of files that target depends on from depfile.  *)
(* All files on the right of a colon are assumed to be dependencies.
   This is despite the fact that holdep produces two entries when run
   on fooScript.sml files, one for fooScript.uo, and another for fooScript
   itself, we actually want all of those dependencies in one big chunk
   because the production of fooTheory.{sig,sml} is done as one
   atomic step from fooScript.sml. *)
fun first f [] = NONE
  | first f (x::xs) = case f x of NONE => first f xs | res => res

fun get_dependencies_from_file depfile = let
  fun get_whole_file s = let
    open TextIO
    val instr = openIn (normPath s)
  in
    inputAll instr before closeIn instr
  end
  fun parse_result s = let
    val lines = String.fields (fn c => c = #"\n") (collapse_bslash_lines s)
    fun process_line line = let
      val (lhs0, rhs0) = Substring.splitl (fn c => c <> #":")
                                          (Substring.full line)
      val lhs = Substring.string lhs0
      val rhs = Substring.string (Substring.slice(rhs0, 1, NONE))
        handle Subscript => ""
    in
      realspace_delimited_fields rhs
    end
    val result = List.concat (map process_line lines)
  in
    List.map toFile result
  end
in
  parse_result (get_whole_file depfile)
end

(* a function that given a product file, figures out the argument that
   should be passed to runholdep in order to get back secondary
   dependencies. *)

fun holdep_arg (UO c) = SOME (SML c)
  | holdep_arg (UI c) = SOME (SIG c)
  | holdep_arg (SML (Theory s)) = SOME (SML (Script s))
  | holdep_arg (SIG (Theory s)) = SOME (SML (Script s))
  | holdep_arg (ART (RawArticle s)) = SOME (SML (Script s))
  | holdep_arg (ART (ProcessedArticle s)) = SOME (ART (RawArticle s))
  | holdep_arg _ = NONE

fun mk_depfile_name DEPDIR s = fullPath [DEPDIR, s^".d"]

infix forces_update_of
fun (f1 forces_update_of f2) = let
  open Time
in
  FileSys.access(f1, []) andalso
  (not (FileSys.access(f2, [])) orelse FileSys.modTime f1 > FileSys.modTime f2)
end


fun get_direct_dependencies {incinfo,DEPDIR,output_functions,extra_targets} f =
let
  val fname = fromFile f
  val arg = holdep_arg f  (* arg is file to analyse for dependencies *)
  val {includes,preincludes} = incinfo
in
  if isSome arg then let
    val arg = valOf arg
    val argname = fromFile arg
    val depfile = mk_depfile_name DEPDIR argname
    val _ =
      if argname forces_update_of depfile then
        runholdep {ofs = output_functions, extras = extra_targets,
                   includes = preincludes @ includes, arg = arg,
                   destination = depfile}
      else ()
    val phase1 =
      (* circumstances can arise in which the dependency file won't be
         built, and won't exist; mainly because the file we're trying to
         compute dependencies for doesn't exist either.  In this case, we
         can only return the empty list *)
      if exists_readable depfile then
        get_dependencies_from_file depfile
      else
        []
  in
    case f of
        UO (Theory s) => UI (Theory s) :: phase1
      | UO x =>
        if FileSys.access(fromFile (SIG x), []) andalso
           List.all (fn f => f <> SIG x) phase1
        then
          UI x :: phase1
        else
          phase1
      | _ => phase1
  end
  else
    []
end



end (* struct *)
