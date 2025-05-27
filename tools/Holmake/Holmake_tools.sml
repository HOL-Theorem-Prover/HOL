structure Holmake_tools :> Holmake_tools =
struct


open Systeml
open terminal_primitives
open Holmake_tools_dtype
open HOLFileSys

structure FileSys = HOLFileSys
fun K x y = x

fun |>(x,f) = f x
infix |>

fun memoise cmp f =
    let
      val stash = ref (Binarymap.mkDict cmp)
      fun lookup s =
          case Binarymap.peek(!stash, s) of
              NONE =>
              let
                val result = f s
              in
                stash := Binarymap.insert(!stash, s, result);
                result
              end
            | SOME r => r
    in
      lookup
    end


structure Exception = struct
  datatype 'a result = Res of 'a | Exn of exn
  fun get_res (Res r) = SOME r | get_res _ = NONE
  fun get_exn (Exn e) = SOME e | get_exn _ = NONE
  fun capture f x = Res (f x) handle e => Exn e
  fun release (Res r) = r | release (Exn e) = raise e
end


structure Path = OS.Path

val DEFAULT_OVERLAY = "Overlay.ui"
fun member m [] = false
  | member m (x::xs) = if x = m then true else member m xs
fun set_unionl s1 s2 =
  case s1 of
    [] => s2
  | (e::es) => let
      val s' = set_unionl es s2
    in
      if member e s' then s' else e::s'
    end
fun delete m [] = []
  | delete m (x::xs) = if m = x then delete m xs else x::delete m xs
fun set_diffl s1 s2 = foldl (fn (s2e, s1') => delete s2e s1') s1 s2
fun remove_duplicates [] = []
  | remove_duplicates (x::xs) = x::(remove_duplicates (delete x xs))


type 'a cmp = 'a * 'a -> order
fun pair_compare (c1,c2) ((a1,b1), (a2,b2)) =
  case c1(a1,a2) of
      EQUAL => c2(b1,b2)
    | x => x
fun lex_compare c (l1, l2) =
  case (l1,l2) of
      ([],[]) => EQUAL
    | ([], _) => LESS
    | (_, []) => GREATER
    | (h1::t1, h2::t2) => case c(h1,h2) of EQUAL => lex_compare c (t1,t2)
                                         | x => x
fun inv_img_cmp f c (a1,a2) = c (f a1, f a2)

fun normPath s = OS.Path.toString(OS.Path.fromString s)
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
    if TERM_isANSI () then pfx ^ s ^ "\027[0m"
    else s

val bold = checkterm "\027[1m"
val boldred = checkterm "\027[31m\027[1m"
val boldgreen = checkterm "\027[32m\027[1m"
val boldyellow = checkterm "\027[33m\027[1m"
val red = checkterm "\027[31m"
val dim = checkterm "\027[2m"
val CLR_EOL = "\027[0K" (* ANSI clear to EOL code *)

fun strip_codes s =
    let
      fun recurse A ss =
          let
            open Substring
            val (pfx,sfx) = position "\027[" ss
          in
            if isEmpty sfx then concat (List.rev (pfx :: A))
            else
              let
                val sfx = slice(sfx,2,NONE)
                val sfx = dropl (fn c => Char.isDigit c orelse c = #";") sfx
                val sfx = slice(sfx,1,NONE) (* terminating char *)
              in
                recurse (pfx::A) sfx
              end
          end
    in
      recurse [] (Substring.full s)
    end
fun noesc_size s = String.size (strip_codes s)

fun optbind x f =
  case x of
      SOME y => f y
    | _ => NONE
fun optchoice (opt1, opt2) =
  case opt1 of
      NONE => opt2()
    | _ => opt1
infix ++
val op++ = optchoice
fun isc r = Int.scan StringCvt.DEC r
fun char_reader (s, i) = if size s <= i then NONE
                         else SOME (String.sub(s,i), (s,i+1))
fun estbind m f s =
  case m s of
      NONE => NONE
    | SOME(r,s') => f r s'

fun run s =
  let
    val outfile = OS.FileSys.tmpName()
    val res = OS.Process.system (String.concatWith " " [s,"1>",outfile,"2>&1"])
    val output =
        let
          val istrm = openIn outfile
        in
          inputAll istrm before
          closeIn istrm before
          OS.FileSys.remove outfile
        end handle IO.Io _ => ""
  in
    if OS.Process.isSuccess res then SOME output else NONE
  end

fun optassert P x = if P x then SOME x else NONE

fun getWidth0 () =
  let
    fun tputresult istr = Int.fromString istr
    fun sttyresult i2str =
      Option.map #1
                 (estbind (isc char_reader) (fn _ => isc char_reader)
                          (i2str, 0))
    fun positive m x = optbind (m x) (optassert (fn i => i > 0))
  in
    optbind (run "stty size") (positive sttyresult) ++
    (fn _ => optbind (run "tput cols") (positive tputresult)) ++
    (fn _ => SOME 80)
  end

fun getWidth() = valOf (getWidth0())

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
                         info_inline : string -> unit,
                         info_inline_end : unit -> unit,
                         chatty : string -> unit,
                         tgtfatal : string -> unit,
                         diag : string -> (unit -> string) -> unit}
type 'a ofn_update = ('a -> 'a) -> output_functions -> output_functions
fun fupd_info_inline f {warn,info,info_inline,info_inline_end,chatty,tgtfatal,diag} =
    {warn = warn,info = info, info_inline_end = info_inline_end, info_inline = f info_inline,
     chatty = chatty, tgtfatal = tgtfatal, diag = diag}
fun fupd_info_inline_end f {warn,info,info_inline,info_inline_end,chatty,tgtfatal,diag} =
    {warn = warn,info = info, info_inline_end = f info_inline_end, info_inline = info_inline,
     chatty = chatty, tgtfatal = tgtfatal, diag = diag}
fun fupd_info f {warn,info,info_inline,info_inline_end,chatty,tgtfatal,diag} =
    {warn = warn,info = f info, info_inline_end = info_inline_end, info_inline = info_inline,
     chatty = chatty, tgtfatal = tgtfatal, diag = diag}
fun quieten_info ofns = ofns |> fupd_info_inline_end (K (K ()))
                             |> fupd_info_inline (K (K ()))
                             |> fupd_info (K (K ()))

fun die_with message = let
in
  stdErr_out ("\n\nHolmake died: " ^ message ^ "\n");
  OS.Process.exit OS.Process.failure
end

fun shorten_name name =
  if OS.Path.file name = "Holmake" then "Holmake" else name

fun output_functions {usepfx,chattiness=n,debug} = let
  val execname = if usepfx then shorten_name (CommandLine.name()) ^ ": " else ""
  open HOLFileSys
  fun msg inlinep strm s =
    if s = "" then ()
    else
      let
        val ss = Substring.full s
        val (pfx_ss,sfx_ss) = Substring.splitl Char.isSpace ss
        val pfx = (if inlinep then "\r" else "") ^ Substring.string pfx_ss
        val sfx = Substring.string sfx_ss ^ (if inlinep then CLR_EOL else "\n")
      in
        output(strm, pfx ^ execname ^ sfx);
        flushOut strm
      end
  fun donothing _ = ()
  val warn = if n >= 1 then msg false stdErr else donothing
  val info = if n >= 1 then msg false stdOut else donothing
  val fancyp = strmIsTTY stdOut andalso TERM_isANSI()
  val (info_inline, info_inline_end) =
      if n >= 1 then
        if fancyp then
          (msg true stdOut, fn () => output(stdOut, "\n"))
        else (msg false stdOut, donothing)
      else (donothing, donothing)
  val chatty = if n >= 2 then msg false stdOut else donothing
  val tgtfatal = msg false stdErr
  fun pfx p s = "["^p^"] "^s
  val diag =
      if n >= 3 then
        case debug of
            NONE => (fn _ => fn _ => ())
          | SOME {ins,outs} =>
            (fn cat => fn sf => if member cat outs then () else
                                if null ins orelse member cat ins then
                                  msg false stdErr (pfx cat (sf()))
                                else ())
      else fn _ => donothing
in
  {warn = warn, diag = diag, tgtfatal = tgtfatal, info = info, chatty = chatty,
   info_inline_end = info_inline_end, info_inline = info_inline}
end

val default_ofns =
    output_functions {usepfx = true, chattiness = 1, debug = NONE}

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
  val diag = diag "lastmadecheck"
  val mypath = find_my_path()
  val _ = diag (K ("running "^mypath))
  fun write_lastmaker_file () = let
    val outstr = openOut ".HOLMK/lastmaker"
  in
    output(outstr, mypath ^ "\n");
    closeOut outstr
  end handle IO.Io _ => ()

  fun lmfile() =
      if not no_lastmakercheck andalso
         FileSys.access (".HOLMK/lastmaker", [FileSys.A_READ])
      then let
          val _ = diag (K "Found a lastmaker file to look at.")
          val istrm = openIn ".HOLMK/lastmaker"
        in
          case inputLine istrm of
            NONE => (warn "Empty Last Maker file";
                     closeIn istrm;
                     write_lastmaker_file())
          | SOME s => let
              open Substring
              val path = string (dropr Char.isSpace (full s))
              val _ = closeIn istrm
            in
              if FileSys.access (path, [FileSys.A_READ, FileSys.A_EXEC])
              then
                if mypath = path then ()
                else
                  (warn ("*** Switching to execute "^path);
                   warn ("*** (Honouring last Holmake call in this directory)");
                   warn ("*** (Use --nolmbc flag to stop this.)");
                   Systeml.exec(path,
                                path::"--nolmbc"::CommandLine.arguments()))
              else (warn "Garbage in Last Maker file";
                    write_lastmaker_file())
            end
        end
      else write_lastmaker_file()
in
  diag (K "Looking to see if I am in a HOL distribution.");
  case check_distrib "Holmake" of
    NONE => let
    in
      diag (K "Not in a HOL distribution");
      lmfile()
    end
  | SOME p =>
    if p = mypath then diag (K "In the right HOL distribution")
    else if no_lastmakercheck then
      diag (K "In the wrong distribution, but --nolmbc takes precedence.")
    else
      (warn ("*** Switching to execute "^p);
       warn ("*** (As we are in/under its HOLDIR)");
       Systeml.exec (p, p::"--nolmbc"::CommandLine.arguments()))
end

fun chatty_remove act (ofns : output_functions) s =
    act s handle e =>
                 (#warn ofns ("Attempt to remove: " ^ s ^
                              " failed with exception " ^ General.exnMessage e);
                  raise e)

local
(* these next two are used just for recursive removal of directories;
   appropriate to use "real" OS.FileSys *)
structure FileSys = OS.FileSys
in
fun dir_files ofns dnm A =
    let
      val ds = FileSys.openDir dnm
      fun recurse A =
          case FileSys.readDir ds of
              NONE => (FileSys.closeDir ds; A)
            | SOME nm => recurse (OS.Path.concat (dnm, nm) :: A)
    in
      recurse A
    end handle OS.SysErr _ =>
               (#warn ofns ("Failed to list contents of directory "^dnm);
                A)

fun recursive_act ofns file_act dir_act name =
    let
      fun worklist nms rmds =
          case nms of
              [] => List.app dir_act rmds
            | n::ns =>
              if FileSys.isLink n then
                (file_act n ; worklist ns rmds)
              else if FileSys.isDir n then
                worklist (dir_files ofns n ns) (n :: rmds)
              else (file_act n ; worklist ns rmds)
    in
      worklist [name] []
    end
fun clean1 (ofns : output_functions) s =
    let val _ = #diag ofns "tools"
                      (fn () => "clean1 " ^ s ^
                                " [In: " ^ OS.FileSys.getDir() ^ "]")
    in
      if OS.FileSys.access (s, []) then
        if OS.FileSys.isDir s then
          if String.isSuffix "/" s then
            recursive_act ofns
                          (chatty_remove OS.FileSys.remove ofns)
                          (chatty_remove OS.FileSys.rmDir ofns)
                          s
          else
            (#warn ofns ("Not removing directory " ^ s ^ " from EXTRA_CLEANS.");
             #warn ofns ("  Use trailing / on name to force this."))
        else chatty_remove FileSys.remove ofns s
      else (* doesn't exist, do nothing *) ()
    end
end (* local *)

fun quiet_remove s = FileSys.remove s handle e => ()
fun clean_dir ofns {extra_cleans} = let
  fun to_delete f =
      case (toFile f) of
        UO _ => true
      | UI _ => true
      | SIG (Theory _) => true
      | SML (Theory _) => true
      | SML (Script s) =>
          (case OS.Path.ext s of SOME "art" => true | _ => false)
      | DAT _ => true
      | ART _ => true
      | _ => false
in
  read_files_with_objs
    {dirname = "."} to_delete (chatty_remove OS.FileSys.remove ofns);
  HFS_NameMunge.clean_last();
  app (clean1 ofns) extra_cleans
end

fun clean_forReloc {holheap} =
  if Systeml.ML_SYSNAME = "poly" then
    case holheap of SOME s => quiet_remove s | _ => ()
  else ()

fun clean_depdir {depdirname} = let
in
  read_files {dirname = depdirname}
             (fn _ => true)
             (fn s => FileSys.remove (fullPath [depdirname, s]));
  FileSys.rmDir depdirname;
  true
end handle OS.SysErr (mesg, _) => let
           in
             print ("make cleanDeps failed with message: "^mesg^"\n");
             false
           end
         | FileSys.DirNotFound => true

val nice_dir =
    case OS.Process.getEnv "HOME" of
        SOME h => (fn s => if String.isPrefix h s then
                             "~" ^ String.extract(s,size h,NONE)
                           else s)
      | NONE => (fn s => s)

fun pushdir d f x =
    let
      val d0 = FileSys.getDir()
      val res = Exception.capture (fn () => (FileSys.chDir d; f x)) ()
    in
      FileSys.chDir d0; Exception.release res
    end


fun xterm_log s =
  ignore (OS.Process.system ("/bin/sh -c 'printf \"\\033]0;" ^ s ^ "\\007\"'"))

structure hmdir =
struct

type t = {absdir : string, relpath : string option}

fun op+ (d, e) = Path.mkCanonical (Path.concat(d, e))

fun curdir () = {relpath = SOME (OS.Path.currentArc),
                 absdir = FileSys.getDir()}
fun chdir ({absdir,...}: t) = FileSys.chDir absdir

fun compare ({absdir = d1, ...} : t, {absdir = d2, ...} : t) =
    String.compare (d1, d2)

fun eqdir d1 d2 = compare(d1,d2) = EQUAL

fun toString {relpath,absdir} =
    case relpath of
        NONE => absdir
      | SOME p => p

fun toAbsPath {relpath,absdir} = absdir

fun getParent {relpath,absdir} =
    {relpath = Option.map OS.Path.getParent relpath,
     absdir = OS.Path.getParent absdir}

fun pretty_dir d =
  let
    val abs = toAbsPath d
    val abs' = holpathdb.reverse_lookup {path=abs}
  in
    if abs = abs' then toString d else abs'
  end

fun fromPath {origin,path} =
    if Path.isAbsolute path then
      {relpath = NONE, absdir = Path.mkCanonical path}
    else
      {relpath = SOME path, absdir = origin + path}

fun extendp {base = {relpath, absdir}, extension} = let
  val relpath_str = case relpath of NONE => "NONE"
                                  | SOME s => "SOME("^s^")"
in
  if Path.isAbsolute extension then
    {relpath = NONE, absdir = Path.mkCanonical extension}
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

type include_info = {includes : string list, preincludes : string list}
val empty_incinfo = {includes = [], preincludes = []}
type dirset = hmdir.t Binaryset.set

val empty_dirset = Binaryset.empty hmdir.compare
type incset_pair = {pres : dirset, incs : dirset}
type incdirmap = (hmdir.t,incset_pair) Binarymap.dict
val empty_incdirmap = Binarymap.mkDict hmdir.compare

type holmake_dirinfo = {
  visited : hmdir.t Binaryset.set,
  incdirmap : incdirmap
}
type holmake_result = holmake_dirinfo option

fun find_files ds P =
  let
    fun recurse acc =
      case readDir ds of
          NONE => (closeDir ds; List.rev acc)
        | SOME fname => if P fname then recurse (fname::acc)
                        else recurse acc
  in
    recurse []
  end

(* targets are also dependencies, so the naming convention is to use variable
   names like deps and tgts both *)
structure hm_target =
struct
type t = (hmdir.t * File * string option)
fun mk(d,f) = (d,f,NONE)
fun dirpart (d:t) = #1 d
fun filepart (d:t) = #2 d
fun HMF_text (t:t) = #3 t
fun setFile f (d,_,sopt) = (d,f,sopt)
fun setHMF_text s (d,f,_) = (d,f,SOME s)
fun toString (d,f,_) = OS.Path.concat (hmdir.toAbsPath d, fromFile f)
val compare = inv_img_cmp (fn (d,f,_) => (d,f))
                          (pair_compare (hmdir.compare, file_compare))
val empty_tgtset : t Binaryset.set = Binaryset.empty compare
fun tgtset_diff dl1 dl2 =
    let
      fun recurse [] = []
        | recurse (d::ds) =
          (if List.exists (fn d' => compare(d,d') = EQUAL) dl2 then []
           else [d]) @ recurse ds
    in
      recurse dl1
    end
fun localFile f = (hmdir.curdir(), f, NONE)
fun filestr_to_tgt s =
    let
      val {dir,file} = OS.Path.splitDirFile s
      val dir' = hmdir.extendp {base = hmdir.curdir(), extension = dir}
    in
      (dir',toFile file,NONE)
    end
fun tgtexists_readable d = exists_readable (toString d)
end (* struct *)

type dep = hm_target.t
val tgt_toString = hm_target.toString

(* dependency analysis *)
exception HolDepFailed
fun runholdep {ofs, extras, includes, arg, destination} = let
  val {chatty, diag, warn, ...} : output_functions = ofs
  val diagK = diag "holdep" o K
  val _ = chatty ("Analysing "^fromFile arg)
  fun buildables tgt  = let
    val d = hm_target.dirpart tgt val f = hm_target.filepart tgt
    val files =
        case f of
          SML (ss as Script t) => [UI ss, UO ss, SML (Theory t), DAT t,
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
  val _ = diagK ("Running Holdep on "^fromFile arg^" with includes = [" ^
                 String.concatWith ", " includes ^ "], assumes = [" ^
                 String.concatWith ", " buildable_extras ^"]")
  val holdep_result =
    Holdep.main {assumes = buildable_extras, diag = diag "holdep",
                 includes = includes, fname = fromFile arg}
    handle Holdep.Holdep_Error s =>
             (warn ("Holdep failed: "^s); raise HolDepFailed)
         | e => (warn ("Holdep exception: "^General.exnMessage e);
                 raise HolDepFailed)
  fun myopen s =
    if FileSys.access(DEPDIR, []) then
      if FileSys.isDir DEPDIR then openOut s
      else die_with ("Want to put dependency information in directory "^
                     DEPDIR^", but it already exists as a file")
    else
     (chatty ("Trying to create directory "^DEPDIR^" for dependency files");
      FileSys.mkDir DEPDIR;
      openOut s
     )
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

(* a function that given a product file, figures out the argument that
   should be passed to runholdep in order to get back secondary
   dependencies. *)

fun holdep_arg (UO c) = SOME (SML c)
  | holdep_arg (UI c) = SOME (SIG c)
  | holdep_arg (SML (Theory s)) = SOME (SML (Script s))
  | holdep_arg (SIG (Theory s)) = SOME (SML (Script s))
  | holdep_arg (DAT s) = SOME (SML (Script s))
  | holdep_arg (ART (RawArticle s)) = SOME (SML (Script s))
  | holdep_arg (ART (ProcessedArticle s)) = SOME (ART (RawArticle s))
  | holdep_arg _ = NONE

fun mk_depfile_name DEPDIR s = fullPath [DEPDIR, s^".d"]


fun get_dependencies_from_file depfile = let
  open hm_target
  fun get_whole_file s = let
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
      map filestr_to_tgt (realspace_delimited_fields rhs)
    end
  in
    List.concat (map process_line lines)
  end
in
  parse_result (get_whole_file depfile)
end




infix forces_update_of
fun (f1 forces_update_of f2) = let
  open Time
in
  access(f1, []) andalso
  (not (access(f2, [])) orelse HOLFileSys.modTime f1 > HOLFileSys.modTime f2)
end
infix depforces_update_of
fun (d1 depforces_update_of d2) =
    tgt_toString d1 forces_update_of tgt_toString d2


fun get_direct_dependencies {incinfo,DEPDIR,output_functions,extra_targets} f =
let
  open hm_target
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
        UO (Theory s) => localFile (UI (Theory s)) :: localFile(DAT s) :: phase1
      | UO x =>
        if access(fromFile (SIG x), []) andalso
           List.all (fn f => f <> localFile (SIG x)) phase1
        then
          localFile (UI x) :: phase1
        else
          phase1
      | _ => phase1
  end
  else
    []
end

type 'a set = 'a Binaryset.set
val empty_strset = Binaryset.empty String.compare
fun set_member s m = Binaryset.member(s,m)
fun set_diff s1 s2 = Binaryset.difference(s1,s2)
fun set_union s1 s2 = Binaryset.union(s1,s2)
fun set_add i s = Binaryset.add(s,i)
fun set_addList l s = Binaryset.addList(s,l)
fun set_exists P s = isSome (Binaryset.find P s)
fun set_mapPartial f emp s =
    Binaryset.foldl (fn (e,A) => case f e of SOME e' => set_add e' A
                                           | NONE => A)
                    emp
                    s
val listItems = Binaryset.listItems

fun set_concatWith p d set =
    let val str = Binaryset.foldl (fn (e, A) => p e ^ d :: A) [] set
                                  |> String.concat
    in
      case str of
          "" => ""
        | _ => String.extract(str, 0, SOME (size str - size d))
    end
fun concatWithf p d [] = ""
  | concatWithf p d [x] = p x
  | concatWithf p d xs =
    let
      fun recur A [] = List.rev A (* shouldn't ever happen *)
        | recur A [x] = List.rev (p x :: A)
        | recur A (x::xs) = recur (d :: p x :: A) xs
    in
      String.concat (recur [] xs)
    end


fun generate_all_plausible_targets warn first_target =
    case first_target of
        SOME d => [d]
      | NONE =>
        let
          open hm_target
          val cds = openDir "."
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
          val initially = map (localFile o src_to_target o toFile) src_files
        in
          listItems (set_addList initially empty_tgtset)
        end

fun front_last xs =
    let fun recur A [] = raise Empty
          | recur A [x] = (List.rev A, x)
          | recur A (x::xs) = recur (x::A) xs
    in
      recur [] xs
    end

fun front xs = #1 (front_last xs)


end (* struct *)
