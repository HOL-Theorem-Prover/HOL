local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate7 z
in
fun updateT z = let
  fun from chattiness config_opt files_wmatches help ignore_project pinned
           tests =
    {
      chattiness = chattiness, config_opt = config_opt,
      files_wmatches = files_wmatches, help = help,
      ignore_project = ignore_project, pinned = pinned, tests = tests
    }
  fun from' tests pinned ignore_project help files_wmatches config_opt
            chattiness =
    {
      chattiness = chattiness, config_opt = config_opt,
      files_wmatches = files_wmatches, help = help,
      ignore_project = ignore_project, pinned = pinned, tests = tests
    }
  fun to f {chattiness, config_opt, files_wmatches, help, ignore_project,
            pinned, tests} =
    f chattiness config_opt files_wmatches help ignore_project pinned tests
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* local *)


fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
fun die s = (warn s; OS.Process.exit OS.Process.failure)
fun succeed s = (print (s^"\n"); OS.Process.exit OS.Process.success)

type checkfn = bool -> string -> int -> (string * Substring.substring) -> bool

(* A check that looks at a directory rather than at a line: run once
   per directory visited, returning SOME (subject, detail) when that
   directory is in violation.  The check names its own subject file so
   that the runner stays generic. *)
type dircheckfn = string -> (string * string) option

datatype check = LineCheck of checkfn
               | DirCheck of dircheckfn

(* `pinned` names the checks whose setting was fixed on the command
   line.  Per-directory settings out of a project file may silence or
   reconfigure any check they like, except one the user has already
   spoken about explicitly here. *)
type t = {
  chattiness : int,
  config_opt : h4pedantConfig.config option,
  files_wmatches : bool,
  help : bool,
  ignore_project : bool,
  pinned : string list,
  tests : (string * (check * string)) list
};


(* acceptable Unicode characters are

                  UTF-8
    ‘   U+2018   0xE28098
    ’   U+2019   0xE28099
    “   U+201C   0xE2809C
    ”   U+201D   0xE2809D
    λ   U+03BB     0xCEBB
*)

fun includes_unicode s =
  let
    val sz = size s
    fun recurse i =
      if i = sz then false
      else
        let val c = ord (String.sub(s,i))
        in
          if c = 0xE2 then quote_char2 (i + 1)
          else if c = 0xCE then maybelambda (i + 1)
          else if c > 127 then true
          else recurse (i + 1)
        end
    and quote_char2 i =
        if i = sz then true
        else if ord (String.sub(s,i)) = 0x80 then quote_char3 (i + 1)
        else true
    and quote_char3 i =
        if i = sz then true
        else
          let val c = ord (String.sub(s,i))
          in
            if c = 0x98 orelse c = 0x99 orelse c = 0x9C orelse c = 0x9D then
              recurse (i + 1)
            else true
          end
    and maybelambda i =
        if i = sz then false
        else
          let val c = ord (String.sub(s,i))
          in
            if c = 0xBB then recurse (i + 1)
            else true
          end
  in
    recurse 0
  end

fun line_error qp fname linenum tag line =
  if qp then false
  else
    (print (fname^":"^Int.toString linenum^": " ^ tag ^ ": " ^ line);
     false)


fun check_unicode qp fname linenum (line,ss) =
  let
    val (p,s) = Substring.position "UOK" ss
  in
    if Substring.size s <> 0 then true
    else
      if includes_unicode line then
        line_error qp fname linenum "Unicode violation" line
      else true
  end

fun check_tabs qp fname linenum (line,ss) =
  let
    open Holmake_tools
    val (p,s) = Substring.position "\t" ss
    val highlightTAB =
        String.translate (fn c => if c = #"\t" then boldred "\\t" else str c)
  in
    if Substring.size s = 0 then true
    else
      line_error qp fname linenum "Includes TAB" (highlightTAB line)
  end

(* mk_check_length n - a check function that flags lines whose
   visible length exceeds `n` characters.  The `+1` accounts for the
   trailing newline that `TextIO.inputLine` includes. *)
fun mk_check_length limit qp fname linenum (line,ss) =
  let
    val sz = UTF8.size line
  in
    if sz > limit + 1 then
      line_error qp fname linenum
                 ("Line-length > " ^ Int.toString limit) line
    else true
  end

fun check_twspace qp fname linenum (line,ss) =
  let
    val sz = String.size line
    val pos = if String.sub(line,sz - 1) = #"\n" then sz - 2 else sz - 1
  in
    if pos >= 0 andalso Char.isSpace (String.sub(line, pos)) then
      line_error qp fname linenum "Trailing whitespace" line
    else true
  end

(* Holmake takes the first explicit non-.PHONY target of a Holmakefile
   as that directory's default goal, and ReadHMF hands it back as the
   fourth component of a parse.  A rule written above `all` therefore
   demotes it silently: a bare `Holmake` here -- and every parent that
   reaches this directory under `CLINE_OPTIONS = -r`, which is how
   src/parallel_builds/core reaches most of src/ -- then builds that
   one rule's target instead of `all`.  Nothing fails; the directory
   just builds less than it owes, and what gets dropped is whatever no
   other directory depends on, typically the selftest.  Ask ReadHMF
   for the goal it computed rather than re-deriving it, so that .PHONY
   filtering, pattern rules, variable expansion and conditionals are
   decided by the parser that actually decides them. *)
fun default_goal_violation dname =
  let
    val hmf = OS.Path.concat(dname, "Holmakefile")
    fun unparseable msg =
        (* Forcing the conditionals open below can reach branches a
           real build never takes, so failing to parse here is not
           evidence of a style problem.  Say so on stderr -- stdout is
           the violation stream -- and let the directory pass. *)
        (warn (hmf ^ ": skipped default-goal check: " ^ msg); NONE)
  in
    if not (OS.FileSys.access(hmf, [OS.FileSys.A_READ])) then NONE
    else
      let
        (* `all` and the rules that can precede it both routinely sit
           inside these conditionals, and a build does set them, so
           force them open -- the same device, for the same reason, as
           buildutils' hmakefile_data. *)
        fun ext (k,v) e =
            Holmake_types.env_extend (k, [Holmake_types.LIT v]) e
        val env = ext ("HOLBUILD", "1")
                      (ext ("HOLSELFTESTLEVEL", "3")
                           (Holmake_types.base_environment()))
        val quiet : internal_functions.diags =
            {info = fn _ => (), warn = fn _ => (),
             die = fn s => raise internal_functions.HolmakeError s}
        (* $(DEFAULT_TARGETS) is a lazy $(wildcard *.sml) over the
           process cwd, so the parse has to happen inside `dname`;
           pushdir restores the cwd even when the parse raises. *)
        val (_, rdb, _, tgt1) =
            Holmake_tools.pushdir dname
              (fn () => ReadHMF.diagread quiet "Holmakefile" env) ()
      in
        case (Binarymap.peek(rdb, "all"), tgt1) of
            (SOME _, SOME t) =>
              if t = "all" then NONE else SOME (hmf, t)
          | _ => NONE
      end
      handle Fail msg => unparseable msg
           | internal_functions.HolmakeError msg => unparseable msg
           | OS.SysErr (msg, _) => unparseable msg
  end

fun inc k m =
  case Binarymap.peek(m,k) of
      NONE => Binarymap.insert(m,k,1)
    | SOME i => Binarymap.insert(m,k,i+1)

fun checkfile (opts as {chattiness,files_wmatches,...}:t) sofar fname =
  let
    val istrm = TextIO.openIn fname
    val linechecks =
        List.mapPartial (fn (_, (LineCheck f, tag)) => SOME (f, tag)
                          | _ => NONE)
                        (#tests opts)
    fun recurse linenum tags sofar =
      case TextIO.inputLine istrm of
          NONE =>
          let
            fun tagfold (k,v,acc) = (k ^ "(" ^ Int.toString v ^ ")") :: acc
            val tagdump = Binarymap.foldr tagfold [] tags
          in
            TextIO.closeIn istrm;
            if files_wmatches andalso not (null tagdump) then
              print (fname ^ ": " ^ String.concatWith ", " tagdump ^ "\n")
            else ();
            sofar
          end
        | SOME line =>
          let
            val ss = Substring.full line
            val qp = (chattiness = 0) orelse files_wmatches
            fun foldthis ((f, tag), (b, tags)) =
              let
                val b' = f qp fname linenum (line,ss)
              in
                (b andalso b', if not b' then inc tag tags else tags)
              end
            val (c, tags) = List.foldl foldthis (true, tags) linechecks
          in
            if not c andalso chattiness = 0 then
              (TextIO.closeIn istrm; false)
            else
              recurse (linenum + 1) tags (c andalso sofar)
          end
  in
    recurse 1 (Binarymap.mkDict String.compare) sofar
  end

fun is_generated opts fname =
  let
    open String
    val {base,ext} = OS.Path.splitBaseExt fname
    fun suff s = isSuffix s base
    fun suffs sl = List.exists suff sl
  in
    case ext of
        SOME "uo" => true
      | SOME "ui" => true
      | SOME "sig" => suffs ["Theory", "ML"]
      | SOME "sml" => suffs [".lex", ".grm", ".grm-sig", "Theory", "ML"]
      | _ => false
  end


(* Every check this tool knows, in the order checks run over a line.
   Command-line flags and per-directory settings prune and replace
   entries of this list; `all_tests` stays the authority on what a
   name means and where it belongs. *)
val all_tests : (string * (check * string)) list =
    [("unicode", (LineCheck check_unicode, "Unicode present")),
     ("tabs", (LineCheck check_tabs, "TAB present")),
     ("linelength",
      (LineCheck (mk_check_length (#linelen h4pedantConfig.builtin_default)),
       "Line too long")),
     ("trailing_wspace", (LineCheck check_twspace, "Trailing whitespace")),
     ("default_goal",
      (DirCheck default_goal_violation, "Default goal not all"))]

fun remove_test s sl =
  case sl of
      [] => []
    | (s',f) :: rest => if s' = s then rest else (s',f) :: remove_test s rest

fun has_test s sl = List.exists (fn (s',_) => s' = s) sl

(* Position of a check in `all_tests`; unknown names sort last. *)
fun test_index s =
  let
    fun recurse i sl =
      case sl of
          [] => i
        | (s',_) :: rest => if s' = s then i else recurse (i + 1) rest
  in
    recurse 0 all_tests
  end

(* Install `entry`, replacing a same-named entry if there is one and
   otherwise splicing it in at its `all_tests` position, so that a
   check configured or re-enabled on the command line still runs where
   it usually runs. *)
fun upsert_test (entry as (s, _)) sl =
  if has_test s sl then
    List.map (fn e as (s',_) => if s' = s then entry else e) sl
  else
    let
      val i = test_index s
      fun ins sl =
        case sl of
            [] => [entry]
          | e :: rest => if test_index (#1 e) > i then entry :: e :: rest
                         else e :: ins rest
    in
      ins sl
    end

(* Turn a check on without disturbing any configuration it already
   carries (a `--linelen` limit, say). *)
fun enable_test s sl =
  if has_test s sl then sl
  else
    case List.find (fn (s',_) => s' = s) all_tests of
        NONE => sl
      | SOME entry => upsert_test entry sl

(* set_linelen n - the line-length check at limit `n`; `n <= 0` means
   the check is off, matching `linelen`'s project-file reading. *)
fun set_linelen n sl =
  if n <= 0 then remove_test "linelength" sl
  else
    upsert_test ("linelength",
                 (LineCheck (mk_check_length n), "Line too long")) sl

(* Per-directory effective tests.  CLI flags have already set the
   global tests list up; per-dir settings may further prune (Unicode
   silenced, line-length disabled) or substitute (a different
   line-length limit).  What they may not touch is a check named in
   `pinned`: a flag the user wrote on the command line is their last
   word on that check, in every directory visited. *)
fun derive_tests pinned opts_tests (pd : h4pedantConfig.per_dir) =
    let
      fun pinned_p s = List.exists (fn s' => s' = s) pinned
      val ts =
          if #unicode_ok pd andalso not (pinned_p "unicode") then
            remove_test "unicode" opts_tests
          else opts_tests
      val ts =
          if #default_goal_ok pd andalso not (pinned_p "default_goal") then
            remove_test "default_goal" ts
          else ts
    in
      if pinned_p "linelength" orelse not (has_test "linelength" ts) then ts
      else set_linelen (#linelen pd) ts
    end

(* Compute the effective per-file opts for files directly under
   `dname`.  Returns `opts` unchanged if no project config is in
   scope. *)
fun opts_for_dir (opts : t) (dname : string) : t =
    case #config_opt opts of
        NONE => opts
      | SOME cfg =>
          let
            val pd = h4pedantConfig.effective_for cfg dname
          in
            updateT opts
                    (U #tests (derive_tests (#pinned opts) (#tests opts) pd))
                    $$
          end

fun is_excluded_path (opts : t) path =
    case #config_opt opts of
        NONE => false
      | SOME cfg => h4pedantConfig.is_excluded cfg path

(* Run the directory-level checks for `dname`.  Reports keep the
   per-file message shape minus the line number, which ReadHMF does
   not report: "<subject>: <tag>: <detail>". *)
fun run_dirchecks (opts as {chattiness,files_wmatches,...}:t) dname sofar =
  let
    fun foldthis ((_, (c, tag)), acc) =
        case c of
            LineCheck _ => acc
          | DirCheck f =>
            (case f dname of
                 NONE => acc
               | SOME (subject, detail) =>
                 (if files_wmatches then
                    print (subject ^ ": " ^ tag ^ "(1)\n")
                  else if chattiness = 0 then ()
                  else print (subject ^ ": " ^ tag ^ ": " ^ detail ^ "\n");
                  false))
  in
    List.foldl foldthis sofar (#tests opts)
  end

fun do_dirstream opts dname ds sofar wlist =
  let
    val opts_here = opts_for_dir opts dname
    val sofar = run_dirchecks opts_here dname sofar
    fun recurse sofar dworklist =
      case OS.FileSys.readDir ds of
          NONE => (OS.FileSys.closeDir ds; (sofar, dworklist))
        | SOME fname =>
          let
            val fullp = OS.Path.concat(dname, fname)
          in
            if OS.FileSys.isLink fullp then recurse sofar dworklist
            else if OS.FileSys.isDir fullp then
              (* .hol is Holmake's own directory: what is under it is
                 built, not written, and its style is nobody's to fix *)
              if fname = ".hol" orelse is_excluded_path opts fullp then
                recurse sofar dworklist
              else recurse sofar (fullp::dworklist)
            else
              let
                val {base,ext} = OS.Path.splitBaseExt fname
              in
                if (ext = SOME "sml" orelse ext = SOME "sig") andalso
                   not (is_generated opts_here fname) andalso
                   fname <> "selftest.sml" andalso
                   fname <> "EmitTeX.sml"
                then
                  recurse (checkfile opts_here sofar fullp) dworklist
                else
                  recurse sofar dworklist
              end
          end
  in
    recurse sofar wlist
  end
and do_dirs (opts:t) sofar wlist =
    case wlist of
        [] => sofar
      | d::res =>
        let
          (* A directory named on the command line that isn't there
             would otherwise surface as a bare exit status, which
             reads exactly like a style violation. *)
          val ds = OS.FileSys.openDir d
                   handle OS.SysErr (msg, _) =>
                          die ("Can't scan " ^ d ^ ": " ^ msg)
          val _ = if #chattiness opts > 1 then warn ("Checking "^d) else ()
          val (sofar, wlist) = do_dirstream opts d ds sofar res
        in
          do_dirs opts sofar wlist
        end

fun fupdbool sel b t = updateT t (U sel b) $$
fun fupdchattiness c t = updateT t (U #chattiness c) $$
fun fupdconfig c t = updateT t (U #config_opt c) $$

val default : t =
    { help = false, chattiness = 1, config_opt = NONE,
      files_wmatches = false, ignore_project = false, pinned = [],
      tests = all_tests
    }

fun fupdtests f t = updateT t (U #tests (f (#tests t))) $$

(* Adjust a check and record that the command line has decided it, so
   that no project-file setting can move it again. *)
fun fupdcheck s f t =
    updateT (fupdtests f t) (U #pinned (s :: #pinned t)) $$

val options = let
  open GetOpt
  fun int_arg flag s =
      case Int.fromString s of
          SOME i => i
        | NONE => die (flag ^ ": expected a number, got `" ^ s ^ "`")
in
  [
    {help = "show this message", long = ["help"], short = "h?",
     desc = NoArg (fn () => fupdbool #help true)},
    {help = "Just print files with problems", long = ["files-with-matches"],
     short = "l", desc = NoArg (fn () => fupdbool #files_wmatches true)},
    {help = "Do Holmakefile default-goal check", long = ["defaultgoal"],
     short = "", desc = NoArg (fn () => fupdcheck "default_goal"
                                                 (enable_test "default_goal"))},
    {help = "Ignore any holproject.toml", long = ["ignore-project-file"],
     short = "", desc = NoArg (fn () => fupdbool #ignore_project true)},
    {help = "Line-length limit (0 to disable the check)",
     long = ["linelen"], short = "",
     desc = ReqArg ((fn s => fupdcheck "linelength"
                                       (set_linelen (int_arg "--linelen" s))),
                    "n")},
    {help = "No Holmakefile default-goal check",
     long = ["nodefaultgoal"], short = "",
     desc = NoArg (fn () => fupdcheck "default_goal"
                                      (remove_test "default_goal"))},
    {help = "No line-length check", long = ["nolinelen"], short = "",
     desc = NoArg (fn () => fupdcheck "linelength"
                                      (remove_test "linelength"))},
    {help = "be less chatty", long = ["quiet"], short = "q",
     desc = NoArg (fn () => fupdchattiness 0)},
    {help = "Flag Unicode", long = ["unicode"], short = "",
     desc = NoArg (fn () => fupdcheck "unicode" (enable_test "unicode"))},
    {help = "allow Unicode", long = ["unicodeok"], short = "u",
     desc = NoArg (fn () => fupdcheck "unicode" (remove_test "unicode"))},
    {help = "be more verbose", long = [], short = "v",
     desc = NoArg (fn () => fupdchattiness 2)}
  ]
end

fun usage_str() =
  GetOpt.usageInfo {
    header =
        "Usage:\n\
        \  " ^ CommandLine.name() ^ " [options] dir1 dir2 .. dirn\n\n\
        \Recursively grep over dirs looking for style violations.",
    options = options
  }

fun read_cline args =
  GetOpt.getOpt { argOrder = GetOpt.Permute,
                  options = options,
                  errFn = warn }
                args



fun main() =
  let
    val (upds, args) = read_cline(CommandLine.arguments())
    val cli_opts = List.foldl (fn (f,a) => f a) default upds
  in
    (* Answer --help before going anywhere near a project file: a
       malformed holproject.toml is no reason to withhold the usage
       message, which is where the reader learns about
       --ignore-project-file. *)
    if #help cli_opts then succeed (usage_str())
    else
    let
      (* --ignore-project-file takes the project file out of the
         picture altogether: no per-directory settings, no include or
         exclude lists, just the directories named here under the
         options named here. *)
      val cfg_opt =
          if #ignore_project cli_opts then NONE
          else (h4pedantConfig.load { start = OS.FileSys.getDir() }
                handle Fail msg => die ("holproject.toml: " ^ msg))
      val opts = updateT cli_opts (U #config_opt cfg_opt) $$
      (* Symlink-resolve scan_dirs so prefix comparison against config
         paths (which are themselves symlink-resolved via the upward
         walk from `OS.FileSys.getDir`) actually matches.  On macOS
         `/var/tmp` and `/private/var/tmp` would otherwise look like
         different subtrees. *)
      fun resolve p = OS.FileSys.fullPath p
                      handle OS.SysErr _ => p
      val scan_dirs =
          List.map resolve
            (case (args, cfg_opt) of
                 (_ :: _, _) => args
               | ([], SOME cfg) =>
                   if null (#includes cfg) then [#root cfg] else #includes cfg
               | ([], NONE) => [OS.FileSys.getDir()])
      val result = do_dirs opts true scan_dirs
    in
      OS.Process.exit
        (if result then OS.Process.success else OS.Process.failure)
    end
  end


(*
#!/bin/bash

if [ $# -eq 1 ]
then
    if [ $1 = "-h" -o $1 = "-?" ]
    then
        echo "Usage:"
        echo "  $0 dir1 dir2 .. dirn"
        echo
        echo "Recursively grep over dirs looking for non-ASCII characters"
        echo "If no directories given, run in HOL's src directory"
        exit 0
    fi
fi

cmd="grep -R -n -v -E '^[[:print:][:space:]]*$|UOK' --include='*.sml' --exclude='*Theory.sml' --exclude='*Theory.sig' --exclude selftest.sml --exclude EmitTeX.sml"

if [ $# -eq 0 ]
then
    LC_ALL=C eval $cmd $(dirname $0)/../src/
else
    LC_ALL=C eval $cmd "$@"
fi
*)
