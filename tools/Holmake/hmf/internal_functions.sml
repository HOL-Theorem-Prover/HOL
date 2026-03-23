structure internal_functions :> internal_functions =
struct

structure FileSys = HOLFileSys
fun member e [] = false
  | member e (h::t) = e = h orelse member e t

fun equal x y = x = y

fun spacify0 acc [] = List.rev acc
  | spacify0 acc [x] = List.rev (x::acc)
  | spacify0 acc (h::t) = spacify0 (" "::h::acc) t

val spacify = String.concat o spacify0 []

fun dropWhile P [] = []
  | dropWhile P (l as (h::t)) = if P h then dropWhile P t else l

fun find_unescaped cset ss = let
  open Substring
  val sz = size ss
  fun recurse i =
    if i >= sz then NONE
    else
      let val c = Substring.sub(ss,i)
      in
        if member c cset then SOME i
        else if c = #"\\" then recurse (i + 2)
        else recurse (i + 1)
      end
in
  recurse 0
end

fun tokenize s = let
  (* could be a call to tokens, but for escaped spaces getting in the way *)
  open Substring
  val ss = dropl Char.isSpace (full s)
  fun recurse acc ss =
      (* assumes first character of ss is not isSpace, or size ss = 0  *)
      if size ss = 0 then List.rev acc
      else
        case find_unescaped [#" ", #"\t"] ss of
          NONE => List.rev (string ss::acc)
        | SOME i => let
            val (t1, rest) = splitAt(ss, i)
          in
            recurse (string t1::acc) (dropl Char.isSpace rest)
          end
in
  recurse [] ss
end

fun subst(from,to,on) = let
  open Substring
  val (from,to,on) = (full from, full to, full on)
  val _ = size from > 0 orelse
          raise Fail "empty from argument to `subst' function"
  fun recurse acc ss = let
    val (ok, rest) = position (string from) ss
  in
    if size rest > 0 then
      recurse (to::ok::acc) (slice(rest, size from, NONE))
    else concat (List.rev (ok::acc))
  end
in
  recurse [] on
end


fun find_percent ss = let
  open Substring
  fun recurse acc ss =
      case getc ss of
        NONE => (full (String.implode (List.rev acc)), full "")
      | SOME(c, ss') => let
        in
          case c of
            #"\\" => let
            in
              case getc ss' of
                NONE => (full (String.implode (List.rev (c::acc))), full "")
              | SOME(c',ss'') =>
                if c' = #"%" orelse c' = #"\\" then
                  recurse (c'::acc) ss''
                else
                  recurse (c'::c::acc) ss''
            end
          | _ => if c = #"%" then (full (String.implode(List.rev acc)), ss)
                 else recurse (c::acc) ss'
        end
in
  recurse [] ss
end

fun pattern_match pattern object = let
  open Substring
  fun translate_pattern patss = let
    val (pfx, rest) = find_percent patss
    val sfx = if size rest > 0 then let
                  val (sfx, rest') = find_percent (slice(rest, 1, NONE))
                in
                  if size rest' > 0 then
                    raise Fail "Multiple % chars in pattern"
                  else
                    SOME sfx
                end
              else NONE
  in
    (pfx, sfx)
  end
  fun fromright (patss, i) (objss, j) =
      if j = ~1 then NONE
      else if i = ~1 then SOME (slice(objss, 0, SOME (j + 1)))
      else let
          val pc = sub(patss, i)
          val oc = sub(objss, j)
        in
          if pc = oc then fromright(patss, i - 1) (objss, j - 1)
          else NONE
        end

  val (patpfx, patsfx) = translate_pattern (full pattern)
  val objss = full object
in
  if isPrefix (string patpfx) objss then let
      val objrest = slice(objss, size patpfx, NONE)
    in
      case patsfx of
        NONE => if size objrest = 0 then SOME "" else NONE
      | SOME sfx => Option.map string
                               (fromright (sfx, size sfx - 1)
                                          (objrest, size objrest - 1))
    end
  else NONE
end

fun pcsubst (residue, pattern) = let
  open Substring
  val patss = full pattern
  val resss = full residue
  fun recurse acc ss =
      case find_unescaped [#"%"] ss of
        NONE => concat (List.rev (ss::acc))
      | SOME i => let
          val (pfx, sfx) = splitAt(ss, i)
        in
          recurse (resss::pfx::acc) (slice(sfx, 1, NONE))
        end
in
  recurse [] (full pattern)
end

fun patsubst (from,to,arglist) = let
  fun mapthis s =
      case pattern_match from s of
        NONE => s
      | SOME stem => pcsubst(stem,to)
in
  spacify (map mapthis (tokenize arglist))
end

fun split_to_directories (comps : parse_glob.t list) = let
  open parse_glob
  fun recurse h acc [] = List.rev (List.rev h::acc)
    | recurse h acc (RE r :: rest) = recurse (RE r::h) acc rest
    | recurse h acc (CHAR #"/" :: rest) = recurse [] (List.rev h::acc) rest
    | recurse h acc (CHAR c :: rest) = recurse (CHAR c :: h) acc rest
in
  recurse [] [] comps
end

fun dirfiles dirname = let
  val dirstrm = FileSys.openDir dirname
  fun recurse acc =
      case FileSys.readDir dirstrm of
          NONE => "." :: ".." :: acc
        | SOME fname => recurse (fname :: acc)
in
  recurse [] before FileSys.closeDir dirstrm
end

fun safeIsDir s =
    FileSys.isDir s handle OS.SysErr _ => false

fun diag s = TextIO.output(TextIO.stdErr, s)

fun wildcard0 (dirname,s) =
    if s = "" then [""]
    else let
      open parse_glob
      val comps = parse_glob_components s
      val split_comps = split_to_directories comps
      fun initial_split d l k =
          case l of
              h::t => if null h then
                        initial_split "/" t (fn (d,s,r) => k (d,s ^ "/", r))
                      else k (d,"", l)
            | [] => k (d,"", l)
      val (starting_dir,pfx, rest) =
          initial_split dirname split_comps (fn x => x)
      fun recurse curpfx curdir complist : string list =
          case complist of
              c::cs => (* c must be non-null *)
              let
                val dotfiles_ok = case c of CHAR #"." :: _ => true
                                          | _ => false
                val re = toRegexp c
                val files = Listsort.sort String.compare (dirfiles curdir)
                val m = regexpMatch.match re
                val require_dir = not (null cs)
                val (_, _, cs') = initial_split "" cs (fn x => x)
                val slashes = if require_dir then "/" else ""
                fun check s =
                    m s andalso
                    (dotfiles_ok orelse String.sub(s,0) <> #".") andalso
                    (not require_dir orelse
                     safeIsDir (OS.Path.concat(curdir, s)))
                      handle e => raise Fail (s ^ " - " ^ exnMessage e)
              in
                case List.filter check files of
                    [] => []
                  | fs =>
                    let
                      val newpfxs = map (fn s => curpfx ^ s ^ slashes) fs
                    in
                      if null cs' then newpfxs
                      else let
                        val newdirs = map (fn d => OS.Path.concat(curdir, d)) fs
                        val more_results : string list list =
                            ListPair.map (fn (pfx,dir) => recurse pfx dir cs')
                                         (newpfxs,newdirs)
                      in
                        List.concat more_results
                      end
                    end
              end
            | [] => raise Fail "wildcard.recurse: should never happen"
    in
      case rest of
          [] => (* happens if input was a series of forward slashes *) [s]
        | _ => case recurse pfx starting_dir rest of [] => [] | x => x
    end

local open Holmake_tools
val wildcard_withdir =
    memoise (pair_compare(String.compare, String.compare)) wildcard0
in
fun wildcard s = wildcard_withdir (OS.FileSys.getDir(), s)
end

fun get_first f [] = NONE
  | get_first f (h::t) = (case f h of NONE => get_first f t | x => x)

fun which arg =
  let
    open FileSys Systeml
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

fun shell arg =
  let
    open Unix

    (* TODO This gets rid of all carriage returns; should only replace
       those paired with a newline *)
    fun fix_nls s =
      let
        val s = String.translate (fn c => if c = #"\r" then "" else String.str c) s
        val s = if String.isSuffix "\n" s then
                  String.substring (s, 0, String.size s - 1)
                else s
      in
        String.map (fn c => if c = #"\n" then #" " else c) s
      end

    val proc = execute ("/bin/sh", ["-c", arg])
    val ins = textInstreamOf proc
    val str = fix_nls (TextIO.inputAll ins)
  in
    if OS.Process.isSuccess (reap proc) then str else ""
  end
  handle OS.SysErr _ => ""

(* taken from
     https://unix.stackexchange.com/a/70675/287940
   by user lesmana
*)
fun tee (cmd, fname) =
    "{ { { { " ^ cmd ^ " ; echo $? >&3; } | tee " ^ fname ^ " >&4; } 3>&1; } | \
    \ { read xs; if [ $xs != \"0\" ] ; then /bin/rm -f " ^ fname ^ " ; fi ; exit $xs; } } 4>&1"

fun hol2fs s =
    case HFS_NameMunge.HOLtoFS s of
        NONE => s
      | SOME {fullfile,...} => fullfile

fun function_call (fnname, args, eval) = let
  open Substring
in
  case fnname of
    "if" =>
    if length args <> 2 andalso length args <> 3 then
      raise Fail "Bad number of arguments to `if' function."
    else let
        val condition = dropr Char.isSpace (hd args)
        val condition_evalled = eval condition
      in
        if condition_evalled <> "" then eval (List.nth(args, 1))
        else if length args = 3 then eval (List.nth(args, 2))
        else ""
      end
  | "subst" =>
    if length args <> 3 then
      raise Fail "Bad number of arguments to `subst' function."
    else let
        val args_evalled = map eval args
        val tuple = case args_evalled of
                      [x,y,z] => (x,y,z)
                    | _ => raise Fail "Can't happen"
      in
        subst tuple
      end
  | "patsubst" =>
    if length args <> 3 then
      raise Fail "Bad number of arguments to `patsubst' function."
    else let
        val args_evalled = map eval args
        val tuple = case args_evalled of
                      [x,y,z] => (x,y,z)
                    | _ => raise Fail "Can't happen"
      in
        patsubst tuple
      end
  | "protect" => if length args <> 1 then
                   raise Fail "Bad number of arguments to `protect' function."
                 else
                   Systeml.protect (eval (hd args))
  | "dprot" => if length args <> 1 then
                 raise Fail "Bad number of arguments to 'dprot' function."
               else subst(" ", "\\ ", eval (hd args))
  | "findstring" => if length args <> 2 then
                      raise Fail "Bad number of arguments to 'findstring' \
                                 \function."
                    else let
                        val (findstr, instr) = case map eval args of
                                                 [x,y] => (x,y)
                                               | _ => raise Fail "Can't happen"
                        open Substring
                        val (pfx,sfx) = position findstr (full instr)
                      in
                        if size sfx = 0 then "" else findstr
                      end
  | "which" => if length args <> 1 then
                 raise Fail "Bad number of arguments to 'which' function"
               else let
                 val arg_evalled = eval (hd args)
               in
                 which arg_evalled
               end
  | "wildcard" => if length args <> 1 then
                    raise Fail "Bad number of arguments to 'wildcard' function"
                  else let
                    val args' = tokenize (Substring.string (hd args))
                    val args_evalled = map (eval o Substring.full) args'
                  in
                    spacify (List.concat (map wildcard args_evalled))
                  end
  | "shell" => if length args <> 1 then
                 raise Fail "Bad number of arguments to 'shell' function"
               else let
                 val arg_evalled = eval (hd args)
               in
                  shell arg_evalled
               end
  | "tee" => if length args <> 2 then
               raise Fail "Bad number of arguments to 'tee' function"
             else
               let val args_evalled = map eval args
               in tee (hd args_evalled, hd (tl args_evalled))
               end
  | "hol2fs" => if length args <> 1 then
                  raise Fail "Bad number of arguments to 'hol2fs' function"
                else
                  let val args_evalled = map eval args
                  in
                    hol2fs (hd args_evalled)
                  end
  | _ => raise Fail ("Unknown function name: "^fnname)
end


end (* struct *)
