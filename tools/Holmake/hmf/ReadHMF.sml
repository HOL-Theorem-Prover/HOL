structure ReadHMF :> ReadHMF =
struct

open Holmake_types Holmake_tools

datatype cond_position = GrabbingText | NoTrueCondYet | SkippingElses
val empty_condstate = [] : cond_position list

infix |>
fun x |> f = f x

fun readline lnum strm = let
  fun recurse (lnum, acc) latest =
      case latest of
        NONE => if null acc then NONE
              else SOME (lnum + 1, String.concat (List.rev acc))
      | SOME "\n" => SOME (lnum + 1, String.concat (List.rev acc))
      | SOME s => let
          val s0 = if String.sub(s, size s - 2) = #"\r" then
                     String.extract(s, 0, SOME (size s - 2))
                   else String.extract(s, 0, SOME (size s - 1))
        in
          if s0 = "" then SOME(lnum + 1, String.concat (List.rev acc))
          else if String.sub(s0, size s0 - 1) = #"\\" then
            recurse (lnum + 1,
                     " " :: String.extract(s0, 0, SOME (size s0 - 1)) :: acc)
                    (TextIO.inputLine strm)
          else
            SOME (lnum + 1, String.concat (List.rev (s0 :: acc)))
        end
in
  recurse (lnum, []) (TextIO.inputLine strm)
end

(* Lexical helpers shared between flatten and the parser. *)

fun strip_leading_wspace s = let
  open Substring
  val ss = full s
in
  string (dropl (fn c => c = #" " orelse c = #"\r") ss)
end

fun drop_twspace s = let
  open Substring
  val ss = full s
in
  string (dropr Char.isSpace ss)
end


fun first_special s = let
  fun recurse i =
      if i = size s then NONE
      else
        case String.sub(s,i) of
            #"=" => SOME "="
          | #":" => SOME ":"
          | #"+" => if i + 1 < size s andalso String.sub(s,i+1) = #"=" then
                      SOME "+="
                    else recurse (i + 1)
          | _ => recurse (i + 1)
in
  recurse 0
end

fun strip_trailing_comment s = let
  fun recurse i =
      if i >= size s then s
      else if String.sub(s,i) = #"\\" then recurse (i + 2)
      else if String.sub(s,i) = #"#" then String.substring(s,0,i)
      else recurse (i + 1)
in
  recurse 0
end

val ss = Substring.full

(* ------------------------------------------------------------------
   Include resolution: lexical pre-expansion.

   `flatten' reads a Holmakefile (and any files it `include's),
   returning a single flat list of origin-tagged lines that the rest
   of the parser then consumes verbatim.  This avoids carrying any
   stream-state across the three Holmakefile-read paths
   (`find_includes0', `extend_path_with_includes0', `get_hmf0') --
   each gets a fresh purely-functional flatten of the same input,
   and there is no `parents'-stack to drift between them.

   Supported directives:
     include FILES         -- mandatory; errors if any file missing
     -include FILES        -- optional; silently skips missing files
     sinclude FILES        -- synonym for -include (GNU make compat)
   Each FILES is a whitespace-separated list with $(VAR)s expanded
   against the env built up by earlier DEFN lines.  Paths are
   resolved relative to the including file's directory (GNU make
   behaviour), not to whatever cwd Holmake was invoked from.  A
   cycle (A includes B includes A) is detected and errors with the
   offending canonical path.  Conditional balance is checked per
   file: `ifdef X' opened in an included file must close in the
   same file (matches GNU make).
   ------------------------------------------------------------------ *)

type origin_line = { file : string, line : int, text : string }

(* substitute_text: expand $(...) in a string against env.  loc is
   used only for error reports from the substitution machinery. *)
fun substitute_text loc env s =
    perform_substitution_at loc env
      (extract_normal_quotation (Substring.full s))

(* `-include' and `sinclude' are GNU-make synonyms for the
   missing-file-tolerant form. *)
val include_keywords =
    [("include", true), ("-include", false), ("sinclude", false)]

fun parse_include s =
    let
      fun afterKw kw =
          if String.isPrefix kw s then
            let val rest = String.extract(s, size kw, NONE)
            in if rest = "" orelse Char.isSpace (String.sub(rest, 0))
               then SOME (strip_leading_wspace rest)
               else NONE
            end
          else NONE
      fun scan [] = NONE
        | scan ((kw, mand) :: rest) =
          (case afterKw kw of
               SOME r => SOME (mand, r)
             | NONE => scan rest)
    in
      scan include_keywords
    end

(* `else' doesn't change the conditional depth -- it toggles within
   an already-open conditional. *)
fun cond_delta s =
    if String.isPrefix "endif" s then ~1
    else if String.isPrefix "ifdef" s orelse String.isPrefix "ifndef" s orelse
            String.isPrefix "ifeq"  s orelse String.isPrefix "ifneq"  s
    then 1
    else 0

(* Recognise DEFN lines so subsequent `include' directives can use
   `$(VAR)' against the env-built-up-so-far.  Conditional state is
   deliberately ignored: a spurious extra binding can only mis-route
   a later `include' path under a key the parser-built env wouldn't
   have had, never the other way round. *)
fun maybe_extend_env env s =
    case first_special s of
        SOME "=" =>
        (case to_token env (DEFN (strip_trailing_comment s)) of
             HM_defn {vname, rhs, ...} => env_extend (vname, rhs) env
           | _ => env)
      | SOME "+=" =>
        (case to_token env (DEFN_EXTEND (strip_trailing_comment s)) of
             HM_defn {vname, rhs, ...} => env_extend (vname, rhs) env
           | _ => env)
      | _ => env

(* Drains istrm via `readline' (the backslash-continuation-aware one
   defined at top of file), not raw `TextIO.inputLine'. *)
fun read_all_lines istrm =
    let
      fun recur lnum acc =
          case readline lnum istrm of
              NONE => List.rev acc
            | SOME (n, s) => recur n ((lnum, s) :: acc)
    in
      recur 1 []
    end

(* `seen' is the canonical-path set of files on the current include
   stack, threaded through to detect cycles. *)
fun flatten {env, fname, seen} =
    let
      val abspath = OS.Path.mkAbsolute
                      {path=fname, relativeTo=OS.FileSys.getDir()}
      val canpath = OS.Path.mkCanonical abspath
      val _ = if Binaryset.member(seen, canpath) then
                raise Fail ("ReadHMF: include cycle re-entering `" ^
                            canpath ^ "'")
              else ()
      val seen' = Binaryset.add(seen, canpath)
      val containing_dir = OS.Path.dir abspath
      val istrm = TextIO.openIn abspath
                  handle _ => raise Fail ("ReadHMF: can't open `" ^
                                          abspath ^ "'")
      val rawlines = read_all_lines istrm
                     handle e => (TextIO.closeIn istrm; raise e)
      val () = TextIO.closeIn istrm
      fun mkline n t = {file = abspath, line = n, text = t}
      fun process_inc env n acc mandatory rest_text =
          let
            val loc = SOME {file = abspath, line = n}
            val expanded = substitute_text loc env rest_text
            val paths = String.tokens Char.isSpace expanded
            val _ = if null paths then
                      raise Fail (abspath ^ ":" ^ Int.toString n ^
                                  ": `include' with no filenames")
                    else ()
            fun one (path, (env, acc)) =
                let
                  val incpath = OS.Path.mkAbsolute
                                  {path=path, relativeTo=containing_dir}
                in
                  if OS.FileSys.access (incpath, [OS.FileSys.A_READ]) then
                    let
                      val (env', sub) =
                          flatten {env=env, fname=incpath, seen=seen'}
                    in
                      (env', List.revAppend(sub, acc))
                    end
                  else if mandatory then
                    raise Fail (abspath ^ ":" ^ Int.toString n ^
                                ": can't open include file `" ^
                                path ^ "'")
                  else (env, acc)
                end
          in
            List.foldl one (env, acc) paths
          end
      fun walk env depth [] acc =
            if depth = 0 then (env, List.rev acc)
            else raise Fail (abspath ^
                             ": unterminated conditional (depth " ^
                             Int.toString depth ^ " at EOF)")
        | walk env depth ((n, raw) :: rest) acc =
            let
              val s = strip_leading_wspace raw
            in
              if s = "" orelse String.sub(s,0) = #"#" then
                walk env depth rest (mkline n raw :: acc)
              else
                case parse_include s of
                    SOME (mandatory, rest_text) =>
                      let
                        val rest_text = strip_trailing_comment rest_text
                                        |> drop_twspace
                        val (env', acc') =
                            process_inc env n acc mandatory rest_text
                      in
                        walk env' depth rest acc'
                      end
                  | NONE =>
                      let
                        val depth' = depth + cond_delta s
                        val _ = if depth' < 0 then
                                  raise Fail (abspath ^ ":" ^
                                              Int.toString n ^
                                              ": unpaired `endif'")
                                else ()
                        val env' = maybe_extend_env env s
                      in
                        walk env' depth' rest (mkline n raw :: acc)
                      end
            end
    in
      walk env 0 rawlines []
    end

(* ------------------------------------------------------------------
   Buf: a thin cursor over a flatten result.  Carries the topname
   (the originally-opened Holmakefile, for context in error
   messages that don't have a specific line) and the current
   remainder of the flattened lines.  Advance is purely functional
   -- it returns a new buf with the tail.  `close_buf' is a no-op
   because flatten closes its TextIO streams as it goes.
   ------------------------------------------------------------------ *)

datatype buf = B of { lines : origin_line list,
                      topname : string }

fun init_buf env fname =
    let
      val abspath = OS.Path.mkAbsolute
                      {path=fname, relativeTo=OS.FileSys.getDir()}
      val (_, lines) = flatten {env=env, fname=abspath,
                                seen=Binaryset.empty String.compare}
    in
      B { lines = lines, topname = abspath }
    end

fun close_buf _ = ()

fun currentline (B {lines=[], ...}) = NONE
  | currentline (B {lines=x::_, ...}) = SOME (#text x)

fun advance (B {lines=[], topname}) = B {lines=[], topname=topname}
  | advance (B {lines=_::rest, topname}) =
      B {lines=rest, topname=topname}

fun current_origin (B {lines=[], topname}) =
      {file=topname, line=0}
  | current_origin (B {lines=x::_, ...}) =
      {file = #file x, line = #line x}

fun error b s =
    let val {file, line} = current_origin b in
      raise Fail (file ^ ":" ^ Int.toString line ^ ": " ^ s)
    end

fun bufloc b : internal_functions.loc option =
    SOME (current_origin b)

fun substitute b env q = perform_substitution_at (bufloc b) env q

fun read_delimited_string b dchar s = let
  (* assume s begins with dchar *)
  val s' = String.extract(s,1,NONE)
  open Substring
  val (result, rest) = position (str dchar) (ss s')
  val _ = size rest <> 0 orelse error b ("No matching "^str dchar)
in
  (string result, string rest
                         |> (fn s => String.extract(s, 1, NONE))
                         |> strip_leading_wspace)
end

fun read_quoted_string b s = let
  val c = String.sub(s, 0)
in
  case c of
    #"'" => read_delimited_string b c s
  | #"\"" => read_delimited_string b c s
  | _ => error b ("Bad argument delimiter: "^str c)
end

fun split_at_rightmost_rparen ss = let
  open Substring
  fun recurse i =
      if i < 0 then (ss, full "")
      else if sub(ss,i) = #")" then (slice(ss,0,SOME i), slice(ss,i,NONE))
      else recurse (i - 1)
in
  recurse (size ss - 1)
end

fun evaluate_cond b env s =
    if String.isPrefix "ifdef" s orelse String.isPrefix "ifndef" s then let
        val (sense, sz, nm) =
            if String.sub(s,2) = #"n" then (false, 6, "ifndef")
            else (true, 5, "ifdef")
        val s' = strip_leading_wspace (String.extract(s, sz, NONE))
        val q = extract_normal_quotation (Substring.full s')
        val s2 = substitute b env q
      in
        case String.tokens Char.isSpace s2 of
          [s] => (case lookup env s of
                    [LIT ""] => SOME (not sense)
                  | [] => SOME (not sense)
                  | _ => SOME sense)
        | _ => error b ("ReadHMF: "^nm^" not followed by a variable name.")
      end
    else if String.isPrefix "ifeq" s orelse String.isPrefix "ifneq" s then let
        val (sense, sz, nm) =
            if String.sub(s,2) = #"n" then (false, 5, "ifneq")
            else (true, 4, "ifeq")
        val s = String.extract(s,sz,NONE) |> strip_leading_wspace |> drop_twspace
        val (arg1, arg2) =
            case String.sub(s,0) of
              #"(" => let
                open Substring
                val (arg1s, blob2s) = position "," (full (String.extract(s,1,NONE)))
                val _ = size blob2s <> 0 orelse
                        error b (nm ^ " with parens requires args separated by \
                                        \commas")
                val (arg2s, parenblob) =
                    split_at_rightmost_rparen (slice(blob2s,1,NONE))
                val _ = size parenblob <> 0 orelse
                        error b ("No right-paren in "^nm^" line")
              in
                (arg1s |> string |> drop_twspace |> strip_leading_wspace,
                 arg2s |> string |> drop_twspace |> strip_leading_wspace)
              end
            | _ => let
                val (arg1, s) = read_quoted_string b s
                val (arg2, s) = read_quoted_string b s
                val _ = size (drop_twspace s) = 0 orelse
                        error b ("Extraneous junk after complete "^nm^" directive")
              in
                (arg1, arg2)
              end
        val (q1, q2) = (extract_normal_quotation (ss arg1),
                        extract_normal_quotation (ss arg2))
        val (s1, s2) = (substitute b env q1, substitute b env q2)
      in
        SOME ((s1 = s2) = sense)
      end
    else NONE

fun getline env (condstate, b) =
    case (currentline b, condstate) of
      (NONE, []) => (b, NONE, condstate)
    | (NONE, _ :: _) => error b "ReadHMF: unterminated conditional"
    | (SOME s, SkippingElses :: rest) => let
        val s = strip_leading_wspace s
      in
        if String.isPrefix "endif" s then getline env (rest, advance b)
        else if String.isPrefix "ifdef" s orelse String.isPrefix "ifndef" s orelse
                String.isPrefix "ifeq" s orelse String.isPrefix "ifneq" s
        then
          getline env (SkippingElses::condstate, advance b)
        else
          getline env (condstate, advance b)
      end
    | (SOME s, NoTrueCondYet::rest) => let
        val s = strip_leading_wspace s
      in
        if String.isPrefix "endif" s then getline env (rest, advance b)
        else if String.isPrefix "if" s then
          getline env (SkippingElses :: condstate, advance b)
        else if String.isPrefix "else" s then let
            val s = strip_leading_wspace (String.extract(s, 4, NONE))
          in
            if String.isPrefix "if" s then
              case evaluate_cond b env s of
                NONE => error b "ReadHMF: bogus string following else"
              | SOME false => getline env (condstate, advance b)
              | SOME true => getline env (GrabbingText::rest, advance b)
            else if s = "" then getline env (GrabbingText::rest, advance b)
            else error b "ReadHMF: bogus string following else"
          end
        else getline env (condstate, advance b)
      end
    | (SOME s0, _) => let
        val s = strip_leading_wspace s0
      in
        if String.isPrefix "endif" s then
          if null condstate then error b "ReadHMF: unpaired endif"
          else getline env (tl condstate, advance b)
        else if String.isPrefix "else" s then
          if null condstate then error b "ReadHMF: unpaired else"
          else getline env (SkippingElses::tl condstate, advance b)
        else if String.isPrefix "if" s then
          case evaluate_cond b env s of
            NONE => (b, SOME s0, condstate)
          | SOME false => getline env (NoTrueCondYet::condstate, advance b)
          | SOME true => getline env (GrabbingText::condstate, advance b)
        else (b, SOME s0, condstate)
      end

fun read_commands env (cs,b) head =
    case getline env (cs, b) of
      (b, NONE, cs) => ((cs, b), RULE head)
    | (b, SOME s, cs) => let
        val s' = strip_leading_wspace s
      in
        if s' = "" orelse String.sub(s',0) = #"#" then
          read_commands env (cs, advance b) head
        else
          case String.sub(s',0) of
            #"\t" => read_commands env (cs, advance b) (head ^ s' ^ "\n")
          | c => ((cs, b), RULE head)
      end


fun process_line env (condstate, b) = let
  val (b, line_opt, condstate) = getline env (condstate, b)
in
  case line_opt of
    NONE => ((condstate, b), EOF)
  | SOME s => let
      val s' = strip_leading_wspace s
    in
      if s' = "" orelse String.sub(s',0) = #"#" then
        process_line env (condstate, advance b)
      else let
          val c1 = String.sub(s',0)
        in
          if c1 = #"\t" then error b "TAB starts an unattached command"
          else
            case first_special s' of
                NONE =>
                  if c1 = #"$" then
                    (* bare top-level function call (e.g. $(info ...));
                       expand for its side effects and discard the result.
                       Anything non-blank after expansion is a typo. *)
                    let
                      val txt = strip_trailing_comment s'
                      val q = extract_normal_quotation (Substring.full txt)
                      val result = substitute b env q
                    in
                      if CharVector.all Char.isSpace result then
                        process_line env (condstate, advance b)
                      else
                        error b ("Top-level expression has non-empty \
                                 \expansion: \"" ^ result ^ "\"")
                    end
                  else error b ("Unrecognised character: \""^
                                String.toString (str c1) ^ "\"")
              | SOME "=" => ((condstate, advance b),
                              DEFN (strip_trailing_comment s))
              | SOME "+=" => ((condstate, advance b),
                              DEFN_EXTEND (strip_trailing_comment s))
              | SOME ":" => read_commands
                                 env
                                 (condstate, advance b)
                                 (strip_trailing_comment s' ^ "\n")
              | SOME _ => error b "ReadHMF: can't happen"
        end
    end
end

fun readall diags fname
            (acc as (tgt1,env,ruledb,depdb,patrules,defs_seen)) csb =
    let
      val {warn=warn0,die=die0,info=info0} = diags
      fun aug f s = f ("*** " ^ fname ^ ": " ^ s)
      val warn = aug warn0 and die = aug die0 and info = aug info0
      fun recurse (acc as (tgt1,env,ruledb,depdb,patrules,defs_seen)) csb =
          case process_line env csb of
              (csb as (cs, b), EOF) =>
              let
                val _ = close_buf b
                fun foldthis (tgt,deps,acc) =
                    case Binarymap.peek(acc,tgt) of
                        NONE =>
                        Binarymap.insert(acc,tgt,
                                         {dependencies = deps, commands = []})
                   | SOME {dependencies, commands} =>
                     Binarymap.insert(acc,tgt,
                                      {dependencies = dependencies @ deps,
                                       commands = commands})
              in
                (env,Binarymap.foldl foldthis ruledb depdb,patrules,tgt1)
              end
            | (csb, x) =>
              (case to_token env x of
                   HM_defn {vname, extendp, rhs} =>
                   (if Binaryset.member(defs_seen, vname) andalso
                       not (extendp)
                    then
                      if vname = "INCLUDES" then
                        die "Can't redefine INCLUDES variable"
                      else
                        warn ("Repeated definition of variable " ^ vname ^
                              " (use += instead?)")
                    else ();
                    recurse (tgt1,env_extend (vname,rhs) env, ruledb, depdb,
                             patrules, Binaryset.add(defs_seen, vname)) csb)
                 | HM_rule rinfo =>
                   let
                     val (rdb',depdb',patrules',tgts) =
                         extend_ruledb warn env rinfo
                                       (ruledb,depdb,patrules)
                     val tgt1' =
                         case tgt1 of
                             NONE => List.find (fn s => s <> ".PHONY") tgts
                           | _ => tgt1
                   in
                     recurse (tgt1',env,rdb',depdb',patrules',defs_seen) csb
                   end)
    in
      recurse acc csb
    end

fun diagread diags fname env =
    readall diags fname (NONE, env, empty_ruledb,
                         Binarymap.mkDict String.compare,
                         empty_patrules,
                         Binaryset.empty String.compare)
            (empty_condstate, init_buf env fname)

fun dflt_warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
val read =
    diagread {warn = dflt_warn,
              die = fn s => (dflt_warn s ; OS.Process.exit OS.Process.failure),
              info = fn s => (TextIO.print (s ^ "\n"))}

fun readlist e vref =
  map dequote (tokenize (perform_substitution e [VREF vref]))


fun find_includes0 dirname =
  let
    fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
    val hm_fname = OS.Path.concat(dirname, "Holmakefile")
  in
    if OS.FileSys.access(hm_fname, [OS.FileSys.A_READ]) then
      let
        val (e, _, _, _) = read hm_fname (base_environment())
        val raw_incs = readlist e "INCLUDES" @ readlist e "PRE_INCLUDES"
      in
        map (fn p => OS.Path.mkAbsolute {path = p, relativeTo = dirname})
            raw_incs
      end handle e => (warn ("Bogus Holmakefile in " ^ dirname ^
                             " - ignoring it"); [])
    else []
  end

fun normPath p =
    OS.Path.mkCanonical
      (OS.Path.mkAbsolute{path = p, relativeTo = OS.FileSys.getDir()})
val find_includes = memoise String.compare find_includes0 o normPath

infix ++
val op ++ = OS.Path.concat
fun canonicalise d1 d2 = OS.Path.mkAbsolute{path = d2, relativeTo = d1}
fun fromList l = Binaryset.addList (Binaryset.empty String.compare, l)

(* returns updated accumulator and list of new places to visit *)
fun extend_path_with_includes0 (A as (visited,prem,postm)) dir verbosity =
    if Binaryset.member(visited, dir) then (A,[])
    else
      if OS.FileSys.access (dir ++ "Holmakefile", [OS.FileSys.A_READ]) then
        let
          open Holmake_types
          val _ = if verbosity > 1 then
                    print ("Visiting " ^ dir ^ " for first time\n")
                  else ()
          val extensions =
              holpathdb.search_for_extensions find_includes
                {starter_dirs = [dir], skip = Binaryset.empty String.compare}
          val _ = List.app holpathdb.extend_db extensions
          val _ = if verbosity > 1 then
                    print ("Completed holpathdb analysis in " ^ dir ^ "\n")
                  else ()
          val base_env = let
            fun foldthis ({vname,path}, env) =
                env_extend (vname, [LIT path]) env
          in
            List.foldl foldthis (base_environment()) extensions
          end
          val (env, _, _, _) = read (dir ++ "Holmakefile") base_env
          fun envlist id =
              map dequote (tokenize (perform_substitution env [VREF id]))
          fun diag nm incs =
              if null incs orelse verbosity < 2 then ()
              else
                print (nm ^ " = " ^ String.concatWith ", " incs ^ "\n")
          val pre_incs = map (canonicalise dir) (envlist "PRE_INCLUDES")
          val _ = diag "PRE_INCLUDES" pre_incs
          val post_incs = map (canonicalise dir) (envlist "INCLUDES")
          val _ = diag "INCLUDES" post_incs
          fun maybeinsert(m,k,v) =
              if null v then m else Binarymap.insert(m,k,v)
        in
          ((Binaryset.add(visited,dir),
            maybeinsert(prem,dir,pre_incs),
            maybeinsert(postm,dir,post_incs)),
           Binaryset.listItems (fromList (pre_incs @ post_incs)))
        end handle e => (if verbosity > 0 then
                           (TextIO.output(TextIO.stdErr,
                                          "[bogus Holmakefile in " ^ dir ^
                                          " - ignoring it]\n");
                            TextIO.flushOut TextIO.stdErr;
                            (A, [])
                           )
                         else (A, []))
      else (A, [])

fun extend_paths A cfg worklist =
    case worklist of
        [] => A
      | d::ds =>
        let
          val (A',new) = extend_path_with_includes0 A d cfg
        in
          extend_paths A' cfg (ds @ new)
        end


val empty_strset = Binaryset.empty String.compare
val empty_strmap = Binarymap.mkDict String.compare
fun extend_path_with_includes (cfg as {lpref,verbosity=v}) =
    let
      val wlist = [OS.FileSys.getDir()]
      val (_, prem, postm) =
          extend_paths (empty_strset, empty_strmap, empty_strmap) v wlist
      fun m s = holpathdb.reverse_lookup {path = s}
      fun foldthis nm (dirname,incs,acc) = (
        if v > 1 then
          print (m dirname ^ "/Holmakefile:" ^ nm ^ " +=\n  " ^
                 String.concatWith "\n  " (map m incs) ^ "\n")
        else ();
        Binaryset.addList(acc,incs)
      )
      fun acc_range nm = Binarymap.foldl (foldthis nm) empty_strset
      val all_preincs = Binaryset.listItems (acc_range "PRE_INCLUDES" prem)
      val all_incs = Binaryset.listItems (acc_range "INCLUDES" postm)
    in
      lpref := all_preincs @ !lpref @ all_incs
    end

end (* struct *)
