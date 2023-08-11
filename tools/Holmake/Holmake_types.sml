structure Holmake_types :> Holmake_types =
struct

open internal_functions HOLFileSys

datatype pretoken =
         DEFN of string | DEFN_EXTEND of string | RULE of string | EOF

datatype frag = LIT of string | VREF of string
type quotation = frag list
type env = (string, quotation)Binarymap.dict
fun env_keys e = Binarymap.foldr (fn (k,v,A) => k::A) [] e
fun env_fold f e A = Binarymap.foldl (fn (k,v,A) => f k v A) A e

type rule_info = {dependencies : string list, commands : string list}
type raw_rule_info = { targets : quotation, dependencies : quotation,
                       commands : quotation list }
type ruledb =
     (string, {dependencies: string list, commands: quotation list}) Binarymap.dict
datatype token = HM_defn of {vname : string, rhs : quotation, extendp : bool}
               | HM_rule of raw_rule_info

fun normquote acc [] = List.rev acc
  | normquote acc [x] = List.rev (x::acc)
  | normquote acc (LIT s1 :: LIT s2 :: t) = normquote acc (LIT (s1 ^ s2) :: t)
  | normquote acc (h :: t) = normquote (h::acc) t

(* for strings that are not commands *)
fun is_special c = c = #"#" orelse c = #"$" orelse c = #"\\"

fun ok_symbolvars c = c = #"<" orelse c = #"@"

fun check_for_vref (startc, endc) acc ss k = let
  open Substring
  (* scan forward for balancing endc *)
  fun recurse (count, depth, ss) =
      case getc ss of
        NONE => raise Fail ("Unclosed variable reference, beginning: $"^
                            str startc ^
                            string (slice(ss, 0, SOME(Int.min(size ss, 10)))))
      | SOME(c, ss') => if c = endc then
                          if depth = 0 then (count, slice(ss, 1, NONE))
                          else recurse (count + 1, depth - 1, ss')
                        else if c = startc then
                          recurse (count + 1, depth + 1, ss')
                        else recurse (count + 1, depth, ss')
  val (varlength, rest) = recurse(0, 0, ss)
in
  k (VREF (string (slice(ss, 0, SOME varlength))) :: acc) rest
end

fun quotable c =
    case c of
      #" " => true
    | #"\\" => true
    | #":" => true
    | #"#" => true
    | _ => false

fun extract_quotation0 cmd acc ss = let
  open Substring
  val (normal, rest) = splitl (not o is_special) ss
  val acc = if size normal > 0 then LIT (string normal) :: acc
            else acc
  val extract = extract_quotation0 cmd
in
  case Substring.getc rest of
    NONE => List.rev acc
  | SOME(c, rest) => let
      fun chew_newline acc rest = let
        val rest = dropl Char.isSpace rest
      in
        if size rest = 0 then List.rev acc
        else extract (LIT " " :: acc) rest
      end
    in
      case c of
        #"#" => if not cmd then
                  (* rest of line is comment; drop it *) List.rev acc
                else extract (LIT "#" :: acc) rest
      | #"\\" =>
        if cmd then
          if size rest > 0 andalso sub(rest,0) = #"\n" andalso
             not Systeml.isUnix
          then
            chew_newline acc rest
          else extract (LIT "\\" :: acc) rest
        else let
          (* need to look at what comes next *)
          in
            case Substring.getc rest of
              NONE => List.rev (LIT "\\" :: acc)
            | SOME (c, rest') => let
              in
                case c of
                  #"\n" => chew_newline acc rest
                | #"#" => extract (LIT "#" :: acc) rest'
                | _ => extract (LIT ("\\" ^ str c) :: acc) rest'
              end
          end
      | #"$" => (* check for well-formed variable *) let
        in
          case Substring.getc rest of
            NONE => (* gnu make silently drops it ; weird *) List.rev acc
          | SOME (c, rest) => let
            in
              case c of
                #"$" => (* becomes a dollar-sign *)
                extract (LIT "$" :: acc) rest
              | #"(" => check_for_vref (c, #")") acc rest extract
              | #"{" => check_for_vref (c, #"}") acc rest extract
              | _ =>
                if Char.isAlphaNum c orelse c = #"_" orelse
                   ok_symbolvars c
                then
                  extract (VREF (str c) :: acc) rest
                else
                  raise Fail ("Bad variable name: "^str c)
            end
        end
      | _ => raise Fail "Can't happen"
    end
end


val extract_normal_quotation = normquote [] o extract_quotation0 false []
val extract_cmd_quotation = normquote [] o extract_quotation0 true []


fun mem e [] = false
  | mem e (h::t) = e = h orelse mem e t

fun strip_trailing_ws ss = let
  (* can't just use dropr Char.isSpace, because the first space
     might be protected with a backslash *)
  open Substring
  val (ok, spaces) = splitr Char.isSpace ss
  val (ok0, bslashes) = splitr (fn c => c = #"\\") ok
in
  if size bslashes mod 2 = 0 then ok
  else if size spaces > 0 then
    slice(ss, 0, SOME (size ok + 1))
  else ok
end

fun convert_newlines ss0 = let
  (* replace \r\n with \n to normalise against windows convention *)
  open Substring
  fun recurse acc ss0 = let
    val (ss1, ss2) = position "\r\n" ss0
  in
    if size ss2 = 0 then concat (List.rev (ss1::acc))
    else recurse (ss1::acc) (Substring.slice(ss2, 1, NONE))
  end
in
  Substring.full (recurse [] ss0)
end

fun to_token env pt =
    case pt of
      DEFN s => let
        open Substring
        val ss = convert_newlines (full s)
        fun endp c = c <> #"=" andalso not (Char.isSpace c)
        val (varname, rest) = splitl endp ss
        val rest = dropl Char.isSpace rest
        val rest = #2 (valOf (getc rest)) (* drops = sign *)
        val rest = dropl Char.isSpace rest
      in
        HM_defn{vname = string varname, rhs = extract_normal_quotation rest,
                extendp = false}
      end
    | DEFN_EXTEND s => let
        open Substring
        val ss = convert_newlines (full s)
        fun endp c = c <> #"+" andalso not (Char.isSpace c)
        val (varname, rest) = splitl endp ss
        val rest = dropl Char.isSpace rest
        val rest = triml 2 rest (* drop += *)
        val rest = dropl Char.isSpace rest
        val key = string varname
        val old = case Binarymap.peek(env,key) of NONE => []
                                                | SOME s => s @ [LIT " "]
     in
       HM_defn{vname = key, rhs = old @ extract_normal_quotation rest,
               extendp = true}
     end
    | RULE s => let
        open Substring
        val ss = convert_newlines (full s)
        val idx = valOf (find_unescaped [#":"] ss)
        val (tgts, rest) = splitAt(ss, idx)
        val tgts = strip_trailing_ws tgts

        val rest = #2 (valOf (getc rest)) (* drop the colon *)
        val (deps, rest) =
            splitAt(rest, valOf (find_unescaped [#"\n"] rest))
            handle Option => (* happens if the dependencies are terminated
                                by an eof character *)
                   splitAt(rest, size rest - 1)
        val rest = #2 (valOf (getc rest)) (* drop the newline/eof *)
        val deps =  (* cut any comment on this line *)
            case find_unescaped [#"#"] deps of
              NONE => deps
            | SOME i => #1 (splitAt(deps, i))
        val deps = dropl Char.isSpace (strip_trailing_ws deps)

        fun docmds acc ss =
            if size ss = 0 then List.rev acc
            else
              case find_unescaped [#"\n"] ss of
                NONE => (* cut out initial TAB, and final EOF character *)
                List.rev (extract_cmd_quotation
                            (slice(ss,1,SOME(size ss - 2))) :: acc)
              | SOME i => let
                  val (cmd, rest) = splitAt(ss, i)
                  val rest = slice(rest, 1, NONE) (* drop newline *)
                  val cmd = slice(cmd, 1, NONE)  (* drop TAB *)
                in
                  docmds (extract_cmd_quotation cmd :: acc) rest
                end
      in
        HM_rule {commands = docmds [] rest,
                 dependencies = extract_normal_quotation deps,
                 targets = extract_normal_quotation tgts}
      end
    | EOF => raise Fail "No EOF-equivalent"

val commafy = String.concatWith ", "

fun argtokenize ss = let
  open Substring
  val sz = size ss
  fun recurse pdepth start i acc =
      if i = sz then
        if pdepth = 0 then List.rev (slice(ss,start,NONE) :: acc)
        else raise Fail "argtokenize: too few right parens"
      else let
          val c = sub(ss,i)
        in
          if c = #"(" then recurse (pdepth + 1) start (i + 1) acc
          else if c = #")" then
            if pdepth = 0 then raise Fail "argtokenize: too many right parens"
            else recurse (pdepth - 1) start (i + 1) acc
          else if c = #"," then
            if pdepth = 0 then recurse pdepth (i + 1) (i + 1)
                                       (slice(ss,start,SOME (i-start)) :: acc)
            else recurse pdepth start (i + 1) acc
          else
            recurse pdepth start (i + 1) acc
        end
in
  recurse 0 0 0 []
end

fun perform_substitution env q = let
  open Substring
  fun envfn s =
      case Binarymap.peek(env, s) of
        NONE => (case OS.Process.getEnv s of
                   NONE => [LIT ""]
                 | SOME s => [LIT s])
      | SOME q => q
  fun finisher q =
      case normquote [] q of
        [LIT s] => s
      | [] => ""
      | _ => raise Fail "Can't happen"
  fun recurse visited fraglist =
      case fraglist of
        [] => []
      | (LIT s :: rest) => LIT s :: recurse visited rest
      | VREF s :: rest => let
          val ss = full s
          val (fnpart, spc_rest) = position " " ss
          val eval = finisher o recurse visited o extract_normal_quotation
          val result =
              if size spc_rest > 0 then let
                  (* have a function call to evaluate *)
                  val fnname = eval fnpart
                  val args = argtokenize
                                 (dropl Char.isSpace
                                        (dropr Char.isSpace spc_rest))
                in
                  [LIT (function_call (fnname, args, eval))]
                end
              else let
                  val varname = eval ss
                  val _ = not (mem varname visited) orelse
                          raise Fail ("Variable loop through: "^
                                      commafy visited)
                  val s_expanded0 = envfn varname
                in
                  recurse (s :: visited) s_expanded0
                end
        in
          result @ recurse visited rest
        end
in
  finisher (recurse [] q)
end

fun dequote s = let
  open Substring
  val ss = full s
  fun recurse acc ss = let
    val (normal, rest) = splitl (fn c => c <> #"\\") ss
    val acc = string normal :: acc
  in
    case getc rest of
      NONE => String.concat (List.rev acc)
    | SOME (_, rest) => let
      in
        case getc rest of
          NONE => String.concat (List.rev ("\\" :: acc))
        | SOME (c, rest) =>
          if quotable c then recurse (str c :: acc) rest
          else recurse (str c :: "\\" :: acc) rest
      end
  end
in
  recurse [] ss
end

fun is_pseudo_target s = s = ".PHONY"

val empty_ruledb = Binarymap.mkDict String.compare
type depdb = (string,string list) Binarymap.dict

fun app_insert (ddb, s, slist) =
    case Binarymap.peek(ddb, s) of
      NONE => Binarymap.insert(ddb, s, slist)
    | SOME existing => Binarymap.insert(ddb, s, existing @ slist)

fun extend_ruledb warn env {targets,dependencies,commands} (rdb,ddb) = let
  val tgts = map dequote (tokenize (perform_substitution env targets))
  val deps = map dequote (tokenize (perform_substitution env dependencies))
in
  if null commands then
    (rdb,
     List.foldl (fn (tgt, ddb) => app_insert(ddb, tgt, deps)) ddb tgts, tgts)
  else let
      val info = {dependencies = deps, commands = commands}
      fun foldthis (t, dict) =
          case Binarymap.peek(dict, t) of
            NONE => Binarymap.insert(dict, t, info)
          | SOME _ => let
            in
              warn ("Later rule for `"^t^
                    "' takes precedence over earlier one.");
              Binarymap.insert(dict, t, info)
            end
    in
      (List.foldl foldthis rdb tgts, ddb, tgts)
    end
end

fun ins (k,v) env = Binarymap.insert(env,k,v)
infix |>
fun x |> f = f x

fun get_rule_info rdb env tgt =
    case Binarymap.peek(rdb, tgt) of
      NONE => NONE
    | SOME {dependencies, commands} => let
        val dep1 = [LIT (hd dependencies)] handle Empty => [LIT ""]
        val env = env |> ins("<", dep1) |> ins("@", [LIT tgt])
      in
        SOME {dependencies = dependencies,
              commands = map (perform_substitution env) commands}
      end


val base_environment0 = let
  open Systeml
  infix ++
  fun p1 ++ p2 = OS.Path.concat(p1,p2)
  val alist =
      [("CC", [LIT CC]),
       ("CP", if OS = "winNT" then [LIT "copy /b"] else [LIT Systeml.CP]),
       ("DEFAULT_TARGETS",
        [VREF ("patsubst %.sml,%.uo,$(patsubst %Theory.sml,,"^
               "$(patsubst %Script.sml,%Theory.uo,$(wildcard *.sml)))")]),
       ("HOLDIR", [LIT HOLDIR]),
       ("HOL_LNSIGOBJ",
        [LIT "for i in `pwd`/",
         VREF "HOLOBJDIR", LIT "/*.uo `pwd`/",
         VREF "HOLOBJDIR",
         LIT "/*.ui ; do b=`basename $i` ; \
             \if [ \"$b\" = \"selftest.uo\" -o \"$b\" = \"selftest.ui\" ] ; \
             \then : ; else ln -fs $i ",
         VREF "SIGOBJ",
         LIT " ; fi ; done && for i in *.sig ; do ln -fs `pwd`/$i ",
         VREF "SIGOBJ",
         LIT " ; echo `pwd`/`basename $i .sig` >> ",
         VREF "SIGOBJ",
         LIT "/SRCFILES ; done"]),
       ("HOLOBJDIR", [LIT HFS_NameMunge.HOLOBJDIR]),
       ("MLLEX", [VREF "protect $(HOLDIR)/tools/mllex/mllex.exe"]),
       ("MLYACC", [VREF "protect $(HOLDIR)/tools/mlyacc/src/mlyacc.exe"]),
       ("ML_SYSNAME", [LIT ML_SYSNAME]),
       ("MV", if OS = "winNT" then [LIT "move", LIT "/y"]
              else [LIT Systeml.MV]),
       ("OS", [LIT OS]),
       ("SIGOBJ", [VREF "HOLDIR", LIT "/sigobj"]),
       ("UNQUOTE", [VREF ("protect $(HOLDIR)/" ^ xable_string "/bin/unquote")])] @
      (if Systeml.ML_SYSNAME = "poly" then
         [("POLY", [LIT (Systeml.protect Systeml.POLY)]),
          ("POLYC", [LIT (Systeml.protect Systeml.POLYC)]),
          ("POLY_VERSION", [LIT (Int.toString Systeml.POLY_VERSION)]),
          ("POLYMLLIBDIR", [LIT (Systeml.protect Systeml.POLYMLLIBDIR)])]
       else [])
in
  List.foldl (fn ((k,v), a) => Binarymap.insert(a, k, v))
             (Binarymap.mkDict String.compare)
             alist
end

fun base_environment () = let
  val kernelid =
      let
        val strm = openIn Holmake_tools.kernelid_fname
        val s =
            case inputLine strm of
                NONE => ""
              | SOME s => hd (String.tokens Char.isSpace s) handle Empty => ""

      in
        s before closeIn strm
      end handle IO.Io _ => ""
in
  Binarymap.insert(base_environment0, "KERNELID", [LIT kernelid])
end

fun lookup e k =
    case Binarymap.peek(e, k) of
      NONE => (case OS.Process.getEnv k of
                   NONE => [LIT ""]
                 | SOME s => [LIT s])
    | SOME q => normquote [] q


fun env_extend (k, v) e = Binarymap.insert(e,k,v)

end (* struct *)
