structure Holmake_types :> Holmake_types =
struct

open internal_functions

datatype pretoken = DEFN of string | RULE of string | EOF

datatype frag = LIT of string | VREF of string
type quotation = frag list
type env = string -> quotation
datatype token = HM_defn of string * quotation
               | HM_rule of { targets : quotation, dependencies : quotation,
                              commands : quotation list }


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
    in
      case c of
        #"#" => if not cmd then
                  (* rest of line is comment; drop it *) List.rev acc
                else extract (LIT "#" :: acc) rest
      | #"\\" =>
        if cmd then extract (LIT "\\" :: acc) rest
        else let
            (* need to look at what comes next *)
          in
            case Substring.getc rest of
              NONE => List.rev (LIT "\\" :: acc)
            | SOME (c, rest) => let
              in
                case c of
                  #"\n" => let
                    (* replace with a space & consume following whitespace,
                       unless consuming the following whitespace leaves
                       nothing left, in which case just drop it all.  This is
                       what GNU make does *)
                    val rest = dropl Char.isSpace rest
                  in
                    if size rest = 0 then List.rev acc
                    else extract (LIT " "::acc) rest
                  end
                  (* some characters can be quoted, others just
                     cause the backslash to be passed through unchanged.
                     GNU make's behaviour here is grossly inconsistent, so
                     I don't feel there's any point in trying to mimic it.
                     At this stage, we have to keep quoting in place
                     anyway, because spaces are being used as separators
                     in lists, and quoted spaces need to be kept in place,
                  *)
                | _ => extract (LIT ("\\"^str c) :: acc) rest
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

fun to_token pt =
    case pt of
      DEFN s => let
        open Substring
        val ss = all s
        fun endp c = c <> #"=" andalso not (Char.isSpace c)
        val (varname, rest) = splitl endp ss
        val rest = dropl Char.isSpace rest
        val rest = #2 (valOf (getc rest)) (* drops = sign *)
        val rest = dropl Char.isSpace rest
      in
        HM_defn(string varname, extract_normal_quotation rest)
      end
    | RULE s => let
        open Substring
        val ss = all s
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

fun commafy0 [] = []
  | commafy0 [x] = [x]
  | commafy0 (h::t) = h :: ", " :: commafy0 t
val commafy = String.concat o commafy0

fun perform_substitution env q = let
  open Substring
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
          val ss = all s
          val (fnpart, spc_rest) = position " " ss
          val result =
              if size spc_rest > 0 then let
                  (* have a function call to evaluate *)
                  val fnname = string fnpart
                  val args =
                      tokens (fn c => c = #",") (dropl Char.isSpace spc_rest)
                  val eval =
                      finisher o recurse visited o extract_normal_quotation
                in
                  [LIT (function_call (fnname, args, eval))]
                end
              else let
                  val _ = not (mem s visited) orelse
                          raise Fail ("Variable loop through: "^
                                      commafy visited)
                  val s_expanded0 = env s
                in
                  recurse (s :: visited) s_expanded0
                end
        in
          result @ recurse visited rest
        end
in
  finisher (recurse [] q)
end

fun extend_env toks e s =
    case toks of
      []  => e s
    | HM_defn(s', q) :: t => if s = s' then q else extend_env t e s
    | _ :: t => extend_env t e s

fun empty_env s = []


fun dequote s = let
  open Substring
  val ss = all s
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

fun mk_rules toks env =
    case toks of
      [] => []
    | (HM_rule {targets, dependencies, commands} :: rest) => let
        val tgts = map dequote (tokenize (perform_substitution env targets))
        val deps =
            map dequote (tokenize (perform_substitution env dependencies))
        fun mk_rule t = let
          fun newenv s = if s = "<" then
                           [LIT (hd deps)] handle Empty => [LIT ""]
                         else if s = "@" then [LIT t]
                         else env s
        in
          { target = t, dependencies = deps,
            commands = map (perform_substitution newenv) commands }
        end
      in
        map mk_rule tgts @ mk_rules rest env
      end
    | _ :: rest => mk_rules rest env

end (* struct *)
