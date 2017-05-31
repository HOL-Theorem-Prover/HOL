structure ReadHMF :> ReadHMF =
struct

open Holmake_types

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
          if String.sub(s0, size s0 - 1) = #"\\" then
            recurse (lnum + 1,
                     " " :: String.extract(s0, 0, SOME (size s0 - 1)) :: acc)
                    (TextIO.inputLine strm)
          else
            SOME (lnum + 1, String.concat (List.rev (s0 :: acc)))
        end
in
  recurse (lnum, []) (TextIO.inputLine strm)
end

datatype buf = B of { lnum : int,
                      strm : TextIO.instream,
                      name : string,
                      curr : (int * string) option }

fun init_buf fname = let
  val istrm = TextIO.openIn fname
in
  B { lnum = 1, strm = istrm, curr = readline 1 istrm, name = fname }
end

fun close_buf (B r) = TextIO.closeIn (#strm r)

fun currentline (B r) = Option.map #2 (#curr r)

fun advance (b as B r) =
  case #curr r of
    NONE => b
  | SOME (n,s) => B { lnum = n, strm = #strm r, name = #name r,
                      curr = readline n (#strm r) }

fun error (B r) s =
    raise Fail (#name r ^":"^Int.toString (#lnum r)^": "^s)

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
  fun recurse i = if i = size s then NONE
                  else if String.sub(s,i) = #"=" then SOME #"="
                  else if String.sub(s,i) = #":" then SOME #":"
                  else recurse (i + 1)
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
        val s2 = perform_substitution env q
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
        val (s1, s2) = (perform_substitution env q1, perform_substitution env q2)
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
                NONE => error b ("Unrecognised character: \""^
                                 String.toString (str c1) ^ "\"")
              | SOME #"=" => ((condstate, advance b), DEFN (strip_trailing_comment s))
              | SOME #":" => read_commands
                                 env
                                 (condstate, advance b)
                                 (strip_trailing_comment s' ^ "\n")
              | SOME _ => error b "ReadHMF: can't happen"
        end
    end
end

fun readall (acc as (tgt1,env,ruledb,depdb)) csb =
    case process_line env csb of
      (csb as (cs, b), EOF) => let
        val _ = close_buf b
        fun foldthis (tgt,deps,acc) =
            case Binarymap.peek(acc,tgt) of
              NONE => Binarymap.insert(acc,tgt,
                                       {dependencies = deps, commands = []})
            | SOME {dependencies, commands} =>
              Binarymap.insert(acc,tgt, {dependencies = dependencies @ deps,
                                         commands = commands})
      in
        (env,Binarymap.foldl foldthis ruledb depdb,tgt1)
      end
    | (csb, x) => let
        fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
      in
        case to_token x of
          HM_defn def => readall (tgt1,env_extend def env, ruledb, depdb) csb
        | HM_rule rinfo => let
            val (rdb',depdb',tgts) = extend_ruledb warn env rinfo (ruledb,depdb)
            val tgt1' =
                case tgt1 of
                  NONE => List.find (fn s => s <> ".PHONY") tgts
                | _ => tgt1
          in
            readall (tgt1',env,rdb',depdb') csb
          end
      end

fun read fname env =
    readall (NONE, env, empty_ruledb,
             Binarymap.mkDict String.compare)
            (empty_condstate, init_buf fname)

fun readlist e vref =
  map dequote (tokenize (perform_substitution e [VREF vref]))

fun find_includes dirname =
  let
    val hm_fname = OS.Path.concat(dirname, "Holmakefile")
  in
    if OS.FileSys.access(hm_fname, [OS.FileSys.A_READ]) then
      let
        val (e, _, _) = read hm_fname (base_environment())
        val raw_incs = readlist e "INCLUDES" @ readlist e "PRE_INCLUDES"
      in
        map (fn p => OS.Path.mkAbsolute {path = p, relativeTo = dirname})
            raw_incs
      end
    else []
  end

end (* struct *)
