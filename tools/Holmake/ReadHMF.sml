structure ReadHMF :> ReadHMF =
struct

open Holmake_types

datatype cond_position = GrabbingText | NoTrueCondYet | SkippingElses
val empty_condstate = [] : cond_position list

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

fun evaluate_cond env s =
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
                  | _ => SOME sense)
        | _ => raise Fail ("ReadHMF: "^nm^" not followed by a variable name.")
      end
    else
      NONE

fun getline env (condstate, b) =
    case (currentline b, condstate) of
      (NONE, []) => (b, NONE, condstate)
    | (NONE, _ :: _) => raise Fail "ReadHMF: unterminated conditional"
    | (SOME s, SkippingElses :: rest) => let
        val s = strip_leading_wspace s
      in
        if String.isPrefix "endif" s then getline env (rest, advance b)
        else if String.isPrefix "ifdef" s orelse String.isPrefix "ifndef" s orelse
                String.isPrefix "ifeq" s
        then
          getline env (SkippingElses::SkippingElses::rest, advance b)
        else
          getline env (SkippingElses::rest, advance b)
      end
    | (SOME s, NoTrueCondYet::rest) => let
        val s = strip_leading_wspace s
      in
        if String.isPrefix "endif" s then getline env (rest, advance b)
        else if String.isPrefix "else" s then let
            val s = strip_leading_wspace (String.extract(s, 4, NONE))
          in
            if String.isPrefix "if" s then
              case evaluate_cond env s of
                NONE => raise Fail "ReadHMF: bogus string following else"
              | SOME false => getline env (NoTrueCondYet::rest, advance b)
              | SOME true => getline env (GrabbingText::rest, advance b)
            else if s = "" then getline env (GrabbingText::rest, advance b)
            else raise Fail "ReadHMF: bogus string following else"
          end
        else getline env (condstate, advance b)
      end
    | (SOME s0, _) => let
        val s = strip_leading_wspace s0
      in
        if String.isPrefix "endif" s then
          if null condstate then raise Fail "ReadHMF: unpaired endif"
          else getline env (tl condstate, advance b)
        else if String.isPrefix "else" s then
          if null condstate then raise Fail "ReadHMF: unpaired else"
          else getline env (SkippingElses::tl condstate, advance b)
        else if String.isPrefix "if" s then
          case evaluate_cond env s of
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
              | SOME _ => raise Fail "ReadHMF: can't happen"
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

end (* struct *)
