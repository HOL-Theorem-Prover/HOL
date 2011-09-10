structure ReadHMF :> ReadHMF =
struct

open Holmake_types

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

fun read_commands b head =
    case currentline b of
      NONE => (b, RULE head)
    | SOME s => let
        val s' = strip_leading_wspace s
      in
        if s' = "" orelse String.sub(s',0) = #"#" then
          read_commands (advance b) head
        else
          case String.sub(s',0) of
            #"\t" => read_commands (advance b) (head ^ s' ^ "\n")
          | c => (b, RULE head)
      end


fun process_line b = let
in
  case currentline b of
    NONE => (b, EOF)
  | SOME s => let
      val s' = strip_leading_wspace s
    in
      if s' = "" orelse String.sub(s',0) = #"#" then
        process_line (advance b)
      else let
          val c1 = String.sub(s',0)
        in
          if c1 = #"\t" then error b "TAB starts an unattached command"
          else
            case first_special s' of
                NONE => error b ("Unrecognised character: \""^
                                 String.toString (str c1) ^ "\"")
              | SOME #"=" => (advance b, DEFN (strip_trailing_comment s))
              | SOME #":" => read_commands
                               (advance b)
                               (strip_trailing_comment s' ^ "\n")
              | SOME _ => raise Fail "ReadHMF: can't happen"
        end
    end
end

fun readall (acc as (tgt1,env,ruledb,depdb)) b =
    case process_line b of
      (b', EOF) => let
        val _ = close_buf b'
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
    | (b', x) => let
        fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
      in
        case to_token x of
          HM_defn def => readall (tgt1,env_extend def env, ruledb, depdb) b'
        | HM_rule rinfo => let
            val (rdb',depdb',tgts) = extend_ruledb warn env rinfo (ruledb,depdb)
            val tgt1' =
                case tgt1 of
                  NONE => List.find (fn s => s <> ".PHONY") tgts
                | _ => tgt1
          in
            readall (tgt1',env,rdb',depdb') b'
          end
      end

fun read fname env =
    readall (NONE, env, empty_ruledb,
             Binarymap.mkDict String.compare)
            (init_buf fname)

end (* struct *)
