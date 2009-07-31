structure ReadHMF :> ReadHMF =
struct

open Holmake_types

fun readline lnum strm = let
  fun recurse (lnum, acc) latest =
      case latest of
        NONE => if null acc then NONE
              else SOME (lnum + 1, String.concat (List.rev acc))
      | SOME "\n" => SOME (lnum + 1, String.concat (List.rev acc))
      | SOME s =>
        if String.sub(s, size s - 2) = #"\\" then
          recurse (lnum + 1,
                   " " :: String.extract(s, 0, SOME (size s - 2)) :: acc)
                  (TextIO.inputLine strm)
        else
          SOME
            (lnum + 1,
             String.concat
               (List.rev (String.extract(s, 0, SOME (size s - 1)) ::
                          acc)))
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
          if c1 = #"\t" then error b "starts an unattached command"
          else
            case first_special s' of
                NONE => error b "Unrecognised"
              | SOME #"=" => (advance b, DEFN (strip_trailing_comment s))
              | SOME #":" => read_commands
                               (advance b)
                               (strip_trailing_comment s' ^ "\n")
        end
    end
end

fun readall acc b =
    case process_line b of
      (b', EOF) => (close_buf b'; List.rev acc)
    | (b', x) => readall (to_token x::acc) b'

fun read fname = readall [] (init_buf fname)

end (* struct *)
