structure TheoryDat :> TheoryDat =
struct

type parent = {thy : string, hash : string}
datatype 'a result = Success of 'a | Failure of string
datatype resolution = Artifact of string
                    | Missing
                    | Ambiguous of string list
datatype problem = HeaderError of string
                 | ResolverError of parent * string
                 | MissingParent of parent
                 | AmbiguousParent of parent * string list
                 | UnreadableParent of parent * string * string
                 | HashMismatch of parent * string

exception BadHeader of string

(* Consume only the prefix. In particular, never search for parent-like
   strings in tables or loadable theory data. *)
fun read_parents path =
    let
      val ins = TextIO.openIn path
      fun bad () = raise BadHeader "Malformed or truncated theory header"
      fun peek () = TextIO.lookahead ins
      fun take () = case TextIO.input1 ins of SOME c => c | NONE => bad ()
      fun space () =
          case peek () of
              SOME c =>
                if Char.isSpace c then (ignore (take ()); space ())
                else if c = #";" then
                  let fun comment () =
                          case TextIO.input1 ins of
                              NONE => ()
                            | SOME #"\n" => ()
                            | SOME _ => comment ()
                  in comment (); space () end
                else ()
            | NONE => ()
      fun expect c = (space (); if take () = c then () else bad ())
      fun tag s =
          (space ();
           List.app (fn c => if take () = c then () else bad ())
                    (String.explode s);
           case peek () of
               SOME c => if Char.isSpace c orelse c = #"(" orelse c = #")"
                         then () else bad ()
             | NONE => bad ())
      fun quoted () =
          let
            val _ = expect #"\""
            fun escape () =
                case take () of
                    #"\"" => #"\""
                  | #"\\" => #"\\"
                  | #"a" => #"\a"
                  | #"b" => #"\b"
                  | #"f" => #"\f"
                  | #"n" => #"\n"
                  | #"r" => #"\r"
                  | #"t" => #"\t"
                  | #"^" =>
                      let val n = Char.ord (take ())
                      in if n >= 64 andalso n <= 95
                         then Char.chr (n - 64) else bad () end
                  | c =>
                      if Char.isDigit c then
                        let val d = take ()
                            val e = take ()
                            val n = (Char.ord c - 48) * 100 +
                                    (Char.ord d - 48) * 10 +
                                    Char.ord e - 48
                        in if Char.isDigit d andalso Char.isDigit e
                              andalso n <= Char.maxOrd
                           then Char.chr n else bad () end
                      else bad ()
            fun loop acc =
                case take () of
                    #"\"" => String.implode (List.rev acc)
                  | #"\\" => loop (escape () :: acc)
                  | c => loop (c :: acc)
          in loop [] end
      fun parents acc =
          (space ();
           case peek () of
               SOME #")" => (ignore (take ()); List.rev acc)
             | SOME #"(" =>
                 let
                   val _ = expect #"("
                   val thy = quoted ()
                   val _ = expect #"."
                   val hash = quoted ()
                   val _ = expect #")"
                   val _ =
                       if thy <> "" andalso
                          (thy = "min" orelse
                           (size hash = 40 andalso
                            List.all (fn c => Char.isDigit c orelse
                                              (c >= #"a" andalso c <= #"f"))
                                     (String.explode hash)))
                       then () else bad ()
                   val _ =
                       if List.exists (fn {thy = t, hash = _} => t = thy) acc
                       then bad () else ()
                 in parents ({thy = thy, hash = hash} :: acc) end
             | _ => bad ())
      fun parse () =
          let
            val _ = expect #"("
            val _ = tag "theory"
            val _ = expect #"("
            val _ = quoted ()
            val ps = parents []
            val _ = expect #"("
            val _ = tag "core-data"
          in ps end
      val ps = parse () handle e => (TextIO.closeIn ins; raise e)
      val _ = TextIO.closeIn ins
    in Success ps end
    handle e => Failure (General.exnMessage e)

fun validate {path, resolve} =
    case read_parents path of
        Failure s => [HeaderError s]
      | Success ps =>
          let
            fun check (p as {thy, hash}) =
                if thy = "min" then
                  if hash = "" then [] else [HashMismatch (p, "")]
                else
                  (case resolve thy of
                      Missing => [MissingParent p]
                    | Ambiguous paths => [AmbiguousParent (p, paths)]
                    | Artifact file =>
                        ((let val actual = SHA1.sha1_file {filename = file}
                          in if hash = actual then []
                             else [HashMismatch (p, actual)] end)
                         handle e =>
                           [UnreadableParent (p, file, General.exnMessage e)]))
                  handle e => [ResolverError (p, General.exnMessage e)]
          in List.concat (map check ps) end

end
