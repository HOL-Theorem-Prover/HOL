structure HOLsexp :> HOLsexp =
struct


  open HOLsexp_dtype

  val Nil = Symbol "nil"
  val Quote = Symbol "quote"

  val fromList = List.foldr Cons Nil

  fun scan creader cs =
      case Int.scan StringCvt.DEC creader cs of
          SOME (i,cs) => SOME (Integer i, cs)
        | NONE => raise Fail "bogus"

  fun is_list s =
      case s of
          Cons(_, s') => is_list s'
        | Symbol "nil" => true
        | _ => false

  fun break_list s =
      let
        fun recurse A s =
            case s of
                Cons(s1, s2) => recurse (s1::A) s2
              | _ => (List.rev A, s)
      in
        recurse [] s
      end

  fun mem x s = CharVector.exists (fn c => c = x) s
  fun printer t =
      let
        open HOLPP
        fun symok c = mem c "-+_#!"
      in
        case t of
            Symbol s =>
            if size s > 0 andalso
               (CharVector.all (fn c => Char.isAlpha c orelse symok c) s orelse
                not (Char.isDigit (String.sub(s,0))) andalso
                CharVector.all (fn c => Char.isAlpha c orelse Char.isDigit c) s)
            then
              add_string s
            else
              add_string ("|" ^ String.translate
                            (fn #"|" => "\\|" | #"\n" => "\\n" | c => str c)
                            s ^ "|")
          | Integer i => add_string (if i < 0 then "-" ^ Int.toString (~i)
                                     else Int.toString i)
          | String s => add_string (Portable.mlquote s)
          | Cons _ =>
            (let val (els, last) = break_list t
             in
               block INCONSISTENT 1 (
                 add_string "(" ::
                 pr_list printer [add_break(1,0)] els @
                 (case last of
                      Symbol "nil" => [add_string ")"]
                    | t => [add_string " .", add_break(1,0), printer t,
                            add_string ")"])
               )
             end)
      end

end
