structure HOLsexp :> HOLsexp =
struct


  open HOLsexp_dtype

  type 'a encoder = 'a -> t
  type 'a decoder = t -> 'a option

  val Nil = Symbol "nil"
  val Quote = Symbol "quote"

  val List = List.foldr Cons Nil

  val scan = HOLsexp_parser.scan
  val fromString = StringCvt.scanString scan
  val fromFile = HOLsexp_parser.raw_read_file
  val fromStream = HOLsexp_parser.raw_read_stream

  fun map_decode f d = Option.map f o d
  fun bind_decode d f x =
      case d x of
          NONE => NONE
        | SOME y => f y
  fun r3_to_p12 (x,y,z) = (x, (y, z))
  fun p12_to_r3 (x,(y,z)) = (x,y,z)
  fun pair_encode (a,b) (x,y) = Cons(a x, b y)
  fun pair_decode (a, b) (Cons(t1,t2)) =
      (case a t1 of
           NONE => NONE
         | SOME v1 => Option.map (fn v2 => (v1,v2)) (b t2))
    | pair_decode _ _ = NONE

  fun tagged_encode s enc v = Cons(Symbol s, enc v)
  fun dest_tagged s t =
      case t of
          Cons(Symbol s', rest) => if s = s' then SOME rest
                                   else NONE
        | _ => NONE
  fun tagged_decode s dec = bind_decode (dest_tagged s) dec

  fun list_encode enc els = List (map enc els)
  fun break_list s =
      let
        fun recurse A s =
            case s of
                Cons(s1, s2) => recurse (s1::A) s2
              | _ => (List.rev A, s)
      in
        recurse [] s
      end
  fun strip_list s =
      let val(sexps, last) = break_list s
      in
        if last = Nil then (sexps, NONE)
        else (sexps, SOME last)
      end
  fun list_decode dec t =
      let
        fun recurse A els =
            case els of
                [] => SOME (List.rev A)
              | h::t => Option.mapPartial (fn v => recurse (v::A) t) (dec h)
      in
        case strip_list t of
            (els, NONE) => recurse [] els
          | _ => NONE
      end

  fun singencode a v = List[a v]
  fun pair3_encode (a,b,c) =
      pair_encode(a,pair_encode(b,singencode c)) o r3_to_p12
  fun pair4_encode (a,b,c,d) =
      pair_encode(a,pair_encode(b,pair_encode(c,singencode d))) o
      (fn (u,v,w,x) => (u,(v,(w,x))))
  fun singleton [a] = SOME a
    | singleton _ = NONE
  fun sing_decode d = bind_decode (list_decode d) singleton
  fun pair3_decode (a,b,c) =
      map_decode p12_to_r3 (pair_decode(a, pair_decode(b,sing_decode c)))
  fun pair4_decode (a,b,c,d) =
      map_decode (fn (u,(v,(w,x))) => (u,v,w,x))
                 (pair_decode(a,pair_decode(b,pair_decode(c,sing_decode d))))

  fun is_list s =
      case s of
          Cons(_, s') => is_list s'
        | Symbol "nil" => true
        | _ => false

  fun int_decode (Integer i) = SOME i
    | int_decode _ = NONE

  fun symbol_decode (Symbol s) = SOME s
    | symbol_decode _ = NONE
  fun string_decode (String s) = SOME s
    | string_decode _ = NONE



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
