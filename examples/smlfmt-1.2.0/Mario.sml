fun go file = let
  val s = TextIO.openIn file
  (* val s = TextIO.openIn "test.sml" *)
  fun readFile acc = case TextIO.inputLine s of
    SOME line => readFile (line :: acc)
  | NONE => (TextIO.closeIn s; concat (rev acc))
  val body = readFile []
  val infixes =
    map (fn x => (x, 0, false)) ["++", "&&", "|->", "THEN", "THEN1",
      "THENL", "THEN_LT", "THENC", "ORELSE", "ORELSE_LT", "ORELSEC", "THEN_TCL",
      "ORELSE_TCL", "?>", "|>", "|>>", "||>", "||->",
      ">>", ">-", ">|", "\\\\", ">>>", ">>-", "??", ">~", ">>~", ">>~-"] @
    [("by", 8, false), ("suffices_by", 8, false), ("$", 1, true)] @
    List.concat (map (fn ((b, a), l) => map (fn x => (x, a, b)) l) [
      ((false, 7), ["*", "/", "div", "mod"]),
      ((false, 6), ["+", "-", "^"]),
      ((true, 5), ["::", "@"]),
      ((false, 4), ["=", "<>", ">", ">=", "<", "<="]),
      ((false, 3), [":=", "o"]),
      ((false, 0), ["before"])])
  val sc = foldl
    (fn ((k, n, r), b) => Binarymap.insert (b, k, (n, r)))
    (Binarymap.mkDict String.compare) infixes
  val {parseDec, ...} = Parser.parseSML file body
    (fn (start, stop) => fn err =>
      (print (concat ["error ", Int.toString start, "-",
        Int.toString stop, ": ", err, "\n"])
        ; raise Bind
        ))
    sc
  fun pull () = case parseDec () of
    SOME dec => (
      (* PolyML.print dec; *)
       pull ())
  | NONE => ()
  in pull () end;

fun testall () = let
  val s = TextIO.openIn "../../../out.log"
  fun readFile acc = case TextIO.inputLine s of
    SOME line => readFile (String.extract(line, 0, SOME (size line - 1)) :: acc)
  | NONE => (TextIO.closeIn s; rev acc)

  fun f file = let
    val _ = print (file ^ "\n")
    val _ = go ("../../../" ^ file)
    in () end
  in app f (readFile []) end

(*
val _ = go "../../../tools/Holmake/tests/gh1371/bugScript.sml";
val _ = go "test.sml";
val _ = testall ();
*)

structure SMLPrinterNew = struct
open Ast

fun ident s = Ident {op_ = NONE, id = s}

local
  fun toEnd s p = case String.sub (s, p) of
    #"\\" => p+1
  | c => if Char.isSpace c then toEnd s (p+1) else raise Unreachable

  (* fun parseHex s p n res =
    if n = 0 then if res > 255 then NONE else SOME (chr res) else
    case String.sub (s, p) handle Subscript => #"\000" of c =>
    if #"0" <= c andalso c <= #"9" then
      parseHex s (p+1) (n-1) (res * 16 + ord c - ord #"0")
    else if #"a" <= c andalso c <= #"f" then
      parseHex s (p+1) (n-1) (res * 16 + ord c - ord #"a" + 10)
    else if #"A" <= c andalso c <= #"F" then
      parseHex s (p+1) (n-1) (res * 16 + ord c - ord #"A" + 10)
    else NONE *)

  fun parseDec s p n res =
    if n = 0 then if res > 255 then NONE else SOME (chr res) else
    case String.sub (s, p) handle Subscript => #"\000" of c =>
    if #"0" <= c andalso c <= #"9" then
      parseDec s (p+1) (n-1) (res * 10 + ord c - ord #"0")
    else NONE
in
fun decodeStr s start stop = let
  fun push start p acc =
    if start = p then acc else String.substring (s, start, p - start) :: acc
  fun loop start p acc =
    if p = stop then push start p acc else
    case String.sub (s, p) of
      #"\\" => (
      case String.sub (s, p+1) of
        #"a" => loop (p+2) (p+2) ("\a" :: push start p acc)
      | #"b" => loop (p+2) (p+2) ("\b" :: push start p acc)
      | #"t" => loop (p+2) (p+2) ("\t" :: push start p acc)
      | #"n" => loop (p+2) (p+2) ("\n" :: push start p acc)
      | #"v" => loop (p+2) (p+2) ("\v" :: push start p acc)
      | #"f" => loop (p+2) (p+2) ("\f" :: push start p acc)
      | #"r" => loop (p+2) (p+2) ("\r" :: push start p acc)
      | #"\\" => loop (p+2) (p+2) ("\\" :: push start p acc)
      | #"\"" => loop (p+2) (p+2) ("\"" :: push start p acc)
      | #"^" => (
        case ord (String.sub (s, p+2)) handle Subscript => 0 of c =>
        if 64 <= c andalso c <= 95 then
          loop (p+3) (p+3) (String.str (chr (c - 64)) :: push start p acc)
        else loop start (p+2) acc)
      | #"u" => raise Fail "unicode escapes are not supported"
      | c =>
        if Char.isSpace c then
          case push start p acc of acc =>
          case toEnd s (p+2) of q => loop q q acc
        else if #"0" <= c andalso c <= #"2" then
          case parseDec s (p+1) 3 0 of
            NONE => loop start (p+2) acc
          | SOME c => loop (p+4) (p+4) (String.str c :: push start p acc)
        else loop start (p+2) acc)
    | _ => loop start (p+1) acc
  in String.concat (rev (loop start start [])) end
end

fun encodeStr ss bef aft = let
  val (s, start, len) = Substring.base ss
  val stop = start + len
  fun push start p acc =
    if start = p then acc else String.substring (s, start, p - start) :: acc
  fun loop start p acc =
    if p = stop then push start p acc else
      case String.sub (s, p) of c =>
      if chr 32 <= c andalso c <= chr 126 then
        case c of
          #"\\" => loop (p+1) (p+1) ("\\\\" :: push start p acc)
        | #"\"" => loop (p+1) (p+1) ("\\\"" :: push start p acc)
        | _ => loop start (p+1) acc
      else case c of
        #"\a" => loop (p+1) (p+1) ("\\a" :: push start p acc)
      | #"\b" => loop (p+1) (p+1) ("\\b" :: push start p acc)
      | #"\t" => loop (p+1) (p+1) ("\\t" :: push start p acc)
      | #"\n" => loop (p+1) (p+1) ("\\n" :: push start p acc)
      | #"\v" => loop (p+1) (p+1) ("\\v" :: push start p acc)
      | #"\f" => loop (p+1) (p+1) ("\\f" :: push start p acc)
      | #"\r" => loop (p+1) (p+1) ("\\r" :: push start p acc)
      | #"\\" => loop (p+1) (p+1) ("\\\\" :: push start p acc)
      | #"\"" => loop (p+1) (p+1) ("\\\"" :: push start p acc)
      | c => let
        val n = ord c
        val a = chr (n div 100 + ord #"0")
        val b = chr ((n div 10) mod 10 + ord #"0")
        val c = chr (n mod 10 + ord #"0")
        in loop (p+1) (p+1) (implode [#"\\", a, b, c] :: push start p acc) end
  in String.concat (rev (bef :: loop start start [aft])) end

(* fun delimited left {args, ...} f delim right =
  append left (fn () =>
    append (flatmap (fn e => append (f e) (fn () => delim)) args) right) *)

  (* datatype exp =
  | List of {left: int, elems: exp delimited, right: int option, stop: int}
    (** [ exp, ..., exp ] *)
  | Tuple of {left: int, elems: exp delimited, right: int option, stop: int}
    (** ( exp, ..., exp ) *)
  | Record of {left: int, elems: row delimited, right: int option, stop: int}
    (** { lab = exp, ..., lab = exp } *)
  | Parens of {left: int, exp: exp, right: int option, stop: int} (** ( exp ) *)
  | Typed of {exp: exp, colon: int, ty: ty} (** exp : ty *)
  | Layered of
    {op_: int option, id: ident, ty: {colon: int, ty: ty} option, as_: int, pat: exp}
    (** [op] vid [:ty] as pat *)
  | Or of exp delimited (** SuccessorML "or patterns": pat | pat | ... | pat *)
  | App of exp * exp (** exp exp *)
 *)

fun expandRecord f pat {left, elems = {args, delims}, right, stop} = let
  fun reord [] NONE acc = rev acc
    | reord [] (SOME p) acc = rev (DotDotDot p :: acc)
    | reord (DotDotDot p :: ls) _ acc = reord ls (SOME p) acc
    | reord (LabEq {lab, eq, exp} :: ls) dot acc =
      reord ls dot (LabEq {lab = lab, eq = eq, exp = f exp} :: acc)
    | reord (LabAs {id, ty, aspat} :: ls) dot acc = let
      val aspat = Option.map (fn {as_, exp} => {as_ = as_, exp = f exp}) aspat
      fun typed exp NONE = exp
        | typed exp (SOME {colon, ty}) = Typed {exp = exp, colon = colon, ty = ty}
      val lab = if pat then LabAs {id = id, ty = ty, aspat = aspat} else
        case aspat of
          NONE => LabEq {lab = id, eq = #1 id, exp = typed (ident id) ty}
        | SOME {as_, exp} => LabEq {lab = id, eq = as_, exp = typed exp ty}
      in reord ls dot (lab :: acc) end
  val elems = {args = reord args NONE [], delims = delims}
  in {left = left, elems = elems, right = right, stop = stop} end

fun mkLocPragma line col s =
  concat [" (*#loc ", Int.toString (line + 1), " ", Int.toString (col + 1), "*)", s]

exception HasOrPat
fun mapDelim f {args, delims} = {args = map f args, delims = delims}
fun expandExp true (e as Wild _) = e
  | expandExp false (Wild p) =
    Raise {raise_ = p, exp = App (ident (p, "Fail"), StringConstant (p, "\"_\""))}
  | expandExp _ (e as IntegerConstant _) = e
  | expandExp _ (e as WordConstant _) = e
  | expandExp _ (StringConstant (p, s)) = let
    val s = decodeStr s 1 (size s - 1)
    in StringConstant (p, encodeStr (Substring.full s) "\"" "\"") end
  | expandExp _ (CharConstant (p, s)) = let
    val s = decodeStr s 2 (size s - 1)
    in CharConstant (p, encodeStr (Substring.full s) "#\"" "\"") end
  | expandExp _ (e as RealConstant _) = e
  | expandExp _ (e as Unit _) = e
  | expandExp _ (e as Ident _) = e
  | expandExp pat (List {left, elems, right, stop}) =
    List {left = left, elems = mapDelim (expandExp pat) elems, right = right, stop = stop}
  | expandExp pat (Tuple {left, elems, right, stop}) =
    Tuple {left = left, elems = mapDelim (expandExp pat) elems, right = right, stop = stop}
  | expandExp pat (Record r) = Record (expandRecord (expandExp pat) pat r)
  | expandExp pat (Parens {left, exp, right, stop}) =
    Parens {left = left, exp = expandExp pat exp, right = right, stop = stop}
  | expandExp pat (Infix {left, id, right}) =
    Infix {left = expandExp pat left, id = id, right = expandExp pat right}
  | expandExp pat (Typed {exp, colon, ty}) = Typed {exp = expandExp pat exp, colon = colon, ty = ty}
  | expandExp pat' (Layered {op_, id, ty, as_, pat}) =
    Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = expandExp pat' pat}
  | expandExp _ (Or _) = raise HasOrPat
  | expandExp _ (e as Select _) = e
  | expandExp pat (Sequence {left, elems, right, stop}) =
    Sequence {left = left, elems = mapDelim (expandExp pat) elems, right = right, stop = stop}
  | expandExp _ (LetInEnd {let_, dec, in_, exps, end_, stop}) =
    LetInEnd {let_ = let_, dec = map expandDec dec, in_ = in_,
      exps = mapDelim (expandExp false) exps, end_ = end_, stop = stop}
  | expandExp pat (App (e1, e2)) = App (expandExp pat e1, expandExp pat e2)
  | expandExp _ (AndAlso {left, andalso_, right}) =
    AndAlso {left = expandExp false left, andalso_ = andalso_, right = expandExp false right}
  | expandExp _ (OrElse {left, orelse_, right}) =
    OrElse {left = expandExp false left, orelse_ = orelse_, right = expandExp false right}
  | expandExp _ (Handle {exp, handle_, elems}) =
    Handle {exp = expandExp false exp, handle_ = handle_, elems = expandArms elems}
  | expandExp _ (Raise {raise_, exp}) = Raise {raise_ = raise_, exp = expandExp false exp}
  | expandExp _ (IfThenElse {if_, exp1, then_, exp2, else_}) = let
    val exp1 = expandExp false exp1
    val exp2 = expandExp false exp2
    val else_ = case else_ of
      NONE => SOME {else_ = if_, exp3 = Unit {left = if_, right = if_}}
    | SOME {else_, exp3} => SOME {else_ = else_, exp3 = expandExp false exp3}
    in IfThenElse {if_ = if_, exp1 = exp1, then_ = then_, exp2 = exp2, else_ = else_} end
  | expandExp _ (While {while_, exp1, do_, exp2}) =
    While {while_ = while_, exp1 = expandExp false exp1, do_ = do_, exp2 = expandExp false exp2}
  | expandExp _ (Case {case_, exp, of_, elems}) =
    Case {case_ = case_, exp = expandExp false exp, of_ = of_, elems = expandArms elems}
  | expandExp _ (Fn {fn_, elems}) = Fn {fn_ = fn_, elems = expandArms elems}

  | expandExp _ (HOLFullQuote {head, type_q, quote, stop, ...}) = let
    val id = (#1 head, case type_q of NONE => "Parse.Term" | SOME _ => "Parse.Type")
    in App (ident id, expandQuote (#1 head) stop quote) end
  | expandExp _ (HOLQuote {head, quote, stop, ...}) = expandQuote (#1 head) stop quote
  | expandExp _ (HOLLinePragma {hash_, value, ...}) = IntegerConstant (hash_, Int.toString value)
  | expandExp _ (HOLFilePragma {hash_, value, ...}) =
    StringConstant (hash_, encodeStr (Substring.full value) "\"" "\"")
  | expandExp _ (HOLLinePragmaWith {hash_, ...}) = Unit {left = hash_, right = hash_}
  | expandExp _ (HOLFilePragmaWith {hash_, ...}) = Unit {left = hash_, right = hash_}
  | expandExp _ (EmptyExp p) = Unit {left = p, right = p}
  | expandExp _ (BadExp {start = p, ...}) =
    Raise {raise_ = p, exp = App (ident (p, "Fail"), StringConstant (p, "\"malformed\""))}

and expandArms elems =
  map (fn {bar, pat, arrow, exp} =>
    {bar = bar, pat = expandExp true pat, arrow = arrow, exp = expandExp false exp}) elems
  handle HasOrPat => let
    fun list [] _ f = f []
      | list (x :: xs) g f =
        g x (fn x => list xs g (fn xs => f (x :: xs)))

    fun delims {args, delims} g f =
      list args g (fn args => f {args = args, delims = delims})

    fun onPat (List {left, elems, right, stop}) f =
        delims elems onPat
          (fn elems => f (List {left = left, elems = elems, right = right, stop = stop}))
      | onPat (Tuple {left, elems, right, stop}) f =
        delims elems onPat
          (fn elems => f (Tuple {left = left, elems = elems, right = right, stop = stop}))
      | onPat (Record r) f = let
        val {left, elems, right, stop} = expandRecord (fn x => x) true r
        in delims elems onRow (fn elems =>
          f (Record {left = left, elems = elems, right = right, stop = stop}))
        end
      | onPat (Parens {left, exp, right, stop}) f =
        onPat exp (fn exp => f (Parens {left = left, exp = exp, right = right, stop = stop}))
      | onPat (Typed {exp, colon, ty}) f =
        onPat exp (fn exp => f (Typed {exp = exp, colon = colon, ty = ty}))
      | onPat (Layered {op_, id, ty, as_, pat}) f =
        onPat pat (fn pat => f (Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = pat}))
      | onPat (App (e1, e2)) f = onPat e1 (fn e1 => onPat e2 (fn e2 => f (App (e1, e2))))
      | onPat (Or {args, ...}) f = orList args f
      | onPat e f = f (expandExp true e)

    and onRow (LabEq {lab, eq, exp}) f =
        onPat exp (fn exp => f (LabEq {lab = lab, eq = eq, exp = exp}))
      | onRow (LabAs {id, ty, aspat = SOME {as_, exp}}) f =
        onPat exp (fn exp => f (LabAs {id = id, ty = ty, aspat = SOME {as_ = as_, exp = exp}}))
      | onRow e f = f e

    and orList [] _ = (fn x => x)
      | orList (e :: es) f = onPat e f o orList es f

    fun arms [] = (fn x => x)
      | arms ({bar, pat, arrow, exp} :: ls) =
        onPat pat (fn pat => fn l => {bar = bar, pat = pat, arrow = arrow, exp = exp} :: l)
          o arms ls
    in arms elems [] end

and expandQuote start stop toks = let
  fun go [] acc = rev acc
    | go (QuoteLiteral {line, col, value} :: rest) acc = let
      val s = encodeStr (Substring.full (mkLocPragma line col (Substring.string value))) "\"" "\""
      in go rest (App (ident (start, "QUOTE"), StringConstant (start, s)) :: acc) end
    | go (QuoteAntiq {exp, ...} :: rest) acc =
      go rest (App (ident (start, "ANTIQUOTE"), expandExp false exp) :: acc)
    | go (DefinitionLabel _ :: _) _ = raise Unreachable
  in List {left = start, elems = {args = go toks [], delims = []}, right = NONE, stop = stop} end

and expandDec dec = dec

datatype lazyseq =
    Nil
  | String of string * (unit -> lazyseq)

fun str s = String (s, fn () => Nil)
fun ch c = str (String.str c)

fun append Nil y = y ()
  | append (String (s, x)) y = String (s, fn () => append (x ()) y)

fun flatmap _ [] = Nil
  | flatmap f (x :: xs) = append (f x) (fn () => flatmap f xs)

fun token s = String (s, fn () => str " ")

fun otoken NONE _ = Nil
  | otoken (SOME _) s = token s

(* fun fromRow r = () *)

(* fun fromExp _ (Wild _) = str "raise Fail \"_\" "
fun fromExp _ (IntegerConstant (_, s)) = token s
  | fromExp _ (WordConstant (_, s)) = token s
  | fromExp _ (StringConstant (_, s)) = let
    val s = decodeStr s 1 (size s - 1)
    in token (encodeStr s "\"" "\"") end
  | fromExp _ (CharConstant (_, s)) = let
    val s = decodeStr s 2 (size s - 1)
    in token (encodeStr s "#\"" "\"") end
  | fromExp _ (RealConstant (_, s)) = token s
  | fromExp _ (Unit _) = token "()"
  | fromExp _ (Ident {op_, id}) = append (otoken op_ "op") (fn () => token (#2 id))
  | fromExp pat (List {elems, ...}) =
    delimited (token "[") elems fromExp pat (token ",") (fn () => token "]")
  | fromExp pat (Tuple {elems, ...}) =
    delimited (token "(") elems fromExp pat (token ",") (fn () => token ")")
  | fromExp pat (Record {elems, ...}) =
    delimited (token "{") elems (fromRow pat) (token ",") (fn () => token "}") *)

     (* (fn () => token (#2 id)) *)


  (* datatype exp =
  | Tuple of {left: int, elems: exp delimited, right: int option, stop: int}
    (** ( exp, ..., exp ) *)
  | Record of {left: int, elems: row delimited, right: int option, stop: int}
    (** { lab = exp, ..., lab = exp } *)
  | Parens of {left: int, exp: exp, right: int option, stop: int} (** ( exp ) *)
  | Infix of {left: exp, id: ident, right: exp} (** exp vid exp *)
  | Typed of {exp: exp, colon: int, ty: ty} (** exp : ty *)
  | Layered of
    {op_: int option, id: ident, ty: {colon: int, ty: ty} option, as_: int, pat: exp}
    (** [op] vid [:ty] as pat *)
  | Or of exp delimited (** SuccessorML "or patterns": pat | pat | ... | pat *)
  | Select of {hash: int, label: ident} (** # label *)
  | Sequence of {left: int, elems: exp delimited, right: int option, stop: int}
    (** (exp; ...; exp) *) (* TODO: this is stupid *)
  | LetInEnd of
    {let_: int, dec: dec list, in_: int option, exps: exp delimited, end_: int option, stop: int}
    (** let dec in exp [; exp ...] end *)
  | App of exp * exp (** exp exp *)
  | AndAlso of {left: exp, andalso_: int, right: exp} (** exp andalso exp *)
  | OrElse of {left: exp, orelse_: int, right: exp} (** exp orelse exp *)
  | Handle of {exp: exp, handle_: int, elems: arm list}
    (** exp handle pat => exp [| pat => exp ...] *)
  | Raise of {raise_: int, exp: exp} (** raise exp *)
  | IfThenElse of {if_: int, exp1: exp, then_: int option, exp2: exp, else_: int option, exp3: exp}
    (** if exp then exp else exp *)
  | While of {while_: int, exp1: exp, do_: int option, exp2: exp} (** while exp do exp *)
  | Case of {case_: int, exp: exp, of_: int option, elems: arm list}
    (** case exp of pat => exp [| pat => exp ...] *)
  | Fn of {fn_: int, elems: arm list} (** fn pat => exp [| pat => exp ...] *)

  | HOLFullQuote of {
      head: int * string, type_q: int option,
      quote: qbody, end_tok: (int * string) option, stop: int}
  | HOLQuote of {head: int * string, quote: qbody, end_tok: (int * string) option, stop: int}
  | HOLLinePragma of {hash_: int, left: int, line_: int, right: int option, stop: int} (* #(LINE) *)
  | HOLLinePragmaWith of {
      hash_: int, left: int, line_: int, eq_: int,
      line: int * string option, col: {comma_: int, col: int * string option} option,
      right: int option, stop: int} (* #(LINE=3) this is BS *)
  | HOLFilePragma of {hash_: int, left: int, file_: int, right: int option, stop: int} (* #(FILE) *)
  | HOLFilePragmaWith of {
      hash_: int, left: int, file_: int, eq_: int,
      file: int * string option, right: int option, stop: int} (* #(FILE=foo.sml) this is BS *)

  | EmptyExp of int
  | BadExp of {start: int, stop: int} *)

end;
