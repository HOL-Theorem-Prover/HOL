structure HOLParser :> HOLParser = struct
open HOLAst

fun mem x = List.exists (fn y => x = y)

exception Unreachable
type scope = (string, int * bool) Binarymap.dict

val initialScope: scope = let
  val infixes =
    List.concat (map (fn ((b, a), l) => map (fn x => (x, a, b)) l) [
      ((false, 0), ["before", "++", "&&", "|->", "THEN", "THEN1",
        "THENL", "THEN_LT", "THENC", "ORELSE", "ORELSE_LT", "ORELSEC",
        "THEN_TCL", "ORELSE_TCL", "?>", "|>", "|>>", "||>", "||->",
        ">>", ">-", ">|", "\\\\", ">>>", ">>-", "??", ">~", ">>~", ">>~-"]),
      ((true, 0), ["##", "?"]),
      ((true, 1), ["$"]),
      ((false, 3), [":=", "o"]),
      ((true, 3), ["-->"]),
      ((false, 4), ["=", "<>", ">", ">=", "<", "<="]),
      ((true, 5), ["::", "@"]),
      ((false, 6), ["+", "-", "^"]),
      ((false, 7), ["*", "/", "div", "mod"]),
      ((false, 8), ["via", "by", "suffices_by"]),
      ((false, 9), ["using"])])
  val sc = foldl
    (fn ((k, n, r), b) => Binarymap.insert (b, k, (n, r)))
    (Binarymap.mkDict String.compare) infixes
  in sc end

type result = {
  getScope: unit -> scope,
  parseDec: unit -> dec option,
  body: DString.dstring,
  events: events }

fun parseSML file read parseError: scope -> result = let
  val pos = ref 0
  val body = DString.new 1024
  val evts = DArray.new (1, LineEvent (0, 0))
  val events = {initFile = file, evts = evts}
  fun getch p = DString.sub (body, p) handle Subscript =>
    case read 1024 of "" => #"\000" | s => (DString.appendStr (body, s); getch p)
  fun ahead i = getch (!pos + i)
  fun cur () = getch (!pos)
  fun next () = pos := !pos + 1
  fun nextn i = pos := !pos + i
  fun takeWhile f = if f (cur ()) then (next (); takeWhile f) else ()
  fun ws () = takeWhile Char.isSpace
  fun isIdRest c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"
  val isIdSym = Char.contains "!%&$#+-/:<=>?@\\~^|*"
  fun colZero start = start = 0 orelse DString.sub (body, start - 1) = #"\n"
  val _ = ws ()

  fun finishString p = case cur () of
    #"\000" => parseError (p, !pos) "unclosed string literal"
  | #"\"" => next ()
  | #"\\" => (next ();
    if Char.isSpace (cur ()) then
      (next (); ws (); (case cur () of #"\\" => next () | _ => ()); finishString p)
    else (next (); finishString p))
  | _ => (next (); finishString p)

  fun finishComment p = case cur () of
    #"\000" => parseError (p, !pos) "unclosed comment"
  | #"*" => (next (); if cur () = #")" then next () else finishComment p)
  | #"(" => (next ();
    if cur () = #"*" then (next (); finishComment (!pos - 2)) else (); finishComment p)
  | _ => (next (); finishComment p)

  fun finishId () = if cur () <> #"." then () else case ahead 1 of c =>
    if isIdSym c then (next (); takeWhile isIdSym; finishId ()) else
    if Char.isAlpha c then (next (); takeWhile isIdRest; finishId ()) else ()

  fun finishRealAfterExp () = (
    if cur () = #"~" then next () else ();
    takeWhile Char.isDigit)
  fun finishReal () = (
    takeWhile Char.isDigit;
    case cur () of
      #"e" => (next (); finishRealAfterExp ())
    | #"E" => (next (); finishRealAfterExp ())
    | _ => ())
  fun finishRealAfterDot () = (
    if Char.isDigit (cur ()) then next () else parseError (!pos, !pos) "Expected digit";
    finishReal ())

  datatype token =
    EOF
  | StringTk
  | CharTk
  | TyVarTk
  | IdentTk
  | IntTk
  | WordTk
  | RealTk
  | OpenQuoteTk
  | Symbol of char
  | ErrorTk

  fun finishInt () = (
    takeWhile Char.isDigit;
    case cur () of
      #"." => (next (); finishRealAfterDot (); RealTk)
    | #"e" => (next (); finishRealAfterExp (); RealTk)
    | #"E" => (next (); finishRealAfterExp (); RealTk)
    | _ => IntTk)

  fun finishIntAfterZero () = case cur () of
    #"x" => if Char.isHexDigit (ahead 1) then (nextn 2; takeWhile Char.isHexDigit; IntTk) else IntTk
  | #"w" => (case ahead 1 of
      #"x" =>
      if Char.isHexDigit (ahead 2) then (nextn 3; takeWhile Char.isHexDigit; WordTk) else IntTk
    | c => if Char.isDigit c then (nextn 2; takeWhile Char.isDigit; WordTk) else IntTk)
  | #"." => (next (); finishRealAfterDot (); RealTk)
  | #"E" => (next (); finishRealAfterExp (); RealTk)
  | #"e" => (next (); finishRealAfterExp (); RealTk)
  | c => if Char.isDigit c then (next (); finishInt ()) else IntTk

  fun token () = (ws (); case cur () of
    #"\000" => (!pos, EOF)
  | #"\"" => (!pos, (next (); finishString (!pos - 1); StringTk))
  | #"~" => (!pos, (next (); case cur () of
      #"0" => (next (); finishIntAfterZero ())
    | c =>
      if Char.isDigit c then (next (); finishInt ()) else
      (takeWhile isIdSym; finishId (); IdentTk)))
  | #"0" => (!pos, (next (); finishIntAfterZero ()))
  | #"'" => (!pos, (next (); takeWhile isIdRest; TyVarTk))
  | #"." => (!pos, (next (); takeWhile (fn c => c = #"."); IdentTk))
  | #"#" => (!pos, (next (); case cur () of
      #"\"" => (next (); finishString (!pos - 2); CharTk)
    | _ => (takeWhile isIdSym; finishId (); IdentTk)))
  | #"(" => let
    val start = !pos
    val _ = next ()
    in
      if cur () = #"*" then (next (); finishComment (!pos - 2); token ()) else
      (start, Symbol #"(")
    end
  | #"`" => (!pos, (next (); case cur () of
      #"`" => (next (); OpenQuoteTk)
    | _ => OpenQuoteTk))
  | #"\226" => (!pos, (case (ahead 1, ahead 2) of
      (#"\128", #"\152") => (nextn 3; OpenQuoteTk)
    | (#"\128", #"\156") => (nextn 3; OpenQuoteTk)
    | _ => (next (); ErrorTk)))
  | c => (!pos, (next ();
    if Char.contains ")[]{},;_" c then Symbol c else
    if isIdSym c then (takeWhile isIdSym; finishId (); IdentTk) else
    if Char.isDigit c then finishInt () else
    if Char.isAlpha c then (takeWhile isIdRest; finishId (); IdentTk) else
    (next (); ErrorTk))))

  (* TODO Rename to something more generic *)
  fun ident start = DString.extract (body, start, SOME (!pos - start))

  datatype ident_kind = Regular | Keyword | HolKeyword
  fun identKind start = let
    val s = ident start
    fun holKw () = if colZero start then HolKeyword else Regular
    in (s, case s of
        ":" => Keyword | ":>" => Keyword | "|" => Keyword | "=" => Keyword | "=>" => Keyword
      | "->" => Keyword | "#" => Keyword | "abstype" => Keyword | "and" => Keyword
      | "andalso" => Keyword | "as" => Keyword | "case" => Keyword | "datatype" => Keyword
      | "do" => Keyword | "else" => Keyword | "end" => Keyword | "exception" => Keyword
      | "fn" => Keyword | "fun" => Keyword | "handle" => Keyword | "if" => Keyword
      | "in" => Keyword | "infix" => Keyword | "infixr" => Keyword | "let" => Keyword
      | "local" => Keyword | "nonfix" => Keyword | "of" => Keyword | "op" => Keyword
      | "open" => Keyword | "orelse" => Keyword | "raise" => Keyword | "rec" => Keyword
      | "then" => Keyword | "type" => Keyword | "val" => Keyword | "with" => Keyword
      | "withtype" => Keyword | "while" => Keyword | "eqtype" => Keyword | "functor" => Keyword
      | "include" => Keyword | "sharing" => Keyword | "sig" => Keyword | "signature" => Keyword
      | "struct" => Keyword | "structure" => Keyword | "where" => Keyword

      | "Datatype" => holKw () | "Type" => holKw () | "Overload" => holKw ()
      | "Definition" => holKw () | "Theorem" => holKw () | "Triviality" => holKw ()
      | "Quote" => holKw () | "Inductive" => holKw () | "CoInductive" => holKw ()
      | "Proof" => holKw () | "QED" => holKw () | "Termination" => holKw () | "End" => holKw ()
      | "Theory" => holKw () | "Ancestors" => holKw () | "Libs" => holKw ()
      | "Resume" => holKw () | "Finalise" => holKw ()

      | _ => Regular)
    end

  val lookahead = ref []
  val token = fn () => case !lookahead of
    [] => token ()
  | tk :: l => (lookahead := l; tk)
  fun unread tk = lookahead := tk :: !lookahead

  fun makeError tk r err =
    case r of
      SOME _ => ()
    | NONE => (case err of
        NONE => ()
      | SOME e => parseError (#1 tk, !pos) e; unread tk)

  fun parseInt err = case token () of
      (start, IntTk) => (start, SOME (ident start))
    | tk => (makeError tk NONE err; (#1 tk, NONE))
  fun parseIdent err = case token () of
      (start, IdentTk) => (start, SOME (ident start))
    | tk => (makeError tk NONE err; (#1 tk, NONE))

  fun parseSymbol s err = let
    val tk = token ()
    val r = case tk of (start, Symbol c) => if c = s then SOME start else NONE | _ => NONE
    val _ = makeError tk r err
    in r end

  fun parseKeyword s err = let
    val tk = token ()
    val r = case tk of (start, IdentTk) => if ident start = s then SOME start else NONE | _ => NONE
    val _ = makeError tk r err
    in r end

  fun parseHolKeyword s err = let
    val tk = token ()
    val r = case tk of
      (start, IdentTk) => if colZero start andalso ident start = s then SOME start else NONE
    | _ => NONE
    val _ = makeError tk r err
    in r end

  fun parseStop f k err = let
    val r = f (SOME err)
    val stop = case r of
      SOME n => n+k
    | NONE => (case token () of tk => (unread tk; #1 tk))
    in (r, stop) end

  fun parseDelimitedClose args delims (f as {elem, close, ...}) =
    case token () of tk =>
      case close tk of
        SOME true => ({args = rev args, delims = rev delims, stop = #1 tk}, SOME (#1 tk), !pos)
      | SOME false => (
        parseError (#1 tk, !pos) "unexpected close token";
        ({args = rev args, delims = rev delims, stop = !pos}, NONE, !pos))
      | NONE => (unread tk; case elem () of e => parseDelimitedClose2 (e :: args) delims f)
  and parseDelimitedClose2 args delims (f as {delim, close, ...}) =
    case token () of tk =>
      case close tk of
        SOME true => ({args = rev args, delims = rev delims, stop = #1 tk}, SOME (#1 tk), !pos)
      | SOME false => (
        parseError (#1 tk, !pos) "unexpected close token";
        ({args = rev args, delims = rev delims, stop = !pos}, NONE, !pos))
      | NONE => case delim tk of
          SOME true => parseDelimitedClose args (SOME (#1 tk) :: delims) f
        | SOME false => (
          parseError (#1 tk, !pos) "unexpected delimiter";
          parseDelimitedClose args (NONE :: delims) f)
        | NONE => (
          parseError (#1 tk, !pos) "expected close delimiter";
          unread tk; ({args = rev args, delims = rev delims, stop = #1 tk}, NONE, #1 tk))

  fun parseDelimited args delims (f as {elem, delim}) =
    case (elem (), token ()) of (e, tk) =>
      case delim tk of
        SOME true => parseDelimited (e :: args) (SOME (#1 tk) :: delims) f
      | SOME false => (
        parseError (#1 tk, !pos) "unexpected delimiter";
        parseDelimited (e :: args) (NONE :: delims) f)
      | NONE => (unread tk; {args = rev (e :: args), delims = rev delims, stop = #1 tk})

  fun isKeyword kw = fn (s, IdentTk) => if ident s = kw then SOME true else NONE | _ => NONE

  fun parseIdentifier' f force = let
    val tk = token ()
    (* In case of failure, record an error and return the empty string *)
    fun fail () = (
      if force then parseError (#1 tk, !pos) "expected identifier" else ();
      unread tk; (#1 tk, ""))
    in
      case tk of
        (start, IdentTk) =>
          (case identKind start of
              (id, Regular) => (start, id)
            | (id, _) => if f id then (start, id) else fail ())
      | _ => fail ()
    end
  val parseIdentifier = parseIdentifier' (fn _ => false)
  val parseIdentifierOrKw = parseIdentifier' (fn _ => true)
  val parseIdentifierOrEq = parseIdentifier' (fn s => s = "=")

  fun parseIdentifiers' f acc = case parseIdentifier' f false of
    (_, "") => rev acc
  | id => parseIdentifiers' f (id :: acc)
  val parseIdentifiers = parseIdentifiers' (fn _ => false)
  val parseIdentifiersOrKws = parseIdentifiers' (fn _ => true)

  fun parseKVals (): kvals = {
    key = parseIdentifierOrKw true,
    bind = Option.map (fn eq_ => {eq_ = eq_, vals = parseIdentifiersOrKws []})
      (parseKeyword "=" NONE) }

  fun parseAttrs f: 'a attrs = case parseSymbol #"[" NONE of
    NONE => NONE
  | SOME left => let
    val (attrs, right, stop) = parseDelimitedClose [] [] {
      elem = f,
      delim = fn (_, Symbol #",") => SOME true | _ => NONE,
      close = fn (_, Symbol #"]") => SOME true | _ => NONE }
    in SOME {left = left, attrs = attrs, right = right, stop = stop} end

  fun parseTy (prec: bool): ty = let
    val lhs = case token () of
      (start, TyVarTk) => TyVar (start, ident start)
    | (start, Symbol #"(") => let
      val (elems, right, stop) = parseDelimitedClose [] [] {
        elem = fn () => parseTy false,
        delim = fn (_, Symbol #",") => SOME true | _ => NONE,
        close = fn (_, Symbol #")") => SOME true | _ => NONE }
      in
        case elems of
          {args = [ty], delims = [], ...} =>
          TyParens {left = start, ty = ty, right = right, stop = stop}
        | _ => case token () of tk =>
          case case tk of (start, IdentTk) => SOME (identKind start) | _ => NONE of
            SOME (id, Regular) => let
            val args = Many {left = start, elems = elems, right = right, stop = stop}
            in TyCon {args = args, id = (#1 tk, id)} end
          | _ => (
            parseError (#1 tk, !pos) "expected a type constructor";
            unread tk; BadTy {start = start, stop = stop})
      end
    | (start, Symbol #"{") => let
      val (elems, right, stop) = parseDelimitedClose [] [] {
        elem = fn () => let
          val tk = token ()
          val lab = case tk of
            (start, IdentTk) =>
            (case identKind start of (id, Regular) => SOME (start, id) | _ => NONE)
          | (start, IntTk) => SOME (start, ident start)
          | _ => NONE
          val _ = case lab of SOME _ => () | NONE =>
            (parseError (#1 tk, !pos) "expected an identifier"; unread tk)
          val colon = parseKeyword ":" (SOME "expected a colon")
          in {start = #1 tk, lab = lab, colon = colon, ty = parseTy false} end,
        delim = fn (_, Symbol #",") => SOME true | (_, Symbol #";") => SOME false | _ => NONE,
        close = fn (_, Symbol #"}") => SOME true | _ => NONE }
      in TyRecord {left = start, elems = elems, right = right, stop = stop} end
    | tk =>
      case case tk of (start, IdentTk) => SOME (identKind start) | _ => NONE of
        SOME (id, Regular) => TyCon {args = Empty, id = (#1 tk, id)}
      | _ => (
        parseError (#1 tk, !pos) "expected a type";
        unread tk; BadTy {start = #1 tk, stop = #1 tk})
    fun rhs lhs = case token () of
      tk as (start, IdentTk) => (case identKind start of
        ("*", _) => if prec then (unread tk; lhs) else
          rhs (TyTuple (parseDelimited [lhs] [SOME start]
            {elem = fn () => parseTy true, delim = isKeyword "*"}))
      | ("->", _) => if prec then (unread tk; lhs) else
          rhs (TyArrow {from = lhs, arrow = start, to = parseTy false})
      | (id, Regular) => rhs (TyCon {args = One lhs, id = (#1 tk, id)})
      | _ => (unread tk; lhs))
    | tk => (unread tk; lhs)
    in rhs lhs end
  val parseTy = fn () => parseTy false

  fun parseTyVars () = case token () of
    (start, TyVarTk) => One (start, ident start)
  | tk as (start, Symbol #"(") => (case token () of
      (v, TyVarTk) => let
      val (elems, right, stop) = parseDelimitedClose2 [(v, ident v)] [] {
        elem = fn () => case token () of
            (start, TyVarTk) => (start, ident start)
          | tk => (parseError (#1 tk, !pos) "expected type variable"; unread tk; (#1 tk, "")),
        delim = fn (_, Symbol #",") => SOME true | (_, Symbol #";") => SOME false | _ => NONE,
        close = fn (_, Symbol #")") => SOME true | _ => NONE }
      in Many {left = start, elems = elems, right = right, stop = stop} end
    | tk2 => (unread tk2; unread tk; Empty))
  | tk => (unread tk; Empty)

  fun parseTyBind (): tybind = {
    tyvars = parseTyVars (),
    tycon = parseIdentifier true,
    bind = Option.map (fn eq => {eq = eq, ty = parseTy ()}) (parseKeyword "=" NONE) }

  fun updateScope (sc:scope): dec -> scope = let
    fun updateInfix right prec elems (sc:scope): scope =
      case case prec of SOME (_, prec) => Int.fromString prec | NONE => SOME 0 of
        NONE => sc
      | SOME prec => let
        fun go [] sc = sc
          | go ((_, "") :: rest) sc = go rest sc
          | go ((_, id) :: rest) sc = go rest (Binarymap.insert (sc, id, (prec, right)))
        in go elems sc end
    fun updateNonfix [] sc = sc
      | updateNonfix ((_, "") :: rest) sc = updateNonfix rest sc
      | updateNonfix ((_, id) :: rest) sc =
        updateNonfix rest (#1 (Binarymap.remove (sc, id)) handle Binarymap.NotFound => sc)
    in fn
        DecInfix {prec, elems, ...} => updateInfix false prec elems sc
      | DecInfixr {prec, elems, ...} => updateInfix true prec elems sc
      | DecNonfix {elems, ...} => updateNonfix elems sc
      | DecLocal {dec2, ...} => updateScopeDecs dec2 sc
      | _ => sc
    end
  and updateScopeDecs [] sc = sc
    | updateScopeDecs (d::ds) sc = updateScopeDecs ds (updateScope sc d)

  fun parseRecordLabel () = case token () of
    (start, IntTk) => (start, ident start)
  | tk => (unread tk; parseIdentifier true)

  fun parseAtomic sc pat force = case token () of
    (start, Symbol #"_") => Wild start
  | (start, IntTk) => IntegerConstant (start, ident start)
  | (start, WordTk) => WordConstant (start, ident start)
  | (start, StringTk) => StringConstant (start, ident start)
  | (start, CharTk) => CharConstant (start, ident start)
  | (start, RealTk) => RealConstant (start, ident start)
  | (startOpen, Symbol #"(") => parseParen sc pat startOpen
  | (start, Symbol #"[") => let
    val (elems, right, stop) = parseDelimitedClose [] [] {
      elem = fn () => parseExp sc pat,
      delim = fn (_, Symbol #",") => SOME true | (_, Symbol #";") => SOME false | _ => NONE,
      close = fn (_, Symbol #"]") => SOME true | _ => NONE }
    in List {left = start, elems = elems, right = right, stop = stop} end
  | (start, Symbol #"{") => let
    val (elems, right, stop) = parseDelimitedClose [] [] {
      elem = fn () =>
      case parseRecordLabel () of
        (start, "...") => DotDotDot start
      | id => case parseKeyword "=" NONE of
          SOME eq => LabEq {lab = id, eq = eq, exp = parseExp sc pat}
        | NONE => LabAs {
          id = id,
          ty = Option.map (fn c => {colon = c, ty = parseTy ()}) (parseKeyword ":" NONE),
          aspat = Option.map
            (fn c => {as_ = c, exp = parseExp sc pat}) (parseKeyword "as" NONE) },
      delim = fn (_, Symbol #",") => SOME true | (_, Symbol #";") => SOME false | _ => NONE,
      close = fn (_, Symbol #"}") => SOME true | _ => NONE }
    in Record {left = start, elems = elems, right = right, stop = stop} end
  | (start, IdentTk) => (case ident start of
      "#" => (case parseSymbol #"(" NONE of
        SOME startParen => let
        val res = case token () of
          (kw, IdentTk) => (case ident kw of
            "LINE" => (case parseKeyword "=" NONE of
              SOME eq_ => let
              val line = parseInt (SOME "expected a number")
              val col = Option.map
                (fn comma_ => {comma_ = comma_, col = parseInt (SOME "expected a number")})
                (parseSymbol #"," NONE)
              val (right, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
              val line' = case line of (_, SOME n) => Int.fromString n | _ => NONE
              val _ = case line' of SOME n => let
                val col' = case col of SOME {col = (_, SOME n), ...} => Int.fromString n | _ => NONE
                val e = case col' of
                  SOME c => LineColEvent (start, n-1, c-1)
                | NONE => LineEvent (start, n-1)
                in DArray.push (evts, e) end
              | _ => ()
              in HOLLinePragmaWith {
                hash_ = start, left = startParen, line_ = kw,
                eq_ = eq_, line = line, col = col, right = right, stop = stop }
              end
            | NONE => let
              val (right, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
              in HOLLinePragma {
                hash_ = start, left = startParen, line_ = kw, right = right, stop = stop}
              end)
          | "FILE" => (case parseKeyword "=" NONE of
              SOME eq_ => let
              val file = parseIdent (SOME "expected an identifier")
              val (right, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
              val _ = case file of (_, SOME n) =>
                DArray.push (evts, FileEvent (start, n))
              | _ => ()
              in HOLFilePragmaWith {
                hash_ = start, left = startParen, file_ = kw,
                eq_ = eq_, file = file, right = right, stop = stop }
              end
            | NONE => let
              val (right, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
              in HOLFilePragma {
                hash_ = start, left = startParen, file_ = kw,
                right = right, stop = stop}
              end)
          | s => (
            parseError (kw, !pos) ("unknown pragma '"^s^"'");
            ExpBad {start = start, stop = !pos}))
        | tk => (
          parseError (#1 tk, #1 tk) "expected pragma";
          unread tk;
          ExpBad {start = start, stop = #1 tk})
        in res end
      | NONE => Select {hash = start, label = parseRecordLabel ()})
    | "let" => let
      val (sc', dec) = parseDecs false sc []
      val in_ = parseKeyword "in" (SOME "expected keyword in")
      val (exps, end_, stop) = parseDelimitedClose [] [] {
        elem = fn () => parseExp sc' false,
        delim = fn (_, Symbol #";") => SOME true | _ => NONE,
        close = isKeyword "end" }
      in LetInEnd {let_ = start, dec = dec, in_ = in_, exps = exps, end_ = end_, stop = stop} end
    | "op" => Ident {op_ = SOME start, id = parseIdentifierOrEq true}
    | "raise" => Raise {raise_ = start, exp = parseExp sc false}
    | "if" => IfThenElse {
      if_ = start,
      exp1 = parseExp sc false,
      then_ = parseKeyword "then" (SOME "expected keyword then"),
      exp2 = parseExp sc false,
      else_ = Option.map (fn else_ =>
        {else_ = else_, exp3 = parseExp sc false}) (parseKeyword "else" NONE) }
    | "while" => While {
      while_ = start,
      exp1 = parseExp sc false,
      do_ = parseKeyword "do" (SOME "expected keyword do"),
      exp2 = parseExp sc false }
    | "case" => let
      val exp = parseExp sc false
      val of_ = parseKeyword "of" (SOME "expected keyword of")
      val (elems, stop) = parseArmList sc []
      in Case {case_ = start, exp = exp, of_ = of_, elems = elems, stop = stop} end
    | "fn" => let
      val (elems, stop) = parseArmList sc []
      in Fn {fn_ = start, elems = elems, stop = stop} end
    | _ => (
      unread (start, IdentTk);
      case parseIdentifierOrEq force of
        (start, "") => ExpEmpty start
      | id => Ident {op_ = NONE, id = id}))
  | (start, OpenQuoteTk) => let
    val open_ = ident start
    val (full, s) = case open_ of
      "`" => (false, "`")
    | "``" => (true, "``")
    | "\226\128\152" => (false, "\226\128\153")
    | "\226\128\156" => (true, "\226\128\157")
    | _ => raise Unreachable
    val left = !pos
    fun findColon i =
      case ahead i of
        #":" => SOME (left + i)
      | #" " => findColon (i + 1)
      | #"\t" => findColon (i + 1)
      | _ => NONE
    val type_q = if full then SOME (findColon 0) else NONE
    val (quote, right) = parseQuoteBody sc start left false [s]
    val end_tok = case ident right of
      "" => NONE
    | s => SOME (right, s)
    val r = case type_q of
      NONE => HOLQuote {head = (start, open_), quote = quote, end_tok = end_tok, stop = !pos}
    | SOME type_q => HOLFullQuote {
        head = (start, open_), type_q = type_q, quote = quote, end_tok = end_tok, stop = !pos}
    in r end
  | tk => (
    if force then parseError (#1 tk, #1 tk) "expected an expression" else ();
    unread tk; ExpEmpty (#1 tk))

  and parseExp (sc:scope) pat = parseExp' sc pat true
  and parseExp' (sc:scope) pat force: exp = let
    fun parseInfix pat force = let

      fun peekInfix () = let
        val (start, tk) = token ()
        val r = case tk of
          IdentTk => let
          val s = ident start
          in Option.map (fn d => (s, d)) (Binarymap.peek (sc, s)) end
        | _ => NONE
        in unread (start, tk); (start, r) end

      fun parseApp lhs =
        case peekInfix () of
          (_, SOME _) => lhs
        | (_, NONE) => case parseAtomic sc pat false of
            ExpEmpty _ => lhs
          | rhs => parseApp (App (lhs, rhs))
      val parseApp = fn force => parseApp (parseAtomic sc pat force)

      fun tail prec lhs =
        case peekInfix () of
          (start, SOME (opr, (prec', _))) =>
          (* = must not be parsed in pattern position *)
          if prec' < prec orelse pat andalso opr = "=" then lhs else let
            val _ = token ()
            val rhs = tail2 prec' (parseApp true)
            in tail prec (Infix {left = lhs, id = (start, opr), right = rhs}) end
        | _ => lhs
      and tail2 prec rhs =
        case peekInfix () of
          (_, SOME (opr, (prec', rassoc))) =>
          if prec' + (if rassoc then 1 else 0) <= prec orelse pat andalso opr = "=" then rhs else
            tail2 prec (tail (prec + (if prec' > prec then 1 else 0)) rhs)
        | _ => rhs

      in tail 0 (parseApp force) end

    fun parseTyped lhs =
      case parseKeyword ":" NONE of
        NONE => lhs
      | SOME colon => parseTyped (Typed {exp = lhs, colon = colon, ty = parseTy ()})

    fun parseLayered pat lhs = if not pat then lhs else let
      fun finish {op_, id} ty = case parseKeyword "as" NONE of
          NONE => lhs
        | SOME as_ => Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = parseExp sc true}
      in
        case lhs of
          Ident id => finish id NONE
        | Typed {exp = Ident id, colon, ty} => finish id (SOME {colon = colon, ty = ty})
        | _ => lhs
      end

    fun parseExp1 pat force = parseLayered pat (parseTyped (parseInfix pat force))

    fun parseOrPat force =
      case parseExp1 true force of lhs =>
      case parseKeyword "|" NONE of
        NONE => lhs
      | SOME bar => Or (parseDelimited [lhs] [SOME bar] {
        elem = fn () => parseExp1 true true,
        delim = isKeyword "|" })

    fun parseAndAlso force =
      case parseExp1 false force of left =>
      case parseKeyword "andalso" NONE of
        SOME andalso_ => AndAlso {left = left, andalso_ = andalso_, right = parseAndAlso true}
      | NONE => left

    fun parseOrElse force =
      case parseAndAlso force of left =>
      case parseKeyword "orelse" NONE of
        SOME orelse_ => OrElse {left = left, orelse_ = orelse_, right = parseOrElse true}
      | NONE => left

    in
      if pat then parseOrPat force else
      case parseOrElse force of exp =>
      case parseKeyword "handle" NONE of
        SOME handle_ => let
        val (elems, stop) = parseArmList sc []
        in Handle {exp = exp, handle_ = handle_, elems = elems, stop = stop} end
      | NONE => exp
    end

  and parseParen sc pat startOpen = (case token () of
      (startClose, Symbol #")") => Unit {left = startOpen, right = startClose}
    | tk =>
      case (unread tk; parseExp sc pat) of exp =>
      case token () of
        (startClose, Symbol #")") =>
        Parens {left = startOpen, exp = exp, right = SOME startClose, stop = startClose+1}
      | (startComma, Symbol #",") => let
        val (elems, right, stop) = parseDelimitedClose [exp] [SOME startComma] {
          elem = fn () => parseExp sc pat,
          delim = fn (_, Symbol #",") => SOME true | _ => NONE,
          close = fn (_, Symbol #")") => SOME true | _ => NONE }
        in Tuple {left = startOpen, elems = elems, right = right, stop = stop} end
      | (startSemi, Symbol #";") => let
        val (elems, right, stop) = parseDelimitedClose [exp] [SOME startSemi] {
          elem = fn () => parseExp sc pat,
          delim = fn (_, Symbol #";") => SOME true | _ => NONE,
          close = fn (_, Symbol #")") => SOME true | _ => NONE }
        in Sequence {left = startOpen, elems = elems, right = right, stop = stop} end
      | tk => (
        parseError (#1 tk, #1 tk) "expected closing parenthesis";
        unread tk;
        Parens {left = startOpen, exp = exp, right = NONE, stop = #1 tk}))

  and parseArmList sc acc = case (parseKeyword "|" NONE, acc) of
    (NONE, {exp, ...}::_) => (rev acc, expStop exp)
  | (bar, acc) => let
    val pat = parseExp sc true
    val arrow = parseKeyword "=>" (SOME "expected =>")
    val exp = parseExp sc false
    in parseArmList sc ({bar = bar, pat = pat, arrow = arrow, exp = exp} :: acc) end

  and parseQuoteBody sc start qstart brack (s:string list) = let
    datatype qtoken = EOF | EndTk | StrongEndTk | AntiqIdent | AntiqParen | OpenBrack
    fun checkKW kw i =
      case SOME (String.sub (kw, i)) handle Subscript => NONE of
        SOME c => ahead i = c andalso checkKW kw (i+1)
      | NONE => true

    fun finishHOLString s p = case cur () of
      #"\000" => parseError (p, !pos) "unclosed string literal"
    | #"\"" => (next ();
      if s = "\"" then () else parseError (!pos - 1, !pos) ("expected ["^s^"]"))
    | #"\226" =>
      if checkKW "\226\128\186" 1 then (nextn 3;
        if s = "\226\128\186" then () else parseError (!pos - 3, !pos) ("expected ["^s^"]"))
      else (next (); finishHOLString s p)
    | #"\194" => if checkKW "\194\187" 1 then (nextn 2;
        if s = "\194\187" then () else parseError (!pos - 2, !pos) ("expected ["^s^"]"))
      else (next (); finishHOLString s p)
    | #"\\" => (next ();
      if Char.isSpace (cur ()) then
        (next (); ws (); (case cur () of #"\\" => next () | _ => ()); finishHOLString s p)
      else (next (); finishHOLString s p))
    | _ => (next (); finishHOLString s p)

    fun qtoken cm =
      case cur () of
        #"\000" => (!pos, EOF)
      | #"(" =>
        if ahead 1 = #"*" then (nextn 2; qtoken (cm + 1))
        else (next (); qtoken cm)
      | #"*" =>
        if cm > 0 andalso ahead 1 = #")" then (nextn 2; qtoken (cm - 1))
        else (next (); qtoken cm)
      | #"[" =>
        if cm = 0 andalso brack andalso colZero (!pos) then (!pos, (next (); OpenBrack))
        else (next (); qtoken cm)
      | #"E" =>
        if colZero (!pos) andalso checkKW "End" 1 then (!pos, (nextn 3; StrongEndTk))
        else (next (); qtoken cm)
      | #"T" =>
        if colZero (!pos) andalso checkKW "Termination" 1 then (!pos, (nextn 11; StrongEndTk))
        else (next (); qtoken cm)
      | #"P" =>
        if colZero (!pos) andalso checkKW "Proof" 1 then (!pos, (nextn 5; StrongEndTk))
        else (next (); qtoken cm)
      | #"`" =>
        if ahead 1 = #"`" then (!pos, (nextn 2; EndTk))
        else (!pos, (next (); EndTk))
      | #"\"" =>
        if cm = 0 then (next (); finishHOLString "\"" (!pos - 1); qtoken cm) else
        (next (); qtoken cm)
      | #"\194" =>
        if cm = 0 andalso checkKW "\194\171" 1 then
          (nextn 2; finishHOLString "\194\187" (!pos - 2); qtoken cm)
        else (next (); qtoken cm)
      | #"\226" =>
        if checkKW "\226\128\157" 1 then (!pos, (nextn 3; EndTk)) else
        if checkKW "\226\128\153" 1 then (!pos, (nextn 3; EndTk)) else
        if cm = 0 andalso checkKW "\226\128\185" 1 then
          (nextn 3; finishHOLString "\226\128\186" (!pos - 3); qtoken cm)
        else (next (); qtoken cm)
      | #"^" => (next ();
        if cm = 0 then
          case cur () of
            #"^" => let
            fun go () = (next (); if cur () = #"^" then go () else ())
            in go (); qtoken cm end
          | #"(" => (!pos - 1, (next (); AntiqParen))
          | c =>
            if Char.isAlpha c then
              (!pos - 1, (takeWhile isIdRest; AntiqIdent))
            else qtoken cm
        else qtoken cm)
      | _ => (next (); qtoken cm)

    fun expected () = "expected [" ^ String.concatWith ", " s ^ "]"

    fun push i p acc = if i = p andalso not (null acc) then acc else
      QuoteLiteral (i, DString.extract (body, i, SOME (p - i))) :: acc

    fun go i acc =
      case qtoken 0 of
        (p, EOF) => (parseError (start, p) "unclosed quotation"; (rev (push i p acc), p))
      | (p, StrongEndTk) => (
        if mem (ident p) s then () else parseError (start, p) (expected ());
        (rev (push i p acc), p))
      | (p, EndTk) => if mem (ident p) s then (rev (push i p acc), p) else go i acc
      | (p, AntiqIdent) => let
        val acc = push i p acc
        val exp = case identKind (p + 1) of
          (s, Regular) => Ident {op_ = NONE, id = (p+1, s)}
        | _ => (parseError (p+1, !pos) "expected identifier"; ExpBad {start = p+1, stop = !pos})
        in go (!pos) (QuoteAntiq {caret_ = p, exp = exp} :: acc) end
      | (p, AntiqParen) => let
        val acc = push i p acc
        val e = parseParen sc false (p+1)
        val stop = case e of
          Unit {right, ...} => right+1
        | Parens {stop, ...} => stop
        | Tuple {stop, ...} => stop
        | Sequence {stop, ...} => stop
        | _ => raise Unreachable
        in go stop (QuoteAntiq {caret_ = p, exp = e} :: acc) end
      | (p, OpenBrack) => let
        val acc = push i p acc
        val _ = ws ()
        val label =
          if checkKW "/\\" 0 then
            SOME (HOLConjLabel (!pos, (nextn 2; ident (!pos - 2))))
          else if checkKW "\226\136\167" 0 then
            SOME (HOLConjLabel (!pos, (nextn 3; ident (!pos - 3))))
          else if cur () = #"~" andalso isIdRest (ahead 1) then
            case !pos + 1 of start => SOME (HOLLabel {
              tilde_ = SOME (!pos),
              id = (start, (nextn 2; takeWhile isIdRest; ident start)) })
          else if Char.isAlpha (cur ()) then
            case !pos of start => SOME (HOLLabel {
              tilde_ = NONE,
              id = (start, (nextn 2; takeWhile isIdRest; ident start)) })
          else NONE
        val attrs = case parseSymbol #"[" NONE of
          NONE => NONE
        | SOME left => let
          val (attrs, right, stop) = parseDelimitedClose [] [] {
            elem = fn () => parseIdentifier false,
            delim = fn (_, Symbol #",") => SOME true | _ => NONE,
            close = fn (_, Symbol #"]") => SOME true | _ => NONE }
          in SOME {left = left, attrs = attrs, right = right, stop = stop} end
        val colon = parseKeyword ":" NONE
        val (right, stop) = parseStop (parseSymbol #"]") 1 "expected ']'"
        val _ = pos := stop
        val r = DefinitionLabel {
          left = p, label = label, attrs = attrs,
          colon = colon, right = right, stop = stop }
        in go stop (r :: acc) end
    in go qstart [] end

  and parseDec (inSig: bool) (sc: scope): (scope * dec) option = let

    fun parseInfixElems acc =
      case parseIdentifierOrEq false of
        (_, "") => rev acc
      | id => parseInfixElems (id :: acc)

    fun parseFValBinds acc = case (parseKeyword "|" NONE, acc) of
      (NONE, _::_) => rev acc
    | (bar, acc) => let
      val pat = parseExp sc true
      val eq = parseKeyword "=" (SOME "expected =")
      val _ = case eq of NONE => parseKeyword "=>" NONE | _ => NONE
      in parseFValBinds ({bar = bar, pat = pat, eq = eq, exp = parseExp sc false} :: acc) end

    fun parseDatBind () = (
      parseDelimited [] [] {
        elem = fn () => let
          val tyvars = parseTyVars ()
          val tycon = parseIdentifier true
          val eq = parseKeyword "=" (SOME "expected '='")
          fun go acc = case (parseKeyword "|" NONE, acc) of
            (NONE, _::_) => rev acc
          | (bar, acc) =>
            go ({
              bar = bar,
              op_ = parseKeyword "op" NONE,
              id = parseIdentifier true,
              arg = Option.map (fn of_ => {of_ = of_, ty = parseTy ()}) (parseKeyword "of" NONE)
            } :: acc)
          val rhs = case eq of NONE => DatvalElems [] | _ =>
            case parseKeyword "datatype" NONE of
              SOME kw => DatvalDatatype {datatype_ = kw, id = parseIdentifier true}
            | NONE => DatvalElems (go [])
          in {tyvars = tyvars, tycon = tycon, eq = eq, rhs = rhs} end,
        delim = isKeyword "and" },
      Option.map (fn withtype_ => {
          withtype_ = withtype_,
          tybind = parseDelimited [] [] {elem = parseTyBind, delim = isKeyword "and"}})
        (parseKeyword "withtype" NONE))

    fun parseInductive start co = let
      val id = parseIdentifierOrKw true
      val (colon, qstart) = parseStop (parseKeyword ":") 1 "expected ':'"
      val (qbody, right) = parseQuoteBody sc qstart qstart true ["End"]
      val (end_, stop) = if ident right = "End" then (SOME right, right+3) else (NONE, right)
      in HOLInductiveDecl {
        co = co, inductive_ = start, id = id, colon = colon,
        quote = qbody, end_ = end_, stop = stop }
      end

    fun parseHolType start overload = let
      val id = case token () of
        (start, StringTk) => QuotedId (start, ident start)
      | tk => (unread tk; UnquotedId (parseIdentifierOrKw true))
      val attrs = parseAttrs (fn () => parseIdentifierOrKw true)
      val bind = Option.map (fn eq => {eq = eq, exp = parseExp sc false})
        (parseKeyword "=" NONE)
      in HOLType {overload = overload, type_ = start, id = id, attrs = attrs, bind = bind} end

    fun parseHolTheorem start triv = let
      val id = parseIdentifier true
      val attrs = parseAttrs parseKVals
      val r = case parseKeyword ":" NONE of
        SOME colon => let
        val qstart = colon+1
        val (qbody, right) = parseQuoteBody sc qstart qstart false ["Proof"]
        val proof_ = if ident right <> "Proof" then NONE else
          SOME {proof_ = right, attrs = parseAttrs parseKVals}
        val tac = parseExp sc false
        val (qed_, stop) = parseStop (parseHolKeyword "QED") 3 "expected 'QED'"
        val _ = case qed_ of NONE => parseHolKeyword "End" NONE | _ => NONE
        in HOLTheoremDecl {
          triv = triv, theorem_ = start, id = id, attrs = attrs, colon = colon,
          quote = qbody, proof_ = proof_, tac = tac, qed_ = qed_, stop = stop }
        end
      | NONE => HOLSimpleThm {
        triv = triv, theorem_ = start, id = id, attrs = attrs,
        bind = Option.map (fn eq => {eq = eq, exp = parseExp sc false}) (parseKeyword "=" NONE) }
      in r end

    val dec = case token () of
      (start, Symbol #";") => SOME (sc, DecSemi start)
    | (start, IdentTk) => (case identKind start of
        ("val", _) => SOME (sc, DecVal {
        val_ = start,
        tyvars = parseTyVars (),
        elems = parseDelimited [] [] {
          elem = fn () => {
            rec_ = parseKeyword "rec" NONE,
            pat = parseExp sc true,
            eq = Option.map (fn eq => {eq = eq, exp = parseExp sc false})
              (parseKeyword "=" NONE) },
          delim = isKeyword "and" } })
      | ("type", _) => SOME (sc, DecType {
        type_ = start,
        tybind = parseDelimited [] [] {elem = parseTyBind, delim = isKeyword "and"} })
      | ("eqtype", _) => SOME (sc, DecEqtype {
        eqtype_ = start,
        tybind = parseDelimited [] [] {elem = parseTyBind, delim = isKeyword "and"} })
      | ("infix", _) => let
        val prec = case parseInt NONE of (_, NONE) => NONE | (start, SOME n) => SOME (start, n)
        val elems = parseInfixElems []
        val dec = DecInfix {infix_ = start, prec = prec, elems = elems}
        in SOME (updateScope sc dec, dec) end
      | ("infixr", _) => let
        val prec = case parseInt NONE of (_, NONE) => NONE | (start, SOME n) => SOME (start, n)
        val elems = parseInfixElems []
        val dec = DecInfixr {infixr_ = start, prec = prec, elems = elems}
        in SOME (updateScope sc dec, dec) end
      | ("nonfix", _) => let
        val elems = parseInfixElems []
        val dec = DecNonfix {nonfix_ = start, elems = elems}
        in SOME (updateScope sc dec, dec) end
      | ("fun", _) => SOME (sc, DecFun {
        fun_ = start,
        tyvars = parseTyVars (),
        fvalbind = parseDelimited [] []
          {elem = fn () => parseFValBinds [], delim = isKeyword "and"} })
      | ("exception", _) => SOME (sc, DecException {
        exception_ = start,
        elems = parseDelimited [] [] {
          elem = fn () => let
            val op_ = parseKeyword "op" NONE
            val id = parseIdentifier true
            val r = case parseKeyword "=" NONE of
              SOME eq => ExnReplicate {op_ = op_, id = id, eq = eq, tgt = parseIdentifier true}
            | NONE => ExnNew {
              op_ = op_, id = id,
              arg = Option.map (fn of_ => {of_ = of_, ty = parseTy ()}) (parseKeyword "of" NONE) }
            in r end,
          delim = isKeyword "and" } })
      | ("local", _) => let
        val (sc1, dec1) = parseDecs inSig sc []
        val in_ = parseKeyword "in" (SOME "expected keyword 'in'")
        val (_, dec2) = parseDecs inSig sc1 []
        val sc' = updateScopeDecs dec2 sc
        val (end_, stop) = parseStop (parseKeyword "end") 3 "expected keyword 'end'"
        in SOME (sc', DecLocal {
          local_ = start, dec1 = dec1, in_ = in_,
          dec2 = dec2, end_ = end_, stop = stop})
        end
      | ("datatype", _) => let
        val (datbind, wt) = parseDatBind ()
        in SOME (sc, DecDatatype {datatype_ = start, datbind = datbind, withtype_ = wt}) end
      | ("open", _) => SOME (sc, DecOpen {open_ = start, elems = parseIdentifiers []})
      | ("include", _) => SOME (sc, DecInclude {
        include_ = start,
        sigexps = case parseSigExp sc of
          SigIdent id => map SigIdent (parseIdentifiers [id])
        | e => [e] })
      | ("abstype", _) => let
        val (datbind, wt) = parseDatBind ()
        val (with_, stop) = parseStop (parseKeyword "with") 4 "expected keyword 'with'"
        val (dec, (end_, stop)) = case with_ of NONE => ([], (NONE, stop)) | _ =>
          (#2 (parseDecs inSig sc []), parseStop (parseKeyword "end") 3 "expected keyword 'end'")
        in SOME (sc, DecAbstype {
          abstype_ = start, datbind = datbind, withtype_ = wt,
          with_ = with_, dec = dec, end_ = end_, stop = stop})
        end
      | ("structure", _) => SOME (sc, DecStructure {
        structure_ = start,
        elems = parseDelimited [] [] {
          elem = fn () => {
            id = parseIdentifier true,
            constraint = parseStructKind sc,
            bind = Option.map (fn eq => {eq = eq, strexp = parseStrExp sc})
              (parseKeyword "=" NONE) },
          delim = isKeyword "and" } })
      | ("signature", _) => SOME (sc, DecSignature {
        signature_ = start,
        elems = parseDelimited [] [] {
          elem = fn () => {
            id = parseIdentifier true,
            bind = Option.map (fn eq => {eq = eq, sigexp = parseSigExp sc})
              (parseKeyword "=" (SOME "expected '='")) },
          delim = isKeyword "and" } })
      | ("sharing", _) => SOME (sc, Sharing {
        sharing_ = start,
        type_ = parseKeyword "type" NONE,
        elems = parseDelimited [] [] {
          elem = fn () => parseIdentifier true,
          delim = isKeyword "=" } })
      | ("functor", _) => SOME (sc, DecFunctor {
        functor_ = start,
        elems = parseDelimited [] [] {
          elem = fn () => {
            id = parseIdentifier true,
            lparen = parseSymbol #"(" (SOME "expected '('"),
            funarg = case parseIdentifier false of
              (_, "") => ArgSpec (#2 (parseDecs true sc []))
            | id => ArgIdent {
              strid = id,
              ty = Option.map (fn colon => {colon = colon, sigexp = parseSigExp sc})
                (parseKeyword ":" (SOME "expected ':'")) },
            rparen = parseSymbol #")" (SOME "expected ')'"),
            constraint = parseStructKind sc,
            bind = Option.map (fn eq => {eq = eq, strexp = parseStrExp sc})
              (parseKeyword "=" (SOME "expected '='")) },
          delim = isKeyword "and" } })
      | ("Definition", HolKeyword) => SOME (sc, let
        val id = parseIdentifier true
        val attrs = parseAttrs parseKVals
        val (colon, qstart) = parseStop (parseKeyword ":") 1 "expected ':'"
        val (qbody, right) = parseQuoteBody sc qstart qstart false ["End", "Termination"]
        val (term, (end_, stop)) = if ident right = "Termination" then
          (SOME {termination_ = right, tac = parseExp sc false},
           (parseStop (parseHolKeyword "End") 3 "expected 'End'"))
        else (NONE, if ident right = "End" then (SOME right, right+3) else (NONE, right))
        val _ = case end_ of NONE => parseHolKeyword "QED" NONE | _ => NONE
        in HOLDefinition {
          definition_ = start, id = id, attrs = attrs, colon = colon,
          quote = qbody, termination = term, end_ = end_, stop = stop }
        end)
      | ("Datatype", HolKeyword) => SOME (sc, let
        val (colon, qstart) = parseStop (parseKeyword ":") 1 "expected ':'"
        val (qbody, right) = parseQuoteBody sc qstart qstart true ["End"]
        val (end_, stop) = if ident right = "End" then (SOME right, right+3) else (NONE, right)
        val _ = case end_ of NONE => parseHolKeyword "QED" NONE | _ => NONE
        in HOLDatatype {
          datatype_ = start, colon = colon,
          quote = qbody, end_ = end_, stop = stop }
        end)
      | ("Quote", HolKeyword) => SOME (sc, let
        val id = parseIdentifier true
        val bind = Option.map (fn eq => {eq = eq, exp = parseAtomic sc false true})
          (parseKeyword "=" NONE)
        val (colon, qstart) = parseStop (parseKeyword ":") 1 "expected ':'"
        val (qbody, right) = parseQuoteBody sc qstart qstart false ["End"]
        val (end_, stop) = if ident right = "End" then (SOME right, right+3) else (NONE, right)
        val _ = case end_ of NONE => parseHolKeyword "QED" NONE | _ => NONE
        in HOLQuoteDecl {
          quote_ = start, id = id, bind = bind, colon = colon,
          quote = qbody, end_ = end_, stop = stop }
        end)
      | ("Inductive", HolKeyword) => SOME (sc, parseInductive start false)
      | ("CoInductive", HolKeyword) => SOME (sc, parseInductive start true)
      | ("Type", HolKeyword) => SOME (sc, parseHolType start false)
      | ("Overload", HolKeyword) => SOME (sc, parseHolType start true)
      | ("Theorem", HolKeyword) => SOME (sc, parseHolTheorem start false)
      | ("Triviality", HolKeyword) => SOME (sc, parseHolTheorem start true)
      | ("Theory", HolKeyword) => SOME (sc, let
        val id = parseIdentifier true
        val attrs = parseAttrs parseKVals
        fun parseHeader acc =
          case parseIdentifier false of
            (_, "") => rev acc
          | id => parseHeader ({id = id, attrs = parseAttrs parseKVals} :: acc)
        fun parseHeaders acc =
          case token () of
            tk as (start, IdentTk) => (case identKind start of
              ("Ancestors", HolKeyword) => parseHeaders (HOLAncestors
              {ancestors_ = start, attrs = parseAttrs parseKVals, elems = parseHeader []} :: acc)
            | ("Libs", HolKeyword) => parseHeaders (HOLLibs
              {libs_ = start, attrs = parseAttrs parseKVals, elems = parseHeader []} :: acc)
            | _ => (unread tk; rev acc))
          | tk => (unread tk; rev acc)
        in HOLTheory {theory_ = start, id = id, attrs = attrs, elems = parseHeaders []} end)
      | ("Resume", HolKeyword) => SOME (sc, let
        val id = parseIdentifier true
        val attrs = parseAttrs parseKVals
        val colon = parseKeyword ":" (SOME "expected a colon")
        val tac = parseExp sc false
        val (qed_, stop) = parseStop (parseHolKeyword "QED") 3 "expected 'QED'"
        val _ = case qed_ of NONE => parseHolKeyword "End" NONE | _ => NONE
        in HOLResume {
          resume_ = start, id = id, attrs = attrs, colon = colon,
          tac = tac, qed_ = qed_, stop = stop }
        end)
      | ("Finalise", HolKeyword) => SOME (sc, let
        val id = parseIdentifier true
        val attrs = parseAttrs parseKVals
        val stop = case attrs of SOME {stop, ...} => stop | NONE => idStop id
        in HOLFinalise {finalise_ = start, id = id, attrs = attrs, stop = stop} end)
      | _ => (unread (start, IdentTk); NONE))
    | tk => (unread tk; NONE)
    in
      case dec of SOME dec => SOME dec | NONE => (
        case parseExp' sc false false of
          ExpEmpty _ => (case token () of
              tk as (start, IdentTk) => let
                val s = ident start
                in if s = "in" orelse s = "end" then (unread tk; NONE)
                   else (
                     parseError (start, !pos) "bad declaration";
                     SOME (sc, DecBad {start = start, stop = !pos})) end
            | tk as (start, Symbol #")") => (unread tk; NONE)
            | tk as (start, EOF) => (unread tk; NONE)
            | (start, _) => (
                parseError (start, !pos) "bad declaration";
                SOME (sc, DecBad {start = start, stop = !pos})))
        | e => SOME (sc, DecExp e))
    end

  and parseDecs (inSig: bool) sc (acc: dec list): scope * dec list =
    case parseDec inSig sc of
      NONE => (sc, rev acc)
    | SOME (sc, d) => parseDecs inSig sc (d :: acc)

  and parseStructKind sc =
    case parseKeyword ":" NONE of
      SOME colon => SOME {colon = (colon, Colon), sigexp = parseSigExp sc}
    | NONE => case parseKeyword ":>" NONE of
        SOME colongt => SOME {colon = (colongt, ColonGt), sigexp = parseSigExp sc}
      | NONE => NONE

  and parseSigExp sc = let
    val lhs = case parseKeyword "sig" NONE of
      SOME sig_ => let
      val (_, spec) = parseDecs true sc []
      val (end_, stop) = parseStop (parseKeyword "end") 3 "expected keyword 'end'"
      in Spec {sig_ = sig_, spec = spec, end_ = end_, stop = stop} end
    | NONE => SigIdent (parseIdentifier true)
    fun rhs lhs =
      case parseKeyword "where" NONE of
        SOME where_ => let
        val elems = parseDelimited [] [] {
          elem = fn () => {
            type_ = parseKeyword "type" (SOME "expected 'type'"),
            tybind = parseTyBind () },
          delim = isKeyword "and" }
        in rhs (WhereType {sigexp = lhs, where_ = where_, elems = elems}) end
      | NONE => lhs
    in rhs lhs end

  and parseStrExp sc = let
    val lhs = case token () of
      (start, IdentTk) => (case identKind start of
        ("struct", _) => let
        val (_, dec) = parseDecs true sc []
        val (end_, stop) = parseStop (parseKeyword "end") 3 "expected keyword 'end'"
        in StrStruct {struct_ = start, strdec = dec, end_ = end_, stop = stop} end
      | ("let", _) => let
        val (_, dec) = parseDecs true sc []
        val in_ = parseKeyword "in" (SOME "expected keyword in")
        val strexp = parseStrExp sc
        val (end_, stop) = parseStop (parseKeyword "end") 3 "expected keyword 'end'"
        in StrLetInEnd {
          let_ = start, strdec = dec, in_ = in_,
          strexp = strexp, end_ = end_, stop = stop} end
      | (id, Regular) => (case parseSymbol #"(" NONE of
          NONE => StrIdent (start, id)
        | SOME lparen =>
          if
            case case token () of tk => (unread tk; tk) of
              (start, IdentTk) => (case identKind start of
                ("let", _) => true
              | ("struct", _) => true
              | (_, Regular) => true
              | _ => false)
            | _ => false
          then let
            val strexp = parseStrExp sc
            val (rparen, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
            in FunAppExp {
              funid = (start, id), lparen = lparen,
              strexp = strexp, rparen = rparen, stop = stop}
            end
          else let
            val (_, dec) = parseDecs true sc []
            val (rparen, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
            in FunAppDec {
              funid = (start, id), lparen = lparen,
              strdec = dec, rparen = rparen, stop = stop}
            end)
      | _ => (
        parseError (start, start) "expected struct expression";
        unread (start, IdentTk); StrIdent (start, "")))
    | tk => (
      parseError (#1 tk, #1 tk) "expected struct expression";
      unread tk; StrIdent (#1 tk, ""))
    fun rhs lhs = case parseStructKind sc of
      SOME kind => rhs (StrConstraint {strexp = lhs, kind = kind})
    | NONE => lhs
    in rhs lhs end

  fun go (sc: scope) = let
    val sc = ref sc
    val isThy = ref NONE
    val noSigDocs = ref false
    (* At the end of a theory we need to generate the declaration corresponding
       to an export_theory call. Using parseDecRef, we ensure this only happens
       once. *)
    val parseDecRef = ref (fn () => NONE)
    fun finishTheory () = case !isThy of
        NONE => NONE
      | SOME theory_ => (
        parseDecRef := (fn () => NONE);
        SOME (HOLTheoryEnd {
          theory_ = theory_,
          stop = DString.size body,
          noSigDocs = !noSigDocs}))
    val _ = parseDecRef := (fn () =>
      case parseDec false (!sc) of
        NONE => (case token () of
            tk as (start, EOF) => (unread tk; finishTheory ())
          | (start, _) => (
              parseError (start, !pos) "bad declaration";
              SOME (DecBad {start = start, stop = !pos})))
      | SOME (sc', d) => (
        sc := sc';
        case d of
          HOLTheory {theory_, attrs, ...} => (
            isThy := SOME theory_;
            app (fn {key = (_, "no_sig_docs"), bind = NONE} => noSigDocs := true | _ => ())
              (case attrs of NONE => [] | SOME v => #args (#attrs v)))
        | _ => ();
        SOME d))
    in {parseDec = fn () => !parseDecRef (), getScope = fn () => !sc, body = body, events = events} end
  in go end

end;
