structure Parser = struct
open Ast

exception Unreachable
type scope = (string, int * bool) Binarymap.dict
type result = {getScope: unit -> scope, parseDec: unit -> dec option}
fun parseSML file body parseError: scope -> result = let
  val pos = ref 0
  val fileRef = ref file
  fun cur () = String.sub (body, !pos) handle Subscript => #"\000"
  fun ahead i = String.sub (body, !pos + i) handle Subscript => #"\000"
  fun next () = pos := !pos + 1
  fun nextn i = pos := !pos + i
  fun takeWhile f = if f (cur ()) then (next (); takeWhile f) else ()
  fun ws () = takeWhile Char.isSpace
  fun isIdRest c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"
  val isIdSym = Char.contains "!%&$#+-/:<=>?@\\~^|*"
  fun colZero start = start = 0 orelse String.sub (body, start - 1) = #"\n"
  val _ = ws ()

  val posLineCol = ref (0, 0, 0)
  fun updatePosLineCol p = let
    val (pos, line, col) = !posLineCol
    fun countLines i line last =
      if i = p then posLineCol := (p, line, p - last) else
      if String.sub (body, i) = #"\n" then countLines (i+1) (line+1) (i+1) else
      countLines (i+1) line last
    fun firstLine i =
      if i = p then posLineCol := (p, line, col + p - pos) else
      if String.sub (body, i) = #"\n" then countLines (i+1) (line+1) (i+1) else
      firstLine (i+1)
    in firstLine pos end

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

  exception Todo
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
  fun ident start = String.substring (body, start, !pos - start)

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
        SOME true => ({args = rev args, delims = rev delims}, SOME (#1 tk), !pos)
      | SOME false => (
        parseError (#1 tk, !pos) "unexpected close token";
        ({args = rev args, delims = rev delims}, NONE, !pos))
      | NONE => (unread tk; case elem () of e => parseDelimitedClose2 (e :: args) delims f)
  and parseDelimitedClose2 args delims (f as {delim, close, ...}) =
    case token () of tk =>
      case close tk of
        SOME true => ({args = rev args, delims = rev delims}, SOME (#1 tk), !pos)
      | SOME false => (
        parseError (#1 tk, !pos) "unexpected close token";
        ({args = rev args, delims = rev delims}, NONE, !pos))
      | NONE => case delim tk of
          SOME true => parseDelimitedClose args (SOME (#1 tk) :: delims) f
        | SOME false => (
          parseError (#1 tk, !pos) "unexpected delimiter";
          parseDelimitedClose args (NONE :: delims) f)
        | NONE => (
          parseError (#1 tk, !pos) "expected close delimiter";
          unread tk; ({args = rev args, delims = rev delims}, NONE, #1 tk))

  fun parseDelimited args delims (f as {elem, delim}) =
    case (elem (), token ()) of (e, tk) =>
      case delim tk of
        SOME true => parseDelimited (e :: args) (SOME (#1 tk) :: delims) f
      | SOME false => (
        parseError (#1 tk, !pos) "unexpected delimiter";
        parseDelimited (e :: args) (NONE :: delims) f)
      | NONE => (unread tk; {args = rev (e :: args), delims = rev delims})

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
          {args = [ty], delims = []} =>
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
          in {lab = lab, colon = colon, ty = parseTy false} end,
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

  fun updateScope sc = let
    fun updateInfix right prec elems sc =
      case case prec of SOME (_, prec) => Int.fromString prec | _ => NONE of
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
              val _ = updatePosLineCol start
              val _ = case case line of (_, SOME n) => Int.fromString n | _ => NONE of
                SOME n => posLineCol := (fn (a,_,c) => (a,n,c)) (!posLineCol)
              | _ => ()
              val col' = case col of SOME {col = (_, SOME n), ...} => Int.fromString n | _ => NONE
              val _ = case col' of
                SOME n => posLineCol := (fn (a,b,_) => (a,b,n)) (!posLineCol)
              | _ => ()
              in HOLLinePragmaWith {
                hash_ = start, left = startParen, line_ = kw,
                eq_ = eq_, line = line, col = col, right = right, stop = stop }
              end
            | NONE => let
              val (right, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
              val (_, line, _) = (updatePosLineCol start; !posLineCol)
              in HOLLinePragma {
                hash_ = start, left = startParen, line_ = kw,
                right = right, stop = stop, value = line}
              end)
          | "FILE" => (case parseKeyword "=" NONE of
              SOME eq_ => let
              val file = parseIdent (SOME "expected an identifier")
              val (right, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
              val _ = case file of (_, SOME n) => fileRef := n | _ => ()
              in HOLFilePragmaWith {
                hash_ = start, left = startParen, file_ = kw,
                eq_ = eq_, file = file, right = right, stop = stop }
              end
            | NONE => let
              val (right, stop) = parseStop (parseSymbol #")") 1 "expected ')'"
              in HOLFilePragma {
                hash_ = start, left = startParen, file_ = kw,
                right = right, stop = stop, value = !fileRef}
              end)
          | s => (
            parseError (kw, !pos) ("unknown pragma '"^s^"'");
            BadExp {start = start, stop = !pos}))
        | tk => (
          parseError (#1 tk, #1 tk) "expected pragma";
          unread tk;
          BadExp {start = start, stop = #1 tk})
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
    | _ => (
      unread (start, IdentTk);
      case parseIdentifierOrEq force of
        (start, "") => EmptyExp start
      | id => Ident {op_ = NONE, id = id}))
  | (start, OpenQuoteTk) => let
    val open_ = ident start
    val (full, s) = case open_ of
      "`" => (false, "`")
    | "``" => (true, "``")
    | "\226\128\152" => (false, "\226\128\153")
    | "\226\128\156" => (false, "\226\128\157")
    | _ => raise Unreachable
    fun findColon i =
      case ahead i of
        #":" => SOME (!pos + i)
      | #" " => findColon (i + 1)
      | #"\t" => findColon (i + 1)
      | _ => NONE
    val left = !pos
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
    unread tk; EmptyExp (#1 tk))

  and parseExp sc pat = parseExp' sc pat true
  and parseExp' sc pat force: exp = let
    fun parseArmList acc = case (parseKeyword "|" NONE, acc) of
      (NONE, _::_) => rev acc
    | (bar, acc) => let
      val pat = parseExp sc true
      val arrow = parseKeyword "=>" (SOME "expected =>")
      val exp = parseExp sc false
      in parseArmList ({bar = bar, pat = pat, arrow = arrow, exp = exp} :: acc) end

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
            EmptyExp _ => lhs
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
        | SOME as_ => parseLayered pat
          (Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = parseExp sc true})
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

    fun parseKwExp force =
      case token () of tk as (start, _) =>
      case case #2 tk of IdentTk => ident start | _ => "" of
        "raise" => Raise {raise_ = start, exp = parseExp sc false}
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
      | "case" => Case {
        case_ = start,
        exp = parseExp sc false,
        of_ = parseKeyword "of" (SOME "expected keyword of"),
        elems = parseArmList [] }
      | "fn" => Fn {fn_ = start, elems = parseArmList []}
      | _ => (unread tk; parseExp1 false force)

    fun parseAndAlso force =
      case parseKwExp force of left =>
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
        SOME handle_ => Handle {exp = exp, handle_ = handle_, elems = parseArmList []}
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
              (!pos - 1, (takeWhile isIdRest; finishId (); AntiqIdent))
            else qtoken cm
        else qtoken cm)
      | _ => (next (); qtoken cm)

    fun expected () = "expected [" ^ String.concatWith ", " s ^ "]"

    fun push i p acc = if i = p then acc else let
      val (_, line, col) = (updatePosLineCol start; !posLineCol)
      val value = Substring.substring (body, i, p - i)
      in QuoteLiteral {line = line, col = col, value = value} :: acc end

    fun go i acc =
      case qtoken 0 of
        (p, EOF) => (parseError (start, p) "unclosed quotation"; (rev (push i p acc), p))
      | (p, StrongEndTk) => (
        if mem (ident p) s then () else parseError (start, p) (expected ());
        (rev acc, p))
      | (p, EndTk) => if mem (ident p) s then (rev acc, p) else go i acc
      | (p, AntiqIdent) => let
        val exp = case identKind (p + 1) of
          (s, Regular) => Ident {op_ = NONE, id = (p+1, s)}
        | _ => (parseError (p+1, !pos) "expected identifier"; BadExp {start = p+1, stop = !pos})
        in go (!pos) (QuoteAntiq {caret_ = p, exp = exp} :: push i p acc) end
      | (p, AntiqParen) => let
        val e = parseParen sc false (p+1)
        val stop = case e of
          Unit {right, ...} => right+1
        | Parens {stop, ...} => stop
        | Tuple {stop, ...} => stop
        | Sequence {stop, ...} => stop
        | _ => raise Unreachable
        in go stop (QuoteAntiq {caret_ = p, exp = e} :: push i p acc) end
      | (p, OpenBrack) => let
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
        val args = case parseSymbol #"[" NONE of
          NONE => NONE
        | SOME left => let
          val (ids, right, stop) = parseDelimitedClose [] [] {
            elem = fn () => parseIdentifier false,
            delim = fn (_, Symbol #",") => SOME true | _ => NONE,
            close = fn (_, Symbol #"]") => SOME true | _ => NONE }
          in SOME {left = left, ids = ids, right = right, stop = stop} end
        val colon = parseKeyword ":" NONE
        val (right, stop) = parseStop (parseSymbol #"]") 1 "expected ']'"
        val _ = pos := stop
        val r = DefinitionLabel {
          left = p, label = label, args = args,
          colon = colon, right = right, stop = stop }
        in go stop (r :: push i p acc) end
    in go qstart [] end

  and parseDec (inSig: bool) sc: (scope * dec) option = let

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
              ("Ancestors", HolKeyword) =>
              parseHeaders (HOLAncestors {ancestors_ = start, elems = parseHeader []} :: acc)
            | ("Libs", HolKeyword) =>
              parseHeaders (HOLLibs {libs_ = start, elems = parseHeader []} :: acc)
            | _ => (unread tk; rev acc))
          | tk => (unread tk; rev acc)
        in HOLTheory {theory_ = start, id = id, attrs = attrs, elems = parseHeaders []} end)
      | _ => (unread (start, IdentTk); NONE))
    | tk => (unread tk; NONE)
    in
      case dec of SOME dec => SOME dec | _ =>
      case parseExp' sc false false of EmptyExp _ => NONE | e => SOME (sc, DecExp e)
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
    val parseDec = fn () => case parseDec false (!sc) of
        NONE => NONE
      | SOME (sc', d) => (sc := sc'; SOME d)
    in {parseDec = parseDec, getScope = fn () => !sc} end
  in go end

end

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
  val {parseDec, ...} = ParserNew.parseSML file body
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
open AstNew

exception Todo

fun mkIdent s = Ident {op_ = NONE, id = s}

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

fun mkString (p, s) = StringConstant (p, encodeStr (Substring.full s) "\"" "\"")

fun mkList (p, ls) = List {left = p, elems = {args = ls, delims = []}, right = NONE, stop = p}

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
          NONE => LabEq {lab = id, eq = #1 id, exp = typed (mkIdent id) ty}
        | SOME {as_, exp} => LabEq {lab = id, eq = as_, exp = typed exp ty}
      in reord ls dot (lab :: acc) end
  val elems = {args = reord args NONE [], delims = delims}
  in {left = left, elems = elems, right = right, stop = stop} end

fun mkLocPragma line col s =
  concat [" (*#loc ", Int.toString (line + 1), " ", Int.toString (col + 1), "*)", s]

fun valPat pos pat e = let
  val s = {rec_ = NONE, pat = pat, eq = SOME {eq = pos, exp = e}}
  in DecVal {val_ = pos, tyvars = Empty, elems = {args = [s], delims = []}} end

fun valWild pos = valPat pos (Wild pos)

fun mapArms g f1 f2 elems = let
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
    | onPat e f = f (g e)

  and onRow (LabEq {lab, eq, exp}) f =
      onPat exp (fn exp => f (LabEq {lab = lab, eq = eq, exp = exp}))
    | onRow (LabAs {id, ty, aspat = SOME {as_, exp}}) f =
      onPat exp (fn exp => f (LabAs {id = id, ty = ty, aspat = SOME {as_ = as_, exp = exp}}))
    | onRow e f = f e

  and orList [] _ = (fn x => x)
    | orList (e :: es) f = onPat e f o orList es f

  fun arms [] = (fn x => x)
    | arms (x :: ls) = onPat (f1 x) (fn pat => fn l => f2 (x, pat) :: l) o arms ls
  in arms elems [] end

exception HasOrPat
fun mapDelim f {args, delims} = {args = map f args, delims = delims}
fun expandExp true (e as Wild _) = e
  | expandExp false (Wild p) =
    Raise {raise_ = p, exp = App (mkIdent (p, "Fail"), mkString (p, "_"))}
  | expandExp _ (e as IntegerConstant _) = e
  | expandExp _ (e as WordConstant _) = e
  | expandExp _ (StringConstant (p, s)) = mkString (p, decodeStr s 1 (size s - 1))
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
    LetInEnd {let_ = let_, dec = expandDecs dec [], in_ = in_,
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
    in App (mkIdent id, expandQuote (#1 head) stop quote) end
  | expandExp _ (HOLQuote {head, quote, stop, ...}) = expandQuote (#1 head) stop quote
  | expandExp _ (HOLLinePragma {hash_, value, ...}) = IntegerConstant (hash_, Int.toString value)
  | expandExp _ (HOLFilePragma {hash_, value, ...}) = mkString (hash_, value)
  | expandExp _ (HOLLinePragmaWith {hash_, ...}) = Unit {left = hash_, right = hash_}
  | expandExp _ (HOLFilePragmaWith {hash_, ...}) = Unit {left = hash_, right = hash_}
  | expandExp _ (EmptyExp p) = Unit {left = p, right = p}
  | expandExp _ (BadExp {start = p, ...}) =
    Raise {raise_ = p, exp = App (mkIdent (p, "Fail"), mkString (p, "malformed"))}

and expandArms elems =
  map (fn {bar, pat, arrow, exp} =>
    {bar = bar, pat = expandExp true pat, arrow = arrow, exp = expandExp false exp}) elems
  handle HasOrPat => mapArms (expandExp true) #pat
    (fn ({bar, arrow, exp, ...}, pat) => {bar = bar, pat = pat, arrow = arrow, exp = exp}) elems

and expandFunBranches elems =
  map (fn {bar, pat, eq, exp} =>
    {bar = bar, pat = expandExp true pat, eq = eq, exp = expandExp false exp}) elems
  handle HasOrPat => mapArms (expandExp true) #pat
    (fn ({bar, eq, exp, ...}, pat) => {bar = bar, pat = pat, eq = eq, exp = exp}) elems

and expandQuote start stop toks = let
  fun go [] acc = rev acc
    | go (QuoteLiteral {line, col, value} :: rest) acc = let
      val s = mkLocPragma line col (Substring.string value)
      in go rest (App (mkIdent (start, "QUOTE"), mkString (start, s)) :: acc) end
    | go (QuoteAntiq {exp, ...} :: rest) acc =
      go rest (App (mkIdent (start, "ANTIQUOTE"), expandExp false exp) :: acc)
    | go (DefinitionLabel _ :: _) _ = raise Unreachable
  in List {left = start, elems = {args = go toks [], delims = []}, right = NONE, stop = stop} end

and expandDecs [] acc = rev acc
  | expandDecs (dec :: rest) acc = expandDecs rest (expandDec dec acc)

and expandDec (DecSemi _) acc = acc
  | expandDec (DecVal {val_, tyvars, elems}) acc = let
    fun f {rec_, pat, eq} = let
      val pat = expandExp true pat handle HasOrPat => raise Fail "or patterns not supported here"
      val eq = Option.map (fn {eq, exp} => {eq = eq, exp = expandExp false exp}) eq
      in {rec_ = rec_, pat = pat, eq = eq} end
    in DecVal {val_ = val_, tyvars = tyvars, elems = mapDelim f elems} :: acc end
  | expandDec (DecFun {fun_, tyvars, fvalbind}) acc =
    DecFun {fun_ = fun_, tyvars = tyvars, fvalbind = mapDelim expandFunBranches fvalbind} :: acc
  | expandDec (dec as DecType _) acc = dec :: acc
  | expandDec (dec as DecEqtype _) acc = dec :: acc
  | expandDec (dec as DecDatatype _) acc = dec :: acc
  | expandDec (dec as DecAbstype _) acc = dec :: acc
  | expandDec (dec as DecException _) acc = dec :: acc
  | expandDec (DecLocal {local_, dec1, in_, dec2, end_, stop}) acc =
    DecLocal {local_ = local_, dec1 = expandDecs dec1 [], in_ = in_,
      dec2 = expandDecs dec2 [], end_ = end_, stop = stop} :: acc
  | expandDec (dec as DecOpen _) acc = dec :: acc
  | expandDec (dec as DecInfix _) acc = dec :: acc
  | expandDec (dec as DecInfixr _) acc = dec :: acc
  | expandDec (dec as DecNonfix _) acc = dec :: acc
  | expandDec (DecStructure {structure_, elems}) acc = let
    fun f {id, constraint, bind} = let
      val bind = Option.map (fn {eq, strexp} => {eq = eq, strexp = expandStrExp strexp}) bind
      in {id = id, constraint = constraint, bind = bind} end
    in DecStructure {structure_ = structure_, elems = mapDelim f elems} :: acc end
  | expandDec (DecInclude {include_, sigexps}) acc =
    DecInclude {include_ = include_, sigexps = map expandSigExp sigexps} :: acc
  | expandDec (dec as Sharing _) acc = dec :: acc
  | expandDec (DecFunctor {functor_, elems}) acc = let
    fun f {id, lparen, funarg, rparen, constraint, bind} = let
      val funarg = expandFunArg funarg
      val bind = Option.map (fn {eq, strexp} => {eq = eq, strexp = expandStrExp strexp}) bind
      in {id = id, lparen = lparen, funarg = funarg,
          rparen = rparen, constraint = constraint, bind = bind} end
    in DecFunctor {functor_ = functor_, elems = mapDelim f elems} :: acc end

  | expandDec (dec as HOLTheory _) acc = dec :: acc
  | expandDec (HOLDefinition
      {definition_, id as (_, name), attrs, colon, quote, termination, end_, stop}) acc = let
    val indThm = ref NONE
    val _ = app (fn
        {key = (_, "induction"), bind = SOME {vals = [tgt], ...}} => indThm := SOME tgt
      | _ => raise Fail "unknown definition attribute"
      ) (case attrs of NONE => [] | SOME v => #args (#attrs v))
    val indThm = case !indThm of
      SOME s => s
    | NONE => (#1 id,
      if String.isSuffix "_def" name then
        String.extract (name, 0, SOME (size name - 4)) ^ "_ind"
      else if String.isSuffix "_DEF" name then
        String.extract (name, 0, SOME (size name - 4)) ^ "_IND"
      else name ^ "_ind")
    val e = ()
    val acc = valPat definition_ (mkIdent id) e :: acc
    in acc end

and expandFunArg (ArgIdent {strid, ty}) = let
    val ty = Option.map (fn {colon, sigexp} => {colon = colon, sigexp = expandSigExp sigexp}) ty
    in ArgIdent {strid = strid, ty = ty} end
  | expandFunArg (ArgSpec spec) = ArgSpec (expandDecs spec [])

and expandSigExp (s as SigIdent _) = s
  | expandSigExp (Spec {sig_, spec, end_, stop}) =
    Spec {sig_ = sig_, spec = expandDecs spec [], end_ = end_, stop = stop}
  | expandSigExp (WhereType {sigexp, where_, elems}) =
    WhereType {sigexp = expandSigExp sigexp, where_ = where_, elems = elems}

and expandStrExp (s as StrIdent _) = s
  | expandStrExp (StrStruct {struct_, strdec, end_, stop}) =
    StrStruct {struct_ = struct_, strdec = expandDecs strdec [], end_ = end_, stop = stop}
  | expandStrExp (StrConstraint {strexp, kind}) =
    StrConstraint {strexp = expandStrExp strexp, kind = kind}
  | expandStrExp (FunAppExp {funid, lparen, strexp, rparen, stop}) =
    FunAppExp {funid = funid, lparen = lparen,
      strexp = expandStrExp strexp, rparen = rparen, stop = stop}
  | expandStrExp (FunAppDec {funid, lparen, strdec, rparen, stop}) =
    FunAppDec {funid = funid, lparen = lparen,
      strdec = expandDecs strdec [], rparen = rparen, stop = stop}
  | expandStrExp (StrLetInEnd {let_, strdec, in_, strexp, end_, stop}) =
    StrLetInEnd {let_ = let_, strdec = expandDecs strdec [], in_ = in_,
      strexp = expandStrExp strexp, end_ = end_, stop = stop}

fun expandTheory {theory_, id, attrs, elems, ...} acc = let
  val bare = ref false
  val _ = app (fn
      {key = (_, "bare"), bind = NONE} => bare := true
    | _ => raise Fail "unknown theory attribute"
    ) (case attrs of NONE => [] | SOME v => #args (#attrs v))
  val grammar = ref []
  fun finish (NONE, acc) = acc
    | finish (SOME (false, ns), acc) =
      DecOpen {open_ = theory_, elems = rev ns} :: acc
    | finish (SOME (true, ns), acc) = DecLocal {
      local_ = theory_, dec1 = [DecOpen {open_ = theory_, elems = rev ns}],
      in_ = SOME theory_, dec2 = [], end_ = SOME theory_, stop = theory_} :: acc
  fun push b x (NONE, acc) = (SOME (b, [x]), acc)
    | push b x (p as (SOME (b2, ns), acc)) =
      if b = b2 then (SOME (b2, x :: ns), acc) else (SOME (b, [x]), finish p)
  fun process [] acc = finish acc
    | process (HOLAncestors {elems, ...} :: ls) acc = processList true elems ls acc
    | process (HOLLibs {elems, ...} :: ls) acc = processList false elems ls acc
  and processList _ [] ls acc = process ls acc
    | processList isThy ({id, attrs} :: thys) ls acc = let
      val aliases = ref []
      val qualified = ref false
      val ignoreGrammar = ref false
      val _ = app (fn x => case (x, isThy) of
          ({key = (_, "alias"), bind = SOME {vals = [tgt], ...}}, _) => aliases := tgt :: !aliases
        | ({key = (_, "qualified"), bind = NONE}, _) => qualified := true
        | ({key = (_, "ignore_grammar"), bind = NONE}, true) => ignoreGrammar := true
        | _ => raise Fail "unknown header attribute"
        ) (case attrs of NONE => [] | SOME v => #args (#attrs v))
      val id' = if isThy then (#1 id, #2 id ^ "Theory") else id
      val acc = push (!qualified) id' acc
      val _ = if isThy andalso not (!ignoreGrammar) then grammar := mkString id :: !grammar else ()
      val acc = foldl (fn (tgt, acc) => let
        val s = {id = tgt, constraint = NONE, bind = SOME {eq = #1 tgt, strexp = StrIdent id'}}
        val d = DecStructure {structure_ = #1 tgt, elems = {args = [s], delims = []}}
        in (NONE, d :: finish acc) end) acc (rev (!aliases))
      in processList isThy thys ls acc end
  val acc = (if !bare then NONE else SOME (false,
    map (fn s => (theory_, s)) ["Parse", "bossLib", "boolLib", "HolKernel"]), acc)
  val acc = process elems acc
  val acc = valWild theory_ (App (mkIdent (theory_, "Theory.new_theory"), mkString id)) :: acc
  val acc = if !bare then acc else
    valWild theory_ (App (mkIdent (theory_, "Parse.set_grammar_ancestry"),
      mkList (theory_, rev (!grammar)))) :: acc
  in acc end

val _ = fn HOLTheory t => expandTheory t | _ => raise Bind

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
