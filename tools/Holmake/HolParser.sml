structure HolParser :> HolParser =
struct

infix |>
fun x |> f = f x
fun mlquote s = String.concat ["\"", String.toString s, "\""]
fun K a _ = a
fun I a = a

structure Simple = struct

local
  structure H = HolLex.UserDeclarations
in
  datatype decl = datatype H.decl
  datatype decls = datatype H.decls
  datatype antiq = datatype H.antiq
  datatype qdecl = datatype H.qdecl
  datatype qbody = datatype H.qbody

  datatype topdecl
    = TopDecl of decl
    | EOF of int

  fun mkParser {read, parseError, pos} = let
    val lex = HolLex.makeLexer (read, pos) (H.STATE {
      comdepth = ref 0, comstart = ref NONE, pardepth = ref 0, parseError = parseError})
    val lookahead = ref NONE
    fun go () =
      case (case !lookahead of SOME tk => (lookahead := NONE; tk) | NONE => lex ()) of
        H.Decl (td, look) => (lookahead := look; TopDecl td)
      | H.CloseParen p => (parseError (p, p + 1) ("unexpected ')'"); go ())
      | H.EndTok _ => go ()
      | H.QED _ => go ()
      | H.EOF p => EOF p
      | _ => raise H.Unreachable
    in go end
end

fun killEnvelopingSpace s =
  s |> Substring.dropl Char.isSpace
    |> Substring.dropr Char.isSpace

fun destNameAttrs ss =
  if Substring.sub(ss, 0) = #"\"" then let
    val ss' = Substring.slice(ss, 1, NONE)
    val (nm, rest) = Substring.position "\"" ss'
    in (nm, Substring.slice(rest, 1, NONE)) end
  else
    Substring.position "[" ss

fun stringOfKey k =
    case k of
        "exclude_simps" => "simpLib.remove_simps"
      | "exclude_frags" => "simpLib.remove_ssfrags"
      | _ => k

fun destAttrs attrs =
  if Substring.isEmpty attrs then []
  else
    Substring.slice(attrs, 1, SOME (Substring.size attrs - 2))
      |> Substring.fields (fn c => c = #",")
      |> map (fn attr =>
        case Substring.fields (fn c => c = #"=") (killEnvelopingSpace attr) of
          [] => raise Fail "String.fields can't return an empty list"
        | [key] => (killEnvelopingSpace key, [])
        | key::vals::_ => (killEnvelopingSpace key, Substring.tokens Char.isSpace vals))

fun destMLThmBinding s =
  let
    (* s matches {keyword}{ws}+{ident}[attrs]
        ident is either a standard ML identifier, or something in double quotes
        NB: If it's in double quotes, the thing in quotes might include square
        brackets!

        returns the ident, the original string corresponding to the string +
        attributes, and the attributes as a separate list of strings
    *)
    val (kwordss, restss) =
        s |> Substring.splitl Char.isAlpha
    val ss = restss |> Substring.dropl Char.isSpace
    val (nms, attrs) = destNameAttrs ss
  in
    {keyword = kwordss, name_attrs = ss, name = nms, attrs = attrs}
  end

fun fromSS (base, ss) = let
  val (_, lo, len) = Substring.base ss
  in (base + lo, base + lo + len) end

datatype type_kind
  = OverloadKind of {inferior: bool, by_nametype: bool}
  | TypeKind of {pp: bool}

fun kindToName local_ kind =
  (if local_ then "temp_" else "") ^
  (case kind of
    OverloadKind {inferior, by_nametype} =>
    (if inferior then "inferior_" else "") ^
    "overload_on" ^
    (if by_nametype then "_by_nametype" else "")
  | TypeKind {pp} => "type_abbrev" ^ (if pp then "_pp" else ""))

(* ("Type"|"Overload"){ws}+({alphaMLid}|{quotedsymbolid})("["{alphaMLid_list}"]")?{ws}*"=" *)
fun parseBeginType (start, text) parseError = let
  val s = Substring.substring(text, 0, size text - 1) (* drop = *)
    |> Substring.dropr Char.isSpace (* drop wspace after name *)
  val {keyword, name, attrs, ...} = destMLThmBinding s
  val isOverload = Substring.size keyword = 8
  fun expectNoArgs [] = ()
    | expectNoArgs (v :: _) = parseError (fromSS (start, v)) "expected no arguments"
  val inferior = ref false
  val local_ = ref false
  val pp = ref false
  val by_nametype = ref false
  fun parseAttr (k, vs) =
    case (Substring.string k, isOverload) of
      ("inferior", true) => (expectNoArgs vs; inferior := true)
    | ("local", _) => (expectNoArgs vs; local_ := true)
    | ("pp", false) => (expectNoArgs vs; pp := true)
    | ("by_nametype", true) => (expectNoArgs vs; by_nametype := true)
    | (sk, _) => parseError (fromSS (start, k)) ("unexpected attribute '"^sk^"'")
  val _ = app parseAttr (destAttrs attrs)
  val kind =
    if isOverload then OverloadKind {inferior = !inferior, by_nametype = !by_nametype}
    else TypeKind {pp = !pp}
  in {local_ = !local_, kind = kind, keyword = keyword, tyname = name} end

(* {Theorempfx}{ws}*":"  or  {Theorempfx}({ws}|{newline})+"="
where Theorempfx = ("Theorem"|"Triviality"){ws}+{alphaMLid}({ws}*"["{alphaMLid_list}"]")?; *)
fun parseTheoremPfx text = let
  val s = Substring.substring(text, 0, size text - 1) (* drop : or = *)
    |> Substring.dropr Char.isSpace (* drop wspace between name and ] *)
  val {keyword, name, attrs, name_attrs} = destMLThmBinding s
  val isTriv = Substring.size keyword = 10
  in {isTriv = isTriv, keyword = keyword,
      thmname = name, attrs = attrs, name_attrs = name_attrs} end

(* Inductivepfx = ("Co")?"Inductive"{ws}+{alphaMLid}{ws}*":"; *)
fun parseInductivePfx text = let
  val (keyword, s) = Substring.substring(text, 0, size text - 1) (* drop : *)
    |> Substring.splitl (not o Char.isSpace) (* split keyword *)
  val name = s
    |> Substring.dropl Char.isSpace (* space before name *)
    |> Substring.dropr Char.isSpace (* space after name *)
  in {isCo = Substring.size keyword = 11, keyword = keyword, thmname = name} end

(* Definitionpfx =
"Definition"{ws}+{alphaMLid}({ws}*"["{optallws}{defn_attribute_list}"]")?{ws}*":"; *)
fun parseDefinitionPfx text = let
  val s = Substring.substring(text, 0, size text - 1) (* drop : *)
    |> Substring.dropr Char.isSpace (* drop wspace after name *)
  in destMLThmBinding s end

(* Quote_pfx = "Quote"{ws}+{QUALalphaMLid}{ws}*":"; *)
fun parseQuotePfx text = let
  val name = Substring.substring(text, 6, size text - 7) (* drop :, "Quote" + next ws char *)
    |> Substring.dropl Char.isSpace (* space before name *)
    |> Substring.dropr Char.isSpace (* space after name *)
  in {keyword = Substring.substring(text, 0, 5), name = name} end

(* Quote_eqnpfx = "Quote"{ws}+{alphaMLid}{ws}*"="{ws}*{QUALalphaMLid}{ws}*":"; *)
fun parseQuoteEqnPfx text = let
  val (left, right) = Substring.substring(text, 6, size text - 7) (* drop :, Quote, next ws char *)
    |> Substring.dropl Char.isSpace (* space before name *)
    |> Substring.dropr Char.isSpace (* space after name *)
    |> Substring.position "="
  val bind = left |> Substring.dropr Char.isSpace
  val name = Substring.slice(right, 1, NONE) |> Substring.dropl Char.isSpace
  in {keyword = Substring.substring(text, 0, 5), bind = bind, name = name} end

(* DefinitionLabel = "["{ws}*{DefinitionLabelID}?("["{alphaMLid_list}"]")?{ws}*":"?{ws}*"]"; *)
fun parseDefnLabel text = let
  val ss = Substring.full text
    |> Substring.dropr Char.isSpace
    |> (fn s => Substring.slice (s, 1, SOME (Substring.size s - 2)))
    |> Substring.dropl Char.isSpace
    |> Substring.dropr (fn c => Char.isSpace c orelse c = #":")
  val (ss, tilde) =
    case Substring.getc ss of
      SOME (#"~", ss) => (ss, true)
    | _ => (ss, false)
  val (name, attrs) = destNameAttrs ss
  val str = Substring.string name
  val name =
    if str = "/\092" orelse str = "\226\136\167" orelse str = "" then NONE
    else SOME name
  in {tilde = tilde, name = name, attrs = attrs, name_attrs = ss} end

end

structure ToSML = struct

  type double_reader = {
    read: int -> string,
    readAt: int -> int -> (int * substring -> unit) -> unit
  }

  (*
    This function takes an input stream `read: int -> string` and returns another stream with the
    same type, along with a function `readAt (from: int) (to: int) (push: int * substring -> unit)`
    which is another stream, yielding values that have already been yielded from the first stream.
    Internally it maintains a buffer of results that `read` has yielded, indexed by byte positions
    (starting at `pos`).

    `readAt from to push` is a request to skip forward to position `from`, then yield the bytes
    `from .. to` to the callback `push`. This function can only be called once for these positions;
    the next call to `readAt` must have a `from` larger than the previous `to` value and `to` must
    be no larger than the total of all bytes provided by the main stream `read`.

    `push (bufstart, chunk)` is called repeatedly to output each chunk of the response, where
    `bufstart + chunk.start` is the position of the start of `chunk` in the stream.
  *)
  fun mkDoubleReader read pos: double_reader = let
    val inbox = ref (pos, [])
    val outbox = ref (pos, [])
    val pos = ref pos
    fun read' n = let
      val buf = read n
      val _ = if buf = "" then () else let
        val (ahead, backlog) = !inbox
        in inbox := (ahead + size buf, buf :: backlog) end
      in buf end
    fun readAt from to push = let
      fun checkInbox from = if from = to then () else let
        fun moveToOutbox [] mid acc = raise Fail "unreachable"
          | moveToOutbox (chunk :: rest) mid acc = let
            val mid' = mid - size chunk
            in
              if mid' <= from then printOutbox mid' chunk mid acc from
              else moveToOutbox rest mid' (chunk :: acc)
            end
        val (lead, bufs) = !inbox
        val _ = if to <= lead then () else raise Fail "main reader has not yielded this much yet"
        in inbox := (lead, []); moveToOutbox bufs lead [] end
      and printOutbox trail chunk trail' rest from =
        if to <= trail' then (
          push (trail, Substring.substring (chunk, from - trail, to - from));
          outbox := (trail, chunk :: rest)
        ) else (
          push (trail, Substring.substring (chunk, from - trail, trail' - from));
          case rest of
            [] => checkInbox trail'
          | chunk' :: rest' => printOutbox trail' chunk' (trail' + size chunk') rest' trail'
        )
      fun dropOutbox [] _ = checkInbox from
        | dropOutbox (chunk :: rest) trail = let
          val trail' = trail + size chunk
          in
            if trail' <= from then dropOutbox rest trail'
            else printOutbox trail chunk trail' rest from
          end
      val _ = if from <= to then () else raise Fail "readAt: to < from"
      val (back, bufs) = !outbox
      val _ = if back <= from then () else raise Fail "segment has already been yielded"
      in dropOutbox bufs back end
    in {read = read', readAt = readAt} end

  type strcode = {
    aux: string -> unit,
    regular: int * substring -> unit,
    strcode: int * substring -> unit,
    strstr: int * substring -> unit
  }

  local
    fun encoder f push (_, s) = let
      val (s, start, len) = Substring.base s
      val stop = start + len
      fun loop start p =
        if p = stop then
          if start = p then () else push (String.substring (s, start, p - start))
        else
          case f (String.sub (s, p)) of
            NONE => loop start (p+1)
          | SOME r => (
            if start = p then () else push (String.substring (s, start, p - start));
            push r;
            loop (p+1) (p+1))
      in loop start start end
  in
    val strstr = encoder (fn ch =>
      if ch < #"\128" then NONE else SOME (AttributeSyntax.bslash_escape ch))
    val strcode = encoder (fn
        #"\\" => SOME "\\\\"
      | #"\"" => SOME "\\\""
      | #"\n" => SOME "\\n\\\n\\"
      | ch => if Char.isPrint ch then NONE else SOME (AttributeSyntax.bslash_escape ch))
  end

  fun mkStrcode push: strcode = {
    regular = fn s => push (Substring.string (#2 s)),
    aux = push,
    strstr = strstr push,
    strcode = strcode push
  }

  fun mkPushTranslatorCore {read, filename, parseError}
      ({regular, aux, strstr, strcode = strcode0}:strcode) = let
    open Simple
    val ss = Substring.string
    val full = Substring.full
    val cat = Substring.concat
    val filename = ref filename
    val {read, readAt} = mkDoubleReader read 0
    val feed = mkParser {read = read, pos = ~1 (* fix for mllex bug *), parseError = parseError}
    val lookahead = ref NONE
    fun feed' () = case !lookahead of SOME tk => tk | NONE => feed ()
    val inThmVal = ref false
    fun finishThmVal () = if !inThmVal then (aux ");"; inThmVal := false) else ()
    val line = ref (0, 0)
    fun countlines (p, s) = let
      val lastline = Substring.dropr (fn c => c <> #"\n") s
      in
        if Substring.isEmpty lastline then ()
        else line := (
          Substring.foldr (fn (c, n) => if c = #"\n" then n+1 else n) (#1 (!line)) lastline,
          let val (_, start, len) = Substring.base lastline in p + start + len end)
      end
    fun wrap f (start, stop) = if start = stop then () else
      readAt start stop (fn s => (countlines s; f s))
    val regular = wrap regular
    val strcode = wrap strcode0
    val strstr = wrap strstr
    val regular' = regular o fromSS
    val strcode' = strcode o fromSS
    val strstr' = strstr o fromSS
    fun locpragma pos = let
      val (line, start) = !line
      in
        aux (concat [
          " (*#loc ", Int.toString (line + 1), " ", Int.toString (pos - start + 1), "*)"])
        (* NB: the initial space is critical, or else the comment might not be recognised
           when prepended by a paren or symbol char.  --KW
           See cvs log comment at rev 1.2 of src/parse/base_tokens.lex *)
      end
    fun quote (start, stop) = (locpragma start; strcode (start, stop))
    fun magicBind name =
      aux (" " ^ Systeml.bindstr (concat ["val ", name, " = DB.fetch \"-\" \"", name,
        "\" handle Feedback.HOL_ERR _ => boolTheory.TRUTH;"]) ^ ";")
    fun doThmAttrs false p attrs name_attrs = aux (ss name_attrs)
      | doThmAttrs true p attrs name_attrs =
        if Substring.isEmpty attrs then
          (aux (ss name_attrs); aux "[local]")
        else (
          aux (ss (Substring.slice (name_attrs, 0, SOME (Substring.size name_attrs - 1))));
          aux ",local]")
    fun doQuoteCore start ds stop f = case ds of
        [] => quote (start, stop)
      | QuoteComment _ :: rest => doQuoteCore start rest stop f
      | QuoteAntiq (_, BadAntiq _) :: rest => doQuoteCore start rest stop f
      | QuoteAntiq (p, Ident (idstart, id)) :: rest => (
        quote (start, p);
        aux "\", ANTIQUOTE "; regular (idstart, idstart + size id); aux ", QUOTE \"";
        doQuoteCore (idstart + size id) rest stop f)
      | QuoteAntiq (p, Paren {start_tok, decls, end_tok, stop = pstop}) :: rest => let
        val Decls {start = dstart, decls, stop = dstop} = decls
        in
          quote (start, p); aux "\", ANTIQUOTE ";
          case end_tok of
            NONE => (doDecls start_tok decls dstop; aux ")")
          | SOME _ => doDecls start_tok decls pstop;
          aux ", QUOTE \"";
          doQuoteCore pstop rest stop f
        end
      | DefinitionLabel (l as (p, t)) :: rest =>
        case f of
          NONE => doQuoteCore start rest stop f
        | SOME g => (quote (start, p); g l; doQuoteCore (p + size t) rest stop f)
    and doQuote (QBody {start, toks, stop}) =
      (aux "[QUOTE \""; doQuoteCore start toks stop NONE; aux "\"]")
    and doQuoteConj (QBody {start, toks, stop}) f = let
      val first = ref true
      val strcode1 = wrap (fn (p as (_, s)) => (
        if !first then first := Substring.isEmpty (Substring.dropl Char.isSpace s) else ();
        strcode0 p))
      fun doQuote0 start toks =
        case toks of
          DefinitionLabel (l as (p, t)) :: rest => (
          strcode1 (start, p); f (!first) l;
          doQuoteCore (p + size t) rest stop (SOME (f false)))
        | QuoteComment (p, stop) :: rest =>
          (strcode1 (start, p); strcode (p, stop); doQuote0 stop rest)
        | _ => doQuoteCore start toks stop (SOME (f false))
      in aux "[QUOTE \"("; locpragma start; doQuote0 start toks; aux ")\"]" end
    and doDecl eager pos d = case d of
        DefinitionDecl {head = (p, head), quote, termination, stop, ...} => let
        val {keyword, name, attrs, name_attrs} = parseDefinitionPfx head
        val attrs = destAttrs attrs
        val indThm =
          case List.find (fn (k,v) => Substring.compare (k, full "induction") = EQUAL) attrs of
            SOME (_, s::_) => ss s
          | _ =>
            if Substring.isSuffix "_def" name then
              cat [Substring.slice (name, 0, SOME (Substring.size name - 4)), full "_ind"]
            else if Substring.isSuffix "_DEF" name then
              cat [Substring.slice (name, 0, SOME (Substring.size name - 4)), full "_IND"]
            else cat [name, full "_ind"]
        in
          regular (pos, p); finishThmVal ();
          aux "val "; regular' (p, name); aux " = ";
          if !filename = "" then aux "TotalDefn.qDefine"
          else app aux [
            "TotalDefn.located_qDefine (DB_dtype.mkloc (",
              mlquote (!filename), ", ",
              Int.toString (#1 (!line) + 1) ^ ", true))"];
          app aux [" \"", ss name_attrs, "\" "]; doQuote quote;
          case termination of
            NONE => aux " NONE;"
          | SOME {decls = Decls {start = dstart, decls = decls, stop = dstop}, ...} =>
            (aux " (SOME ("; doDecls dstart decls dstop; aux "));");
          magicBind indThm;
          stop
        end
      | DatatypeDecl {head = (p, head), quote, stop, ...} => (
          regular (pos, p); finishThmVal ();
          aux "val _ = bossLib.Datatype "; doQuote quote; aux ";";
          stop)
      | QuoteDecl {head = (p, head), quote, stop, ...} => let
        val {keyword, name} = parseQuotePfx head
        in
          regular (pos, p); finishThmVal ();
          aux "val _ = "; regular' (p, name); aux " "; doQuote quote; aux ";";
          stop
        end
      | QuoteEqnDecl {head = (p, head), quote, stop, ...} => let
        val {keyword, name, bind} = parseQuoteEqnPfx head
        in
          regular (pos, p); finishThmVal ();
          aux "val "; regular' (p, bind); aux " = ";
          regular' (p, name); aux " "; doQuote quote; aux ";";
          stop
        end
      | InductiveDecl {head = (p, head), quote, stop, ...} => let
        val {isCo, keyword, thmname = stem} = parseInductivePfx head
        val (entryPoint, indSuffix) =
          if isCo then ("CoIndDefLib.xHol_coreln", "_coind") else ("IndDefLib.xHol_reln", "_ind")
        val conjIdx = ref 1
        val conjs = ref []
        fun collect first (p, lab) = (
          if first then () else (aux ") /\\\\ ("; conjIdx := !conjIdx + 1);
          case parseDefnLabel lab of
            {tilde, name = SOME name, name_attrs, ...} =>
            conjs := (!conjIdx, tilde, name, name_attrs) :: !conjs
          | _ => ()
        )
        in
          regular (pos, p); finishThmVal ();
          app aux ["val (", ss stem, "_rules,", ss stem, indSuffix, ",",
            ss stem, "_cases) = ", entryPoint, " \"", ss stem, "\" "];
          doQuoteConj quote collect; aux ";";
          magicBind (cat [stem, full "_strongind"]);
          app (fn (i, tilde, name, name_attrs) => let
            val f = if tilde then fn s => app aux [ss stem, "_", s] else aux
            in
              aux " val "; f (ss name); aux " = boolLib.save_thm(\""; f (ss name_attrs);
              app aux ["\", Drule.cj ", Int.toString i, " ",
                ss stem, "_rules handle HOL_ERR _ => boolTheory.TRUTH);"]
            end) (rev (!conjs));
          stop
        end
      | BeginType (p, head) => let
        val {local_, kind, keyword, tyname} = parseBeginType (p, head) parseError
        val fnm = kindToName local_ kind
        in
          regular (pos, p); finishThmVal ();
          app aux ["val _ = Parse.", fnm, "(\""]; strstr' (p, tyname); aux "\",";
          inThmVal := true; p + size head
        end
      | BeginSimpleThm (p, head) => let
        val {isTriv, keyword, thmname, attrs, name_attrs} = parseTheoremPfx head
        in
          regular (pos, p); finishThmVal ();
          aux "val "; regular' (p, thmname); aux " = boolLib.save_thm(\"";
          doThmAttrs isTriv p attrs name_attrs; aux "\","; inThmVal := true;
          p + size head
        end
      | TheoremDecl {head = (p, head), quote, proof_tok, body, stop, ...} => let
        val {isTriv, keyword, thmname, attrs, name_attrs} = parseTheoremPfx head
        val goalabs = "(fn HOL__GOAL__foo => (";
        val Decls {start = dstart, decls, stop = dstop} = body
        in
          regular (pos, p); finishThmVal ();
          aux "val "; regular' (p, thmname); aux " = Q.store_thm(\"";
          doThmAttrs isTriv p attrs name_attrs; aux "\", ";
          doQuote quote; aux ", ";
          case proof_tok of
            SOME (p, tok) => let
            fun ofKey "exclude_simps" = "simpLib.remove_simps"
              | ofKey "exclude_frags" = "simpLib.remove_ssfrags"
              | ofKey k = k
            fun mktm1 (k,vals) = ofKey (ss k) ^ " [" ^
              String.concatWith "," (map (mlquote o ss) vals) ^ "]"
            fun mktm kv [] = mktm1 kv
              | mktm kv (kv2::xs) = mktm1 kv ^ " o " ^ mktm kv2 xs
            val () = case destAttrs (#2 (destNameAttrs (full tok))) of
              [] => ()
            | kv::attrs => aux ("BasicProvers.with_simpset_updates (" ^ mktm kv attrs ^ ") ")
            val n = #1 (!line)
            val _ = readAt p (p + size tok) countlines
            in aux goalabs; aux (CharVector.tabulate (#1 (!line) - n, (fn _ => #"\n"))) end
          | _ => aux goalabs;
          doDecls dstart decls dstop; aux ") HOL__GOAL__foo));";
          stop
        end
      | Chunk p =>
        if !inThmVal then
          (regular (pos, p); aux ");"; inThmVal := false; p)
        else if eager then
          (regular (pos, p); p)
        else
          pos
      | Semi p =>
        if !inThmVal then
          (regular (pos, p); aux ")"; inThmVal := false; regular (p, p+1); p+1)
        else if eager then
          (regular (pos, p+1); p+1)
        else
          pos
      | FullQuote {head = (p, head), type_q, quote, stop, ...} => (
        regular (pos, p);
        aux (case type_q of NONE => "(Parse.Term " | SOME _ => "(Parse.Type ");
        doQuote quote; aux ")";
        stop)
      | Quote {head = (p, _), quote, stop, ...} => (regular (pos, p); doQuote quote; stop)
      | String (start, stop) => (regular (pos, start); strstr (start, stop); stop)
      | LinePragma p => (regular (pos, p); aux (Int.toString (#1 (!line) + 1)); p + 7)
      | LinePragmaWith (p, text) => let
        val num = Substring.substring(text, 7, size text - 8)
        in
          regular (pos, p);
          case Int.fromString (Substring.string num) of
            NONE => parseError (fromSS (p, num)) "expected an integer"
          | SOME num => line := (fn (_, pos) => (num - 1, pos)) (!line);
          aux " "; p + size text
        end
      | FilePragma p => (regular (pos, p); aux (mlquote (!filename)); p + 7)
      | FilePragmaWith (p, text) => (
          regular (pos, p);
          filename := String.substring(text, 7, size text - 8);
          aux " "; p + size text)
    and doDecls start [] stop = regular (start, stop)
      | doDecls start (d :: ds) stop = doDecls (doDecl false start d) ds stop
    in {
      feed = feed',
      regular = regular,
      finishThmVal = finishThmVal,
      doDecl = doDecl
    } end

  fun mkPushTranslator args strcode = let
    open Simple
    val {feed, regular, finishThmVal, doDecl, ...} = mkPushTranslatorCore args strcode
    val pos = ref 0
    in fn () =>
      case feed () of
        TopDecl d => (pos := doDecl true (!pos) d; false)
      | Simple.EOF p => (regular (!pos, p); finishThmVal (); pos := p; true)
    end

  fun mkPullTranslator args = let
    val queue = ref []
    val atEnd = ref false
    val push = mkPushTranslator args (mkStrcode (fn s => queue := s :: !queue))
    fun loop () =
      case !queue of
        s :: rest => (queue := rest; s)
      | [] => if !atEnd then "" else (
        atEnd := push ();
        queue := rev (!queue);
        loop ())
    in loop end

end

open HOLFileSys
type reader = {read : unit -> char option, eof : unit -> bool}

fun exhaust_parser (read, close) =
  let
    fun recurse acc =
      case read () of
          "" => (close(); String.concat (List.rev acc))
        | s => recurse (s::acc)
  in
    recurse []
  end

fun mkstate b = {inscriptp = b, quotefixp = false}

fun file_to_parser fname = let
  val instrm = openIn fname
  (* val isscript = String.isSuffix "Script.sml" fname *)
  val read = ToSML.mkPullTranslator
    {read = fn n => input instrm, filename = fname, parseError = K (K ())}
  in (read, fn () => closeIn instrm) end

fun string_to_parser isscriptp s = let
  val sr = ref s
  fun str_read _ = (!sr before sr := "")
  val read = ToSML.mkPullTranslator {read = str_read, filename = "", parseError = K (K ())}
  in (read, I) end

fun input_to_parser isscriptp fname inp = let
  val read = ToSML.mkPullTranslator {read = inp, filename = fname, parseError = K (K ())}
  in (read, I) end

fun stream_to_parser isscriptp fname strm =
  input_to_parser isscriptp fname (fn n => input strm)

fun inputFile fname = exhaust_parser (file_to_parser fname)
fun fromString b s = exhaust_parser (string_to_parser b s)

fun mkReaderEOF (read, close) = let
  val i = ref 0
  val s = ref ""
  val sz = ref 0
  val eofp = ref false
  fun pull () = (s := read(); sz := size (!s); i := 0;
                 if !sz = 0 then (eofp := true; close()) else ())
  fun doit () =
    if !eofp then NONE
    else if !i < !sz then SOME (String.sub(!s,!i)) before i := !i + 1
    else (pull(); doit())
  fun eof () = !eofp
  in {read = doit, eof = eof} end

fun fileToReader fname = mkReaderEOF (file_to_parser fname)
fun stringToReader b s = mkReaderEOF (string_to_parser b s)
fun inputToReader b fnm inp = mkReaderEOF (input_to_parser b fnm inp)
fun streamToReader b fnm strm = mkReaderEOF (stream_to_parser b fnm strm)

end
