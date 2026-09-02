signature LSPServer =
sig
  val start : {diag: string -> unit, dbg: bool} -> unit
end;

(* load "JSONDecode"; *)

structure LSPServer :> LSPServer =
struct

(* structure Thread = PolyThread; *)
open Thread LSPExtension

fun I x = x
fun leLC (l,c) (l',c') = l <= l' andalso (l <> l' orelse c <= c')

type encode = (string -> unit) -> unit
fun encOut str: encode = fn print => print str
val encNull = encOut "null"
fun encInt x = if x < 0 then encOut ("-" ^ Int.toString (~x)) else encOut (Int.toString x)

local

fun encodeSubstring {str, start, stop} print = let
  fun cleanup start i =
    if start < i then print (String.substring (str, start, i - start)) else ()
  fun hexdigit n = Char.chr (n + (if n < 10 then 48 else 55))
  fun inner start i =
    if i >= stop then cleanup start i
    else
      let val c = String.sub (str, i) in
        if #" " <= c then
          if c = #"\\" then breakStreak start i "\\\\" else
          if c = #"\"" then breakStreak start i "\\\"" else
          inner start (i+1)
        else breakStreak start i (case c of
            #"\b" => "\\b"
          | #"\f" => "\\f"
          | #"\n" => "\\n"
          | #"\r" => "\\r"
          | #"\t" => "\\t"
          | _ => let
            val n = Char.ord c
            in "\\u00" ^ String.implode [hexdigit (n div 16), hexdigit (n mod 16)] end)
      end
  and breakStreak start i next = (cleanup start i; print next; inner (i+1) (i+1))
  in inner start start end

in

(* fun encSubstringContents str = let
  val (str, start, length) = Substring.base str
  in encodeSubstring {str=str, start=start, stop=start+length} end *)

fun encStringContents str =
  encodeSubstring {str=str, start=0, stop=String.size str}

end

fun encString str print = (print "\""; encStringContents str print; print "\"")

(* fun encSubstring str print = (print "\""; encSubstringContents str print; print "\"") *)

fun encOrNull _ NONE = encNull
  | encOrNull encode (SOME a) = encode a

fun encArray encode ls print = case ls of
    [] => print "[]"
  | a :: ls => let
    fun inner [] = print "]"
      | inner (a :: ls) = (print ","; encode a print; inner ls)
    val () = print "["
    val () = encode a print
    in inner ls end

fun encPosition (line, col) print = (
  print "{\"line\":"; encInt line print;
  print ",\"character\":"; encInt col print;
  print "}")

fun encRange encPos (start, stop) print = (
  print "{\"start\":"; encPos start print;
  print ",\"end\":"; encPos stop print;
  print "}")

type location_link = {
  origin: rangeLC option,
  range: rangeLC, selRange: rangeLC, uri: string option}

fun encLocationLink uri0 ({origin, uri, range, selRange}: location_link) print = (
  print "{\"targetUri\":"; encString (Option.getOpt (uri, uri0)) print;
  print ",\"targetRange\":"; encRange encPosition range print;
  print ",\"targetSelectionRange\":"; encRange encPosition selRange print;
  case origin of
    NONE => ()
  | SOME origin => (print ",\"originSelectionRange\":"; encRange encPosition origin print);
  print "}")

fun encHover ({markdown, range}: hover) print = (
  print "{\"contents\":{\"kind\":\"markdown\",\"value\":";
    encString markdown print; print "}";
  case range of
    NONE => ()
  | SOME range => (print ",\"range\":"; encRange encPosition range print);
  print "}")

fun encGoalState ({asms, goal}: goal_state) print = (
  print "{\"asms\":"; encArray encString asms print;
  print ",\"goal\":"; encString goal print;
  print "}")

fun encGoalStateResponse ({theorem, step, goals, pretty, context, status,
                           error, failedRange} : goal_state_response) print = (
  print "{\"theorem\":"; encString theorem print;
  print ",\"step\":"; encInt step print;
  print ",\"goals\":"; encArray encGoalState goals print;
  print ",\"pretty\":"; encString pretty print;
  print ",\"context\":"; encArray encString context print;
  print ",\"status\":"; encString status print;
  print ",\"error\":"; encOrNull encString error print;
  print "}")

(* Stream an in-memory buffer's declarations.  The parser pulls its
   input through a callback and we have the whole text in hand, so give
   it over in one chunk and nothing after that.  Errors are dropped: a
   buffer being edited is mildly invalid most of the time. *)
fun bufferDecs text = let
  val consumed = ref false
  fun read _ = if !consumed then "" else (consumed := true; text)
  fun errSink _ _ _ = ()
  val {parseDec, ...} =
    HOLSourceParser.parseSML "" read errSink HOLSourceParser.initialScope
  in parseDec end

(* Given the buffer text and a cursor byte offset, return the enclosing
   `Theorem NAME[attrs]: … Proof … QED` block (also `Triviality`) as a
   `theorem_context`, or NONE if the cursor isn't inside one.  The
   declaration's start byte comes back with it: that is how the proof
   pool names a proof, and finding it here saves a second walk over the
   buffer.

   Drives HOLSourceParser over the current buffer text — same parser
   the compile uses — so keyword matching, attribute brackets, strings
   and comments are handled correctly.  parseDec streams decs one at a
   time; we bail on the first matching HOLTheoremDecl. *)
fun findEnclosingTheorem compileDone text cursor = let
  val parseDec = bufferDecs text
  fun loop () =
    case parseDec () of
      NONE => NONE
    | SOME (dec as HOLSourceAST.HOLTheoremDecl {
              id = (_, name), colon, tac,
              proof_ = SOME {proof_, ...}, qed_, stop, ...}) =>
        (* An in-progress Proof-QED block has `qed_ = NONE`; treat the
           dec's `stop` as the upper bound so the LSP can drive live
           goal-state while the user is still typing the tactic body
           (Slice G.1). *)
        let val upperBound = case qed_ of SOME q => q | NONE => stop in
        if proof_ <= cursor andalso cursor <= upperBound
        then let val (tacStart, tacEnd) = HOLSourceAST.expSpan tac
                 val (decStart, _) = HOLSourceAST.decSpan dec
        in SOME (decStart,
                 {name = name,
                  quote = String.substring (text, colon + 1,
                                            Int.max (0, proof_ - colon - 1)),
                  quoteStart = colon + 1,
                  tacText = String.substring (text, tacStart,
                                              Int.max (0, tacEnd - tacStart)),
                  tacStart = tacStart,
                  cursor = cursor,
                  compileDone = compileDone})
        end
        else loop ()
        end
    | SOME _ => loop ()
  in loop () end

(* SML identifier characters, for the two places that scan raw text:
   the `Datatype:' name scrape and completion's prefix.  Not
   `HOLSourceParser''s own `isIdRest', which it does not export. *)
fun isIdentChar c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"

(* The declarations of a buffer, for `textDocument/documentSymbol'.

   Driven by the parser rather than by the last compile's `builtTrees':
   an outline is wanted most exactly when the file does not compile --
   its ancestors are missing, or it is halfway through an edit -- and
   `bufferDecs' needs neither a compile nor any HOL state.  It is also
   the only source that covers the whole file rather than the part the
   compile frontier has reached.

   `span' is the whole declaration and `selSpan' the name as written;
   LSP wants both, the second to highlight when you pick the symbol. *)
datatype symbol = Sym of {
  name: string,
  detail: string option,
  kind: int,
  span: int * int,
  selSpan: int * int,
  children: symbol list }

(* LSP SymbolKind, the few we use. *)
val symModule = 2 and symMethod = 6 and symConstructor = 9
val symEnum = 10 and symInterface = 11 and symFunction = 12
val symVariable = 13 and symConstant = 14 and symStruct = 23
val symOperator = 25

(* A file with more declarations than this is pathological; the cap
   keeps a runaway parse off the request thread. *)
val maxSymbols = 2000

fun bufferSymbols text = let
  val parseDec = bufferDecs text
  val count = ref 0
  fun bump () = (count := !count + 1; !count <= maxSymbols)
  open HOLSourceAST
  fun mkSym {name = (p, nm), detail, kind, span, children} =
      if nm = "" then NONE   (* parse repair invents empty idents *)
      else SOME (Sym {name = nm, detail = detail, kind = kind,
                      span = span, selSpan = (p, p + size nm),
                      children = children})
  (* `[simp]', `[local]' and friends.  LSP's SymbolTag has only
     Deprecated, so an attribute cannot be structural; it goes in the
     detail line where a client will show it beside the name. *)
  fun attrsText render (attrs: 'a attrs) =
      case attrs of
        NONE => ""
      | SOME {attrs = {args, ...}, ...} =>
        (case List.mapPartial render args of
           [] => ""
         | ss => " [" ^ String.concatWith ", " ss ^ "]")
  fun kvalText ({key = (_, k), bind} : kvals) =
      SOME (case bind of
              NONE => k
            | SOME {vals, ...} =>
              k ^ " = " ^ String.concatWith "," (map #2 vals))
  fun identText ((_, s) : ident) = SOME s
  fun kw base attrs = SOME (base ^ attrsText kvalText attrs)
  fun kwI base attrs = SOME (base ^ attrsText identText attrs)
  (* Names bound by a `val' pattern.  Constructor positions are not
     bindings: `val SOME x = e' binds x, and `val h::t = e' binds h and
     t, so the head of an application and an infix operator are both
     skipped. *)
  fun patNames e acc = case e of
      Ident {id, ...} => id :: acc
    | Parens {exp, ...} => patNames exp acc
    | Typed {exp, ...} => patNames exp acc
    | Tuple {elems = {args, ...}, ...} => foldl (fn (a, c) => patNames a c) acc args
    | List {elems = {args, ...}, ...} => foldl (fn (a, c) => patNames a c) acc args
    | App (_, arg) => patNames arg acc
    | Infix {left, right, ...} => patNames left (patNames right acc)
    | Layered {id, pat, ...} => id :: patNames pat acc
    | _ => acc
  (* `fun f x y = ...': the name is the head of the clause's pattern. *)
  fun funName e = case e of
      Ident {id, ...} => SOME id
    | App (f, _) => funName f
    | Parens {exp, ...} => funName exp
    | Infix {id, ...} => SOME id
    | _ => NONE
  (* `Datatype:' carries no parsed identifier -- the names live in the
     quotation, which the expander hands to bossLib.Datatype unread.
     A QuoteLiteral is (file offset, raw slice), so scan the text for
     the identifier before each top-level `=' and keep its offset. *)
  fun quoteTypeNames qs = let
    fun literals [] acc = rev acc
      | literals (QuoteLiteral (i, s) :: r) acc = literals r ((i, s) :: acc)
      | literals (_ :: r) acc = literals r acc
    (* One declaration: its name is the leading identifier, and it
       counts only if this piece goes on to define something. *)
    fun nameOf (base, piece) = let
      val ss = Substring.full piece
      val trimmed = Substring.dropl Char.isSpace ss
      val lead = Substring.size ss - Substring.size trimmed
      val (nm, rest) = Substring.splitl isIdentChar trimmed
      in
        if Substring.isEmpty nm orelse not (Substring.isSubstring "=" rest)
        then NONE
        else SOME (base + lead, Substring.string nm)
      end
    fun namesIn (base, s) = let
      (* `String.fields' loses the offsets, so carry one along: each
         piece starts after the previous piece and its `;'. *)
      fun step (piece, (off, acc)) =
          (off + size piece + 1, nameOf (off, piece) :: acc)
      val pieces = String.fields (fn c => c = #";") s
      val (_, acc) = List.foldl step (base, []) pieces
      in List.mapPartial (fn x => x) (rev acc) end
    in List.concat (map namesIn (literals qs [])) end
  (* Labelled conjuncts of a Definition or Inductive appear in the
     source, so they can be children with honest spans; the generated
     names (foo_ind, foo_rules) cannot. *)
  fun labelNames qs =
      List.mapPartial
        (fn DefinitionLabel {label = SOME (HOLLabel {id, ...}), ...} => SOME id
          | _ => NONE) qs
  fun symsOf dec =
      if not (bump ()) then []
      else let
        val span = decSpan dec
        (* One symbol from an id, for the many shapes that differ only
           in what to call them. *)
        fun simple detail kind id =
            mklist {name = id, detail = SOME detail, kind = kind,
                    span = span, children = []}
        (* The `x and y and z' shapes.  Takes idents rather than the
           binding records: those differ per declaration kind, and SML
           has no row polymorphism, so each caller selects its own. *)
        fun simpleIds detail kind ids =
            List.mapPartial
              (fn id => mkSym {name = id, detail = SOME detail, kind = kind,
                               span = span, children = []})
              ids
        fun thmSym triv attrs id children =
            mklist {name = id,
                    detail = kw (if triv then "Triviality" else "Theorem")
                                attrs,
                    kind = symConstant, span = span, children = children}
      in case dec of
        HOLTheory {id, ...} => simple "Theory" symModule id
      | HOLTheoremDecl {triv, id, attrs, quote, ...} =>
          thmSym triv attrs id (childrenOf quote)
      | HOLSimpleThm {triv, id, attrs, ...} => thmSym triv attrs id []
      | HOLDefinition {id, attrs, quote, ...} =>
          mklist {name = id, detail = kw "Definition" attrs,
                  kind = symFunction, span = span,
                  children = childrenOf quote}
      | HOLInductiveDecl {co, id, quote, ...} =>
          mklist {name = id,
                  detail = SOME (if co then "CoInductive" else "Inductive"),
                  kind = symFunction, span = span,
                  children = childrenOf quote}
      | HOLDatatype {quote, ...} =>
          List.mapPartial
            (fn (p, nm) => mkSym {name = (p, nm), detail = SOME "Datatype",
                                  kind = symEnum, span = span, children = []})
            (quoteTypeNames quote)
      | HOLQuoteDecl {id, ...} => simple "Quote" symVariable id
      | HOLType {overload, id, attrs, ...} => let
          val nm = case id of UnquotedId i => i | QuotedId (p, s) => (p, s)
          in mklist {name = nm,
                     detail = kwI (if overload then "Overload" else "Type") attrs,
                     kind = if overload then symOperator else symStruct,
                     span = span, children = []}
          end
      | HOLResume {id, ...} => simple "Resume" symConstant id
      | HOLFinalise {id, ...} => simple "Finalise" symConstant id
      | DecVal {elems = {args, ...}, ...} =>
          List.concat (map (fn {pat, ...} =>
              List.mapPartial
                (fn id => mkSym {name = id, detail = SOME "val",
                                 kind = symVariable, span = span,
                                 children = []})
                (rev (patNames pat []))) args)
      | DecFun {fvalbind = {args, ...}, ...} =>
          List.mapPartial
            (fn [] => NONE
              | ({pat, ...} :: _) =>
                (case funName pat of
                   NONE => NONE
                 | SOME id => mkSym {name = id, detail = SOME "fun",
                                     kind = symFunction, span = span,
                                     children = []}))
            args
      | DecType {tybind = {args, ...}, ...} =>
          List.mapPartial
            (fn {tycon, ...} => mkSym {name = tycon, detail = SOME "type",
                                       kind = symStruct, span = span,
                                       children = []})
            args
      | DecDatatype {datbind = {args, ...}, ...} =>
          List.mapPartial
            (fn {tycon, rhs, ...} =>
                mkSym {name = tycon, detail = SOME "datatype", kind = symEnum,
                       span = span,
                       children = case rhs of
                           DatvalElems cs =>
                             List.mapPartial
                               (fn {id, ...} =>
                                   mkSym {name = id, detail = NONE,
                                          kind = symConstructor,
                                          span = idSpan id, children = []})
                               cs
                         | _ => []})
            args
      | DecException {elems = {args, ...}, ...} => let
          fun exnId (ExnNew {id, ...}) = id
            | exnId (ExnReplicate {id, ...}) = id
          in List.concat (map (simple "exception" symConstructor o exnId) args)
          end
      | DecStructure {elems = {args, ...}, ...} =>
          simpleIds "structure" symModule (map #id args)
      | DecSignature {elems = {args, ...}, ...} =>
          simpleIds "signature" symInterface (map #id args)
      | DecFunctor {elems = {args, ...}, ...} =>
          simpleIds "functor" symModule (map #id args)
      (* `local ... in ... end' is scoping, not structure: its
         declarations belong beside their neighbours. *)
      | DecLocal {dec1, dec2, ...} =>
          List.concat (map symsOf dec1) @ List.concat (map symsOf dec2)
      | DecExpansion {orig, ...} => symsOf orig
      | _ => [] end
  and mklist r = case mkSym r of NONE => [] | SOME s => [s]
  and childrenOf quote =
      List.mapPartial
        (fn id => mkSym {name = id, detail = NONE, kind = symMethod,
                         span = idSpan id, children = []})
        (labelNames quote)
  fun loop acc =
      if !count > maxSymbols then rev acc
      else case parseDec () of
             NONE => rev acc
           | SOME dec => loop (List.revAppend (symsOf dec, acc))
  in loop [] handle _ => [] end

(* The modules a script names as its dependencies: the theories and
   libraries of its `Theory ... Ancestors ... Libs ...' header, plus the
   identifiers of any top-level `open' preceding the first real
   declaration (old-style scripts name their ancestors that way).  Each
   comes with the byte range of the name as written, so a load failure
   can be reported against the text that asked for it.  `Ancestors foo'
   loads the module `fooTheory'; `Libs bar' loads `bar'.

   `parseDec' streams, and we stop at the first declaration that is
   neither the header nor an `open', so this reads no further than the
   top of the file. *)
fun headerModules text = let
  val parseDec = bufferDecs text
  fun named suffix ((p, nm): HOLSourceAST.ident) =
      (nm ^ suffix, (p, p + size nm))
  fun elems suffix es = map (fn {id, ...} => named suffix id) es
  fun header (HOLSourceAST.HOLAncestors {elems = es, ...}) = elems "Theory" es
    | header (HOLSourceAST.HOLLibs {elems = es, ...}) = elems "" es
  fun loop acc =
    case parseDec () of
      NONE => rev acc
    | SOME (HOLSourceAST.HOLTheory {elems, ...}) =>
        loop (List.revAppend (List.concat (map header elems), acc))
    | SOME (HOLSourceAST.DecOpen {elems, ...}) =>
        loop (List.revAppend (map (named "") elems, acc))
    | SOME (HOLSourceAST.HOLLinePragmaWith _) => loop acc
    | SOME (HOLSourceAST.HOLFilePragmaWith _) => loop acc
    | SOME _ => rev acc
  in loop [] handle _ => [] end

(* `Meta.load' reports a module it cannot find or read by raising
   `Fail msg'; unwrap that, so a diagnostic reads as the message rather
   than as an exception constructor wrapped round it. *)
fun depExnMessage (Fail s) = s
  | depExnMessage e = exnMessage e

exception MalformedData

datatype req_id = Id of int | Str of string
datatype 'v result = Ok of 'v | Err of {code: int, message: string, data: 'v option}
datatype 'v message =
  Request of {id: req_id, method: string, params: 'v}
| Response of {id: req_id, result: 'v result}
| Notification of {method: string, params: 'v}

fun mkResponse id r = Response {id = id, result = r}
fun mkNotif method params = Notification {method = method, params = params}
fun mkErr code message = Err {code = code, message = message, data = NONE}

(* val ParseError = ~32700 *)
val InvalidRequest = ~32600
(* val MethodNotFound = ~32601 *)
val InvalidParams = ~32602
val InternalError = ~32603
(* val ServerErrorStart = ~32099 *)
(* val ServerErrorEnd = ~32000 *)
val ServerNotInitialized = ~32002
(* val UnknownErrorCode = ~32001 *)
(* val RequestCanceled = ~32800 *)
(* val ContentModified = ~32801 *)
(* val ServerCancelled = ~32802 *)
(* val RequestFailed = ~32803 *)

(* Column width a goal state is rendered at when the client does not
   say.  75 is what HOL's own goalstack printing uses. *)
val defaultGoalWidth = 75

val ErrorSeverity = 1
val WarnSeverity = 2
(* val InfoSeverity = 3 *)
(* val HintSeverity = 4 *)

datatype incremental = IncrNone | IncrChunk | IncrStream
datatype holdep_kind = HoldepNone | HoldepQuiet | HoldepList
datatype elab_on = ElabOnNone | ElabOnChange | ElabOnSave

local
  open JSONDecode JSON
  exception Invalid
in

val error = map3 (fn (code, message, data) => {code = code, message = message, data = data})
  (field "code" int, field "message" string, fieldO "data" raw)

val incr = ofRaw (fn jv =>
  case decode int jv of
    0 => IncrNone | 1 => IncrChunk | 2 => IncrStream
  | _ => raise JSONError (Invalid, jv))

val holdepKind = ofRaw (fn jv =>
  case decode int jv of
    0 => HoldepNone | 1 => HoldepQuiet | 2 => HoldepList
  | _ => raise JSONError (Invalid, jv))

val req_id = orElse (map Id int, map Str string)
val decMessage: JSON.value message decoder = ofRaw (fn jv =>
  case decode (fieldO "id" req_id) jv of
    NONE => Notification {
      method = decode (field "method" string) jv,
      params = decode (fieldD "params" raw NULL) jv}
  | SOME id => case decode (fieldO "method" string) jv of
    SOME method => Request {
      id = id, method = method,
      params = decode (fieldD "params" raw NULL) jv}
  | NONE => let
    val result = case decode (fieldO "error" error) jv of
      SOME e => Err e
    | NONE => Ok (decode (field "result" raw) jv )
    in Response {id = id, result = result} end)

val elabOn = ofRaw (fn jv =>
  case decode int jv of
    0 => ElabOnNone | 1 => ElabOnChange | 2 => ElabOnSave
  | _ => raise JSONError (Invalid, jv))

val position = tuple2 (field "line" int, field "character" int)
val range = tuple2 (field "start" position, field "end" position)

val textDocumentPositionParams =
  map2 (fn (uri, pos) => {uri = uri, pos = pos})
    (field "textDocument" (field "uri" string), field "position" position)

(* `$/hol/goalState': a position request plus the column width to
   render the goal state at.  Absent means `defaultGoalWidth', so a
   client that does not measure its pane gets what it always got. *)
val goalStateParams =
  map3 (fn (uri, pos, width) => {uri = uri, pos = pos, width = width})
    (field "textDocument" (field "uri" string), field "position" position,
     fieldD "width" int defaultGoalWidth)

val workspaceSymbolParams = field "query" string

val cancelParams = field "id" req_id

val evalParams = map4 (fn (uri, code, incr, holdep) =>
    {uri = uri, code = code, incr = incr, holdep = holdep})
  (field "uri" string, field "code" string, fieldD "incr" incr IncrNone,
    fieldD "holdep" holdepKind HoldepQuiet)

val textDocumentParams = field "textDocument" (
  map3 (fn (uri, version, text) => {uri = uri, version = version, text = text})
    (field "uri" string, field "version" int, field "text" string))

val versionedTextId = tuple2 (field "uri" string, field "version" int)

val changeEvent = map2 (fn (range, text) => {range = range, text = text})
  (fieldO "range" range, field "text" string)

val didChangeParams =
  map2 (fn ((uri, version), changes) => {uri = uri, version = version, changes = changes})
    (field "textDocument" versionedTextId, field "contentChanges" (array changeEvent))

val textDocumentId = field "textDocument" (field "uri" string)

end

fun encReqId (Id id) = encInt id
  | encReqId (Str s) = encString s

fun encMessage (Request {id, method, params: encode}) print = (
    print "{\"jsonrpc\":\"2.0\",\"id\":"; encReqId id print;
    print ",\"method\":"; encString method print;
    print ",\"params\":"; params print; print "}")
  | encMessage (Response {id, result}) print = (
    print "{\"jsonrpc\":\"2.0\",\"id\":"; encReqId id print;
    case result of
      Ok r => (print ",\"result\":"; r print)
    | Err {code, message, data} => (
      print ",\"error\":{\"code\":"; encInt code print;
      print ",\"message\":"; encString message print;
      case data of NONE => () | SOME data => (print ",\"data\":"; data print);
      print "}");
    print "}")
  | encMessage (Notification {method, params}) print = (
    print "{\"jsonrpc\":\"2.0\",\"method\":"; encString method print;
    print ",\"params\":"; params print; print "}")

structure Channel: sig
type 'a sender
type 'a receiver
exception Disconnected
val channel: unit -> 'a sender * 'a receiver
val send: 'a sender -> 'a -> unit
val closeSender: 'a sender -> exn option -> unit
val recv: 'a receiver -> 'a
end = struct

exception Disconnected
(* One condition variable serves both ends, so every wake-up must be a
   broadcast rather than a signal.  With more than one sender -- which
   the proof pool introduced, its workers announcing outcomes from their
   own threads while the compile thread also sends -- `signal` can hand
   the wake-up to the *other* sender instead of the receiver: that sender
   sees the slot still Full, waits again, and the signal is consumed with
   the receiver never woken.  Nobody signals after that.  Broadcasting
   makes each waiter re-test its own predicate, which the loops below
   already do. *)
datatype 'a slot = Empty | Full of 'a | Disconn of exn option
type 'a sender = ConditionVar.conditionVar * Mutex.mutex * 'a slot ref
type 'a receiver = 'a sender

fun channel () = let
  val x = (ConditionVar.conditionVar (), Mutex.mutex (), ref Empty)
  in (x, x) end

fun send (cvar, mutex, r) v = let
  fun loop () =
    case !r of
      Disconn (SOME e) => PolyML.Exception.reraise e
    | Disconn NONE => raise Disconnected
    | Empty => (r := Full v; Mutex.unlock mutex; ConditionVar.broadcast cvar)
    | Full _ => (ConditionVar.wait (cvar, mutex); loop ())
  in Mutex.lock mutex; loop () end

fun closeSender (cvar, mutex, r) e = let
  fun loop () =
    case !r of
      Disconn (SOME e) => PolyML.Exception.reraise e
    | Disconn NONE => raise Disconnected
    | Full _ => (ConditionVar.wait (cvar, mutex); loop ())
    | _ => (r := Disconn e; Mutex.unlock mutex; ConditionVar.broadcast cvar)
  in Mutex.lock mutex; loop () end

fun recv (cvar, mutex, r) = let
  fun loop () =
    case !r of
      Disconn (SOME e) => PolyML.Exception.reraise e
    | Disconn NONE => raise Disconnected
    | Full v => (r := Empty; Mutex.unlock mutex; ConditionVar.broadcast cvar; v)
    | Empty => (ConditionVar.wait (cvar, mutex); loop ())
  in Mutex.lock mutex; loop () end

end

type connection = {recv: unit -> JSON.value message, send: encode message -> unit}
fun stdioConnection (): connection = let
  val recv = let
    val (send, recv) = Channel.channel ()
    fun readHeaders sz =
      case TextIO.inputLine TextIO.stdIn of
        NONE => NONE
      | SOME line =>
        case String.fields (fn x => x = #":") line of
          ["\r\n"] => (case sz of SOME n => SOME n | NONE => raise MalformedData)
        | ["Content-Length", n] => ((
          if String.sub(n, 0) = #" " andalso String.substring(n, size n - 2, 2) = "\r\n" then
            case Int.fromString (String.substring (n, 1, size n - 3)) of
              SOME n => readHeaders (SOME n)
            | NONE => raise MalformedData
          else raise MalformedData)
          handle Subscript => raise MalformedData)
        | _ => readHeaders sz
    fun loop () =
      case readHeaders NONE of
        NONE => ()
      | SOME size => let
        val inp = TextIO.inputN (TextIO.stdIn, size)
        val msg = JSONDecode.decodeString decMessage inp
        in Channel.send send msg; loop () end
    fun readerThread () =
      (loop (); Channel.closeSender send NONE)
      handle e => (Channel.closeSender send (SOME e); PolyML.Exception.reraise e)
    val _ = Thread.fork (readerThread, [])
    in fn () => Channel.recv recv end

  (* Hijack the real stdOut for our JSON-RPC frames, and re-point
     TextIO.stdOut at TextIO.stdErr so USER code that writes via
     TextIO.stdOut (e.g. `val _ = print "..."` at top level in a HOL
     script) doesn't corrupt the wire. *)
  val lspOut = TextIO.getOutstream TextIO.stdOut
  val () = TextIO.setOutstream (TextIO.stdOut,
                                TextIO.getOutstream TextIO.stdErr)
  val send = let
    val (send, recv) = Channel.channel ()
    fun writerThread () = let
      val msg: encode message = Channel.recv recv
      val buf = ref []
      val () = encMessage msg (fn s => buf := s :: !buf)
      fun write (n, a :: buf, acc) = write (n + size a, buf, a :: acc)
        | write (n, [], acc) =
          TextIO.StreamIO.output (lspOut,
            String.concat ("Content-Length: " :: Int.toString n :: "\r\n\r\n" :: acc))
      in write (0, !buf, []); TextIO.StreamIO.flushOut lspOut;
         writerThread () end
       (* An encode-time exception must not kill the writer: the
          channel would stay Full and every send would hang. *)
       handle e => (
         TextIO.output (TextIO.stdErr,
           "[LSP-writer] dropping message; encode raised: " ^ exnMessage e ^ "\n");
         TextIO.flushOut TextIO.stdErr;
         writerThread ())
    val _ = Thread.fork (writerThread, [])
    in Channel.send send end
  in {send = send, recv = recv} end

exception ProtocolError

fun initialize ({send, recv}:connection) capabilitiesFor = let
  fun init () =
    case recv () of
      Request {method = "initialize", id, params} => (id, params)
    | Request {id, ...} => (
      send (mkResponse id (mkErr ServerNotInitialized "expected initialize request"));
      init ())
    | Notification {method = "exit", ...} => raise ProtocolError
    | Notification _ => init ()
    | _ => raise ProtocolError
  val (id, params) = init ()
  val _ = send (mkResponse id (Ok (fn print => (
    print "{\"capabilities\":"; print (capabilitiesFor params);
    print "}"))))
  val _ = case recv () of
    Notification {method = "initialized", ...} => ()
  | _ => raise ProtocolError
  in params end

fun encPosLC lines = encPosition o getLineCol lines
val encRangeLC = encRange o encPosLC
fun locToRange ({startPosition,endPosition,...}:PolyML.location) =
  (FixedInt.toInt startPosition, FixedInt.toInt endPosition)
(* fun encLocLC lines = encRangeLC lines o locToRange *)

(* DocumentSymbol: hierarchical, with `children' and `detail' omitted
   when empty so the wire form stays the shape clients expect. *)
fun encDocumentSymbol lines (Sym {name, detail, kind, span, selSpan,
                                  children}) print = (
    print "{\"name\":"; encString name print;
    (case detail of
       NONE => ()
     | SOME d => (print ",\"detail\":"; encString d print));
    print ",\"kind\":"; encInt kind print;
    print ",\"range\":"; encRangeLC lines span print;
    print ",\"selectionRange\":"; encRangeLC lines selSpan print;
    (case children of
       [] => ()
     | cs => (print ",\"children\":";
              encArray (encDocumentSymbol lines) cs print));
    print "}")

(* SymbolInformation: the flat form, for a client that does not
   advertise hierarchical support, and the only form `workspace/symbol'
   has. *)
fun encSymbolInformation uri lines container (Sym {name, kind, span, ...})
                         print = (
    print "{\"name\":"; encString name print;
    print ",\"kind\":"; encInt kind print;
    (case container of
       NONE => ()
     | SOME c => (print ",\"containerName\":"; encString c print));
    print ",\"location\":{\"uri\":"; encString uri print;
    print ",\"range\":"; encRangeLC lines span print;
    print "}}")

(* Flatten for the same reason: `containerName' is how the flat form
   says what a child belonged to. *)
fun flatSymbols syms = let
  fun go parent (sym as Sym {name, children, ...}) acc =
      List.foldl (fn (c, a) => go (SOME name) c a)
                 ((parent, sym) :: acc) children
  in rev (List.foldl (fn (s, a) => go NONE s a) [] syms) end

fun encPretty textWidth pp print = let
  fun print' s = encStringContents s print
  in print "\""; PolyML.prettyPrint (print', textWidth) pp; print "\"" end

fun encDArray encode ls print = case DArray.size ls of
    0 => print "[]"
  | n => let
    fun inner i = if i < n then
      (print ","; encode (DArray.sub (ls, i)) print; inner (i+1))
    else print "]"
    in print "["; encode (DArray.sub (ls, 0)) print; inner 1 end

fun lastIndexOf c s = let
  fun go i = if i = 0 then ~1 else case i - 1 of i' =>
    if c = String.sub (s, i') then i' else go i'
  in go (String.size s) end

fun splitOn c s = let
  fun loop i j out =
    if i = 0 then String.substring (s, i, j - i) :: out
    else case i - 1 of i' =>
      if c = String.sub (s, i')
      then loop i' i' (String.substring (s, i, j - i) :: out)
      else loop i' j out
  in case String.size s of sz => loop sz sz [] end

(* `extend_path_with_includes` reads `getDir()`'s Holmakefile and
   blindly appends its INCLUDES to `Meta.loadPath` with no dedup
   against existing entries.  Cache each canonical dir we've
   already walked so per-didOpen calls don't grow the load path
   linearly in the number of opened files. *)
val walkedDirs : string Binaryset.set ref =
  ref (Binaryset.empty String.compare)

fun walkIncludesFrom dir = let
  val abs = OS.Path.mkAbsolute {path = dir, relativeTo = OS.FileSys.getDir()}
             handle _ => dir
in
  if Binaryset.member (!walkedDirs, abs) then ()
  else let
    val saved = OS.FileSys.getDir()
    fun restore () = OS.FileSys.chDir saved handle _ => ()
  in
    (OS.FileSys.chDir dir;
     ReadHMF.extend_path_with_includes
       {verbosity = 0, lpref = Meta.loadPath};
     walkedDirs := Binaryset.add (!walkedDirs, abs);
     restore ())
    handle _ => restore ()
  end
end

fun uriToPath uri =
  if String.isPrefix "file://" uri
  then SOME (String.extract (uri, 7, NONE)) else NONE

(* `hol.ML` at boot preloads project_dirs / external_includes from
   cwd's `holproject.toml`; this handler catches files whose
   Holmakefile chain isn't reached that way -- HOL4 dev under a
   `holmake = false` toml, or files opened outside any holproject. *)
fun augmentLoadPathForUri uri = case uriToPath uri of
    NONE => ()
  | SOME path => walkIncludesFrom (OS.Path.dir path)

fun start {diag, dbg} = let
  val _ = PolyML.print_depth 100
  val conn as {send, recv} = stdioConnection ()
  (* LSP 3.17 position encoding.  Server-side buffers and offsets count
     bytes, so utf-8 is what this server would rather speak: it costs
     nothing and an edit crossing a multi-byte character (`⇒`, `∧`)
     cannot land mid-codepoint and corrupt the buffer -- which surfaces
     as a HOL "Lexical error" on the first byte of the split character.

     But the choice is the client's to offer and ours to make from what
     it offers, and declaring utf-8 regardless is not a way of getting
     it: vscode-languageclient hardcodes `["utf-16"]' and throws on any
     other answer, so its users had the encoding stripped back out and
     every position off by (bytes - code units) on any line with a
     non-ASCII character before it.  Take utf-8 when offered -- eglot
     offers `["utf-32" "utf-8" "utf-16"]' -- and otherwise convert, so
     the client that cannot count bytes need not.

     A client that offers nothing gets utf-16, which is what the spec
     says its silence means. *)
  val clientEncodings = fn params =>
      JSONDecode.decode
        (JSONDecode.fieldD "capabilities"
           (JSONDecode.fieldD "general"
              (JSONDecode.fieldD "positionEncodings"
                 (JSONDecode.array JSONDecode.string) []) []) [])
        params
      handle _ => []
  (* Whether the client takes the nested DocumentSymbol form.  The spec
     says a silent client gets the flat one. *)
  val hierarchicalSymbols = ref false
  fun capabilitiesFor params = let
    val utf8 = List.exists (fn e => e = "utf-8")
                           (clientEncodings params)
    val () = LSPExtension.setUTF16Positions (not utf8)
    val () = hierarchicalSymbols :=
      (JSONDecode.decode
         (JSONDecode.fieldD "capabilities"
            (JSONDecode.fieldD "textDocument"
               (JSONDecode.fieldD "documentSymbol"
                  (JSONDecode.fieldD "hierarchicalDocumentSymbolSupport"
                     JSONDecode.bool false) false) false) false)
         params
       handle _ => false)
    in concat [
      "{\"textDocumentSync\":2", (* 2 = Incremental; applyEdit supports it *)
      ",\"positionEncoding\":",
      if utf8 then "\"utf-8\"" else "\"utf-16\"",
      ",\"hoverProvider\":true",
      ",\"definitionProvider\":true",
      ",\"documentSymbolProvider\":true",
      ",\"workspaceSymbolProvider\":true",
      ",\"completionProvider\":{\"triggerCharacters\":[\".\"]}",
      (* No `referencesProvider'.  It was advertised for a long time
         with no handler behind it, so a client that believed it got
         "unknown method".  An honest implementation is not available
         either: Poly records references only within the compilation
         unit it is compiling, and HOL has no index of which proofs
         cite a theorem -- `DB.revlookup' says where a theorem was
         stored, not who cites it. *)
      "}"]
    end
  val _ (*clientCapabilities*) = initialize conn capabilitiesFor
  fun logMessage str =
    send (Notification {
      method = "window/logMessage",
      params = fn print => (
        print "{\"type\":4,\"message\":"; encString str print; print "}")})
  (* type 2 = Warning; unlike `logMessage` this one is meant to be
     seen without opening the log. *)
  fun warnUser str =
    send (Notification {
      method = "window/showMessage",
      params = fn print => (
        print "{\"type\":2,\"message\":"; encString str print; print "}")})
  val _ = diag "started"
  val _ = logMessage "started"
  val _ = markServerStarted ()

  (* A server process is bound to the first file it opens.  A second
     file cannot be served correctly: its ancestors have to be in the
     theory graph, only loading puts them there, and loading a theory
     seals it (`Theory.load_complete'), so an ancestor already loaded
     for the first file can be neither re-read nor withdrawn.  The
     result is a broken environment for the second file -- wrong goals
     and dead hovers -- with nothing in either file to explain it.

     Clients are expected to run one server per buffer; `hol-lsp-enable'
     does this by giving each buffer its own eglot project.  Say so
     when a client does otherwise, rather than answering with quiet
     nonsense.

     Only `*Script.sml' takes the binding.  A `.sig' or an ordinary
     `.sml' declares no theory of its own, and editors routinely open
     them alongside a script -- the hol4-vscode selector matches the
     whole language, so it sends every one of them.  Letting those
     claim the process would hand it to whichever file the client
     happened to sync first and then report the user's actual script
     as the offender.

     One warning per process, not per file: a client that opens N
     scripts syncs them all at once (vscode-languageclient replays
     `didOpen' for every already-open match when it registers), and N
     toasts is a worse way to learn one fact.  Every offending file
     still reaches the log. *)
  val boundUri : string option ref = ref NONE
  val warnedOnce = ref false
  fun isScriptUri uri = String.isSuffix "Script.sml" uri
  (* Whether this file may run a compile.  Everything HOL-side --
     the Context, the sealed-theory set, `Meta.loadedMods' -- is
     process-global, so a second file's compile does not merely answer
     for itself: it rewinds and re-establishes the very state the bound
     file's goals and hovers are read from.  Refusing keeps the
     isolation guarantee a property of the code and not only of the
     client's willingness to start one process per script.

     The test is the binding, not `isScriptUri': a file that never
     claimed the binding is welcome, and much of the test suite opens
     a second such file and expects it to compile. *)
  fun mayCompile uri =
    case !boundUri of NONE => true | SOME first => first = uri
  fun checkSingleFile uri =
    if not (isScriptUri uri) then ()
    else case !boundUri of
      NONE => boundUri := SOME uri
    | SOME first =>
      if first = uri then ()
      else let
        val msg = String.concat [
          "This HOL server is bound to ", first,
          ".  Goal states and hovers for ", uri,
          " will be unreliable: one server can serve only one script, ",
          "and closing the first does not release it.  Configure your ",
          "editor to start a server per buffer -- see ",
          "tools-poly/lsp/README.md, \"One server per buffer\"."]
        in
          logMessage msg;
          if !warnedOnce then () else (warnedOnce := true; warnUser msg)
        end

  val textWidth = 100 (* configure? *)
  val printDepth = 100

  val jobs = let
    val mutex = Mutex.mutex ()
    val jobs = ref []
    fun modify f = let
      val _ = Mutex.lock mutex
      val j = !jobs
      val _ = jobs := f j
      val _ = Mutex.unlock mutex
      in j end
    in modify end

  fun spawnJobCore id job = let
    val jobThread = Thread.fork (job, [])
    in jobs (fn js => (id, jobThread) :: js); () end

  fun spawnJob id params decode f = spawnJobCore id (fn () => let
    val result = f (JSONDecode.decode decode params) handle
      JSONErrors.JSONError _ => mkErr InvalidParams "json decode failed"
    | e => mkErr InternalError (exnMessage e)
    val _ = send (mkResponse id result)
    val _ = jobs (fn js => let
      fun go (_, []) = js
        | go (acc, j::js) = if #1 j = id then List.revAppend (acc, js) else go (j::acc, js)
      in go ([], js) end)
    in () end)

  val elabOnRef = ref ElabOnChange
  val holdepMode = ref HoldepQuiet

  (* Server-initiated request ids and progress tokens for
     window/workDoneProgress. *)
  val nextRequestId = ref 100000
  fun allocRequestId () =
      !nextRequestId before nextRequestId := !nextRequestId + 1
  val progressIdCounter = ref 0

  datatype report =
    Error of {hard: bool, pos: range, msg: encode}
  | CompilerOut of int * string list
  | ToplevelOut of int * string list
  | Progress of int
  | Completed
  | Interrupted

  (* Per-dec snapshot; see `parse_data.declSnapshots` below.  A resume
     to `endByte` seeds the new compile with `builtTrees` and `plugins`
     from this snapshot, restores HOL state via `compileSnap`, and
     uses `diags` as the frozen prefix of the diagnostic list. *)
  type declSnapshot = {
    endByte     : int,
    builtTrees  : HOL_IDE.built list,
    diags       : report DArray.darray,
    plugins     : plugin_data,
    compileSnap : LSPExtension.compileSnap }

  type parse_data = {
    done: bool,
    pos: int,
    builtTrees: HOL_IDE.built list,
    diags: report DArray.darray,
    plugins: plugin_data,
    (* Newest-first list of per-dec snapshots taken by the current /
       last-completed compile.  Consulted by `startCompile` to resume
       from the largest snapshot with `endByte <= minEditOffset`
       instead of restarting from byte 0. *)
    declSnapshots: declSnapshot list}
  fun emptyParseData n: parse_data = {
    done = false, pos = 0, builtTrees = [],
    diags = DArray.new (n, Completed),
    plugins = emptyPluginData,
    declSnapshots = [] }
  (* Preserve `declSnapshots` from `p` but zero the rest.  Used by
     `applyEdit` so a `didChange` doesn't discard the snapshots the
     previous compile computed. *)
  fun carryOverSnapshots ({declSnapshots, ...}:parse_data): parse_data = {
    done = false, pos = 0, builtTrees = [],
    diags = DArray.new (0, Completed),
    plugins = emptyPluginData,
    declSnapshots = declSnapshots }
  fun addBuiltTree t {done, pos, builtTrees, diags, plugins, declSnapshots} =
    {done = done, pos = pos, builtTrees = t :: builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun setParsePos pos {done, pos = _, builtTrees, diags, plugins, declSnapshots} =
    {done = done, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun setParseDone pos {done = _, pos = _, builtTrees, diags, plugins, declSnapshots} =
    {done = true, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun setPlugins plugins {done, pos, builtTrees, diags, plugins = _, declSnapshots} =
    {done = done, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = declSnapshots}
  fun addDeclSnapshot snap {done, pos, builtTrees, diags, plugins, declSnapshots} =
    {done = done, pos = pos, builtTrees = builtTrees, diags = diags,
     plugins = plugins, declSnapshots = snap :: declSnapshots}

  (* Why a file is not being compiled: the declared dependency list
     whose change clears the block, and what went wrong. *)
  type deps_blocked = {mods: string list, message: string}

  type text_data = {text: string, version: int, lines: lines}
  type compile_data = {parse: parse_data ref, text: text_data,
                       thread: Thread.thread, cancelled: bool ref}
  type file_data = {
    compile: compile_data option ref,
    lastTrees: {parse: parse_data, text: text_data} ref,
    (* debounce epoch: incremented on didChange and at startCompile
       entry.  scheduleCompile's forked thread captures the epoch and
       only fires startCompile if its epoch still matches when it
       wakes up.  Rapid-fire edits fork many threads but only the
       last (whose epoch survives to wake time) actually compiles. *)
    debounce: int ref,
    (* Rolling minimum edit offset across `applyEdit` batches since
       the last successful compile.  `startCompile` picks the largest
       snapshot in `lastTrees.parse.declSnapshots` with `endByte <=
       !minEditOffset` (falling back to a full boot-restore if none).
       `NONE` means no edit info is available (fresh file, or a
       previous compile completed and cleared it) — treated as 0
       (full restart). *)
    minEditOffset: int option ref,
    (* Runtime-diagnostic squiggles the walker has observed since
       the last compile: keyed by theorem name, value is the
       Error report for the failed leaf.  Fresh compiles clear
       these; a successful walker query for a theorem removes its
       entry so a user-fix removes the squiggle without waiting
       for the next compile. *)
    walkerDiags: (string, report) Binarymap.dict ref,
    (* Set when a compile was abandoned because the file's declared
       dependencies -- the modules of `headerModules' -- could not be
       loaded; it carries that module list.  See `startCompile' for what
       lifts the block. *)
    depsBlocked: deps_blocked option ref,
    (* The outline for this buffer, with the text version it was parsed
       from.  documentSymbol is asked on every edit and
       `workspace/symbol' re-asks for every open buffer on every
       keystroke of the search box, so parsing per request would repeat
       work the text has not invalidated. *)
    symbols: (int * symbol list) option ref,
    (* The compile thread's LSP namespace layer, as of the last
       declaration it finished.  The layer is thread-local
       (lsp_namespace.ML), so a request thread answering completion sees
       globals only until it installs this.  Captured even when the
       compile has errors: a file that does not compile is exactly when
       its own names are worth offering. *)
    nsLayer: (unit -> unit) option ref,
    (* Names in scope, with the `nsLayer' generation they came from.
       `#allVal' and friends walk the whole global namespace and filter
       it, which is far too much to redo per keystroke; the layer only
       changes when a declaration finishes compiling. *)
    nsGen: int ref,
    nsNames: (int * (string * int) list) option ref}
  local
    val mutex = Mutex.mutex ()
    val fileInfo = ref (Binarymap.mkDict String.compare: (string, file_data) Binarymap.dict)
  in
    fun withFileInfo f = (Mutex.lock mutex; let
      val (v, r) = f (!fileInfo)
      val _ = fileInfo := v
      val _ = Mutex.unlock mutex
      in r end
      handle e => (Mutex.unlock mutex; PolyML.Exception.reraise e))
  end

  fun newFile text version = let
    val text = {text = text, version = version, lines = mkLineCounter text}
    in {compile = ref NONE, lastTrees = ref {parse = emptyParseData 0, text = text},
        debounce = ref 0, minEditOffset = ref NONE,
        walkerDiags = ref (Binarymap.mkDict String.compare),
        depsBlocked = ref NONE, symbols = ref NONE, nsLayer = ref NONE,
        nsGen = ref 0, nsNames = ref NONE} end

  (* Cooperative cancel: signal the flag, which the compile thread
     checks at each Progress event and raises Thread.Interrupt.  We
     can't use Thread.interrupt directly for two reasons: the compile
     thread runs InterruptDefer (so Poly wouldn't deliver it), and
     HOL's tactic-level `handle _ =>` would swallow it mid-proof
     without stopping the wider compile.

     stopCompile does NOT wait for the thread to exit — it's called
     from the recv thread on every didChange, and a stuck compile
     (e.g., HOL's parser recovering from an unterminated `Theorem`)
     would otherwise block recv, freezing hover requests and further
     didChanges.  The `cancelled` flag doubles as a "no longer
     current" marker: the compile thread checks it before writing
     lastTrees so a stale finish can't clobber the new state. *)
  fun stopCompile r = case !r of
    NONE => ()
  | SOME {cancelled, ...} => (r := NONE; cancelled := true)

  (* Push `off` into the rolling min-edit tracker; a later `startCompile`
     consults this to decide whether to resume from a snapshot.  An edit
     is not the only thing that can move it: so can discovering that a
     declaration's proof suspends. *)
  fun bumpMinEdit minEditOffset off =
      case !minEditOffset of
        NONE => minEditOffset := SOME off
      | SOME m => if off < m then minEditOffset := SOME off else ()

  fun commonPrefixLen (a, b) = let
    val n = Int.min (size a, size b)
    fun go i = if i >= n orelse String.sub (a, i) <> String.sub (b, i) then i
               else go (i + 1)
    in go 0 end

  fun applyEdit ({compile, lastTrees, minEditOffset, ...}:file_data) version changes = let
    val _ = stopCompile compile
    fun getLines text NONE = mkLineCounter text
      | getLines _ (SOME lines) = lines
    val bumpMin = bumpMinEdit minEditOffset
    (* The old `parse` value is carried through the fold so we can
       preserve its `declSnapshots` on each step (via
       `carryOverSnapshots`).

       A full-text replace (`range = NONE`) used to drop the
       snapshots and push min-edit-offset to 0, on the grounds that
       their `endByte` offsets no longer index anything meaningful.
       That holds only past the point where the two texts diverge --
       and a whole-document replace is typically a revert or a
       reformat, where they diverge late or not at all.  Sending
       those down the from-scratch path recompiled the file in a
       process that has already run its `Ancestors', which does not
       give the same result: a `C-x v u' left the goal state
       reporting tactics as failing that had just worked.

       So take the offset from the texts rather than from the edit:
       the first byte at which old and new differ.  That is never
       earlier than the edit's own start -- everything before it is
       untouched by construction -- and is often much later, because
       a replacement usually re-inserts what it replaced.  It matters
       for a range as well as for a whole-document change: reverting
       a buffer has Emacs report one change spanning the entire
       document, whose `from' is 0 like any other. *)
    fun applyText [] data = data
      | applyText ({range = NONE, text}::cs) (parse, base, _) =
        (bumpMin (commonPrefixLen (base, text));
         applyText cs (carryOverSnapshots parse, text, NONE))
      | applyText ({range = SOME (from, to), text}::cs) (parse, base, lines) = let
        val lines = getLines base lines
        val (from, to) = (fromLineCol lines from, fromLineCol lines to)
        val text = Substring.concat [
          Substring.substring (base, 0, from),
          Substring.full text,
          Substring.substring (base, to, size base - to)]
        val _ = bumpMin (commonPrefixLen (base, text))
        in applyText cs (carryOverSnapshots parse, text, NONE) end
    val {parse, text = {text, lines, version = _}} = !lastTrees
    val (parse, text, lines) = applyText changes (parse, text, SOME lines)
    val text = {text = text, lines = getLines text lines, version = version}
    in lastTrees := {parse = parse, text = text} end

  fun exceptionMessage (exn: exn) =
    PolyML.PrettyBlock(0, false, [], [
      PolyML.PrettyBlock(0, false, [], [PolyML.PrettyString "Exception"]),
      PolyML.PrettyBreak(1, 3),
      PolyML.prettyRepresentation(exn, printDepth),
      PolyML.PrettyBreak(1, 3),
      PolyML.PrettyString "raised"])

  fun exnToReport i e = Error {hard = true,
    pos = case PolyML.Exception.exceptionLocation e of
      (* A HOL kernel exception (raised from Theory.new_theory or
         similar) carries a location inside the HOL source that
         raised it — mapping its byte offset via the current file's
         `lines` table produces a nonsense line.  Trust the
         location only when its `file` field is empty (meaning
         "the anonymous compile unit we're currently feeding to
         PolyML.compiler"). *)
      SOME (l as {file = "", ...}) => locToRange l
    | _ => (i, i),
    msg = encPretty textWidth (exceptionMessage e)}

  fun mergeInto msg buf =
    case (msg, DArray.last buf) of
      (CompilerOut (pos', [s]), SOME (CompilerOut (pos, ss))) =>
      if pos = pos' then DArray.setLast (buf, CompilerOut (pos, s :: ss))
      else DArray.push (buf, msg)
    | (ToplevelOut (pos', [s]), SOME (ToplevelOut (pos, ss))) =>
      if pos = pos' then DArray.setLast (buf, ToplevelOut (pos, s :: ss))
      else DArray.push (buf, msg)
    | _ => DArray.push (buf, msg)

  fun getHoldep text = let
    val {read, ...} = HOLSource.stringToReader {quietOpen = false, print = fn _ => ()} text
    in
      Binarymap.foldr (fn (a, _, r) => a :: r) [] (Holdep_tokens.reader_deps ("", read))
      handle _ => []
    end

  fun compileForReport uri code startByte lastPos builtTree onDecCompleted
                       report = let
    (* A deferred proof belongs to the declaration being compiled when it
       is enqueued, so record that declaration's start as each one
       begins.  Elaboration is single-threaded, so a plain ref is
       enough. *)
    fun onDecStarted off = LSPExtension.currentProofOffset := off
    val _ = HOL_IDE.initialize {
      text = code,
      filename = uri,
      (* `unclosed quotation` / `expected ...` almost always mean an
         in-progress edit; surface those as Warning, not Error. *)
      parseError = fn pos => fn s => let
        val soft = String.isSubstring "unclosed quotation" s
                   orelse String.isSubstring "expected" s
      in report (Error {hard = not soft, pos = pos, msg = encString s}) end,
      compilerOut = fn s => report (CompilerOut (!lastPos, [s])),
      toplevelOut = fn s => report (ToplevelOut (!lastPos, [s])),
      progress = fn i => (lastPos := i; report (Progress i)),
      error = fn {hard, location, message, ...} => report (Error {
        hard = hard, pos = locToRange location, msg = encPretty textWidth message}),
      runtimeExn = fn e => report (exnToReport (!lastPos) e),
      builtTree = builtTree,
      onDecStarted = onDecStarted,
      onDecCompleted = onDecCompleted,
      startByte = startByte }
    in lastPos := size code end

  (* Materialise an `encode` (`(string -> unit) -> unit`) into a plain
     string.  Used to build dedup keys for Error reports whose `msg`
     is a pretty-printer callback. *)
  fun encodeToString enc = let
    val buf = ref []
    fun sink s = buf := s :: !buf
    val () = enc sink
    in String.concat (rev (!buf)) end

  (* Drop later Error reports whose (pos, msg) matches an earlier one.
     A single mis-typed dec often triggers multiple parser recovery
     passes each emitting the same "expected 'QED'" / "expected an
     expression" pair -- users don't need to see them twice.  Non-
     Error reports pass through unchanged. *)
  fun dedupReports d = let
    val seen = ref (Binaryset.empty String.compare)
    val out = DArray.new (DArray.size d, Completed)
    fun step r = case r of
        Error {pos = (s, e), msg, ...} =>
          let val k = Int.toString s ^ ":" ^ Int.toString e ^ ":"
                      ^ encodeToString msg
          in if Binaryset.member (!seen, k) then ()
             else (seen := Binaryset.add (!seen, k);
                   DArray.push (out, r))
          end
      | _ => DArray.push (out, r)
    val () = DArray.app step d
    in out end

  (* Emit `$/proofStates` for `uri`: one change in what the
     proof-checking pool is doing.

       {"uri": ..., "states": [{"pos": {"line": l, "character": c},
                                "name": "foo",
                                "status": "checking" | "proved" | "failed"
                                        | "suspended" | "diverged"
                                        | "cheated",
                                "detail": "..."}, ...]}

     `detail` is present only for `failed`, `suspended` and `diverged`.

     A transition stream, not a snapshot: merge each state in, keyed by
     `pos`.  The pool announces every change from the thread that causes
     it -- `checking` when a proof is forked, its verdict when it
     settles, `cheated` when its entry is dropped -- so a client that
     accumulates them tracks the pool exactly.

     There is deliberately no full-state message.  Sending one cannot be
     made correct: the state has to be sampled and only then sent, so a
     worker settling in between has its newer verdict overwritten by the
     older sample.  Per proof the transitions are ordered, which is what
     a client needs.

     Positions shift when the buffer is edited, but an edit invalidates
     the proofs it reaches, and those are announced as `cheated` under
     their old positions before any new ones are announced.

     A position rather than a range: the pool identifies a proof by the
     byte its declaration starts at, which is all it needs for
     cancellation, and a client wanting to decorate the whole
     Theorem-QED block can find the end itself.  Ranges can be added if
     a client would rather not.

     A declaration *absent* from the list is one the pool is not working
     on.  Per the state model in LSPExtension: if the compile has reached
     it, it is `cheated` -- statement and tactic type-check, and the
     proof is taken on trust; if not, it is `unseen`.  The server does
     not distinguish those on the wire, having no list of declarations
     past the compile frontier; a client can tell them apart from its own
     parse and the last `$/compileProgress`. *)
  fun sendProofStates uri lines states = let
    fun statusName st =
        case st of
            LSPExtension.Unseen => "unseen"
          | LSPExtension.Cheated => "cheated"
          | LSPExtension.Checking => "checking"
          | LSPExtension.Proved => "proved"
          | LSPExtension.Failed _ => "failed"
          | LSPExtension.Suspended _ => "suspended"
          | LSPExtension.Diverged _ => "diverged"
    fun detailOf st =
        case st of
            LSPExtension.Failed m => SOME m
          | LSPExtension.Suspended m => SOME m
          | LSPExtension.Diverged m => SOME m
          | _ => NONE
    fun encState ({site, offset, status} : LSPExtension.proof_state) print = (
        print "{\"pos\":"; encPosLC lines offset print;
        print ",\"name\":"; encString site print;
        print ",\"status\":"; encString (statusName status) print;
        (case detailOf status of
             NONE => ()
           | SOME m => (print ",\"detail\":"; encString m print));
        print "}")
    in
      send (mkNotif "$/proofStates" (fn print => (
        print "{\"uri\":"; encString uri print;
        print ",\"states\":"; encArray encState states print;
        print "}")))
    end

  (* Give up on the proofs a compile is about to invalidate, and tell the
     client.  `resumeStart` is where it will re-elaborate from, NONE
     meaning the whole file.

     `inProofBody` is the declaration containing the edit, when the edit
     lies inside a `Proof ... QED` body.  That case is worth separating
     out, because a tactic contributes nothing to the elaboration
     context: every later declaration's statement parses to the same term
     against the same context, so the proofs already running on them are
     still the right proofs and only the edited one need be abandoned.
     The pass that follows re-enqueues all of them anyway; `check`
     recognises the ones already in progress and leaves them running
     rather than forking a second copy.

     Text being unchanged is *not* on its own enough to justify this.  A
     declaration below an edited *definition* also has unchanged text,
     but its context has changed, so its statement can parse to a
     different term.  Hence the test is "the edit is confined to a
     tactic", not "this declaration was not touched".

     The declaration's start is safe to compare against offsets recorded
     in the previous pass for the same reason the resume decision is: an
     edit cannot move anything before itself. *)
  fun invalidateProofs {resumeStart, inProofBody} = (
    case (inProofBody, resumeStart) of
        (SOME d, _) => !LSPExtension.cancelProofAt d
      | (NONE, NONE) => !LSPExtension.cancelAllProofs ()
      | (NONE, SOME b) => !LSPExtension.cancelProofsAtOrAfter b)

  (* The declaration whose `Proof ... QED` body contains the edit, if the
     edit is in one.  `findEnclosingTheorem` answers exactly that and is
     the same walk the goal-state handler does.  Its `compileDone`
     argument only reaches the `theorem_context` it builds, which we
     discard, so anything will do here. *)
  fun proofBodyAt text off =
      (case off of
           NONE => NONE
         | SOME b => (case findEnclosingTheorem false text b of
                          SOME (decStart, _) => SOME decStart
                        | NONE => NONE))
      handle Empty => NONE

  (* Tell the client the file is not being compiled, and why.  Sent
     when the block is first recorded and again on each later edit that
     leaves the declared dependencies unchanged, so a client can show
     the state without having to remember it. *)
  fun sendDepsBlocked uri ({mods, message}: deps_blocked) =
      send (mkNotif "$/compileBlocked" (fn print => (
        print "{\"uri\":"; encString uri print;
        print ",\"modules\":"; encArray encString mods print;
        print ",\"message\":"; encString message print;
        print "}")))

  (* Record the block, and announce it once where the user will see it
     without opening the LSP log: the file simply going quiet is the
     one thing worse than the cascade of squiggles this replaces. *)
  fun markDepsBlocked uri ({depsBlocked, ...}:file_data) b = let
    (* Only the first block says so out loud.  A user fixing the header
       gets a compile attempt per edit, and most of those attempts fail
       again while the name is half-typed; one warning per keystroke is
       worse than the silence it is there to explain. *)
    val fresh = not (isSome (!depsBlocked))
    in
      depsBlocked := SOME b;
      sendDepsBlocked uri b;
      if fresh then
        warnUser ("HOL: not compiling " ^ OS.Path.file uri ^ ": "
                  ^ #message b ^ " (edit the Ancestors / Libs header to "
                  ^ "try again)")
      else ()
    end

  (* Emit publishDiagnostics for `uri` combining the last-completed
     compile's diagnostics and any walker-observed runtime squiggles. *)
  fun publishAllDiagnostics uri
                            ({lastTrees, walkerDiags, ...}:file_data) = let
    val {text, parse} = !lastTrees
    val {lines, version, ...} = text
    val compileDiags = #diags parse
    val wd = !walkerDiags
    val total = DArray.size compileDiags + Binarymap.numItems wd
    val snapshot = DArray.clone (compileDiags, total)
    val _ = Binarymap.app (fn (_, r) => DArray.push (snapshot, r)) wd
    val snapshot = dedupReports snapshot
    fun encDiag (Error {hard, pos, msg}) print = (
        print "{\"range\":"; encRangeLC lines pos print;
        print ",\"severity\":";
        encInt (if hard then ErrorSeverity else WarnSeverity) print;
        print ",\"message\":"; msg print; print "}")
      | encDiag _ _ = raise Fail "unexpected report kind"
  in
    send (mkNotif "textDocument/publishDiagnostics" (fn print => (
      print "{\"uri\":"; encString uri print;
      print ",\"version\":"; encInt version print;
      print ",\"diagnostics\":"; encDArray encDiag snapshot print;
      print "}")))
  end

  fun startCompile uri (v as {compile, lastTrees, debounce, minEditOffset,
                              walkerDiags, depsBlocked, nsLayer, nsGen,
                              ...}:file_data) =
    (* Every route to a compile comes through here -- didOpen,
       didChange's debounce, didSave, `$/hol/retryCompile', and the
       proof pool's retract -- so this is the one place the binding has
       to be checked. *)
    if not (mayCompile uri) then
      logMessage ("not compiling " ^ uri ^
                  ": this server is bound to another script")
    else (
    (* Invalidate any pending scheduleCompile thread: their epoch
       check will see the new value and self-abort. *)
    debounce := !debounce + 1;
    (* Runtime squiggles from the walker are always stale w.r.t. the
       new compile -- clear them so a fix removes squiggles even
       before the user visits the theorem to re-run the walker. *)
    walkerDiags := Binarymap.mkDict String.compare;
    let
    (* The dependencies the file declares, and where it names them.
       A failure to load one of these is fatal to the whole file, so
       it is tracked apart from the rest: `getHoldep' reports every
       module the text mentions, including basis structures and ones
       the file declares itself, and "Cannot find file" for those is
       routine and harmless. *)
    val declared = headerModules (#text (#text (!lastTrees)))
    val declaredNames = map #1 declared
    (* A file whose declared dependencies did not load gets no compile
       at all until that list changes.  The check is the list itself
       rather than a general "has the file changed": nothing the user
       types in the body can make a missing ancestor appear, so
       recompiling on it would redraw the same diagnostics at the cost
       of a whole elaboration, and the goal-state walker and hover
       would answer from an environment that cannot be right.  Editing
       the header is the one edit that can change the answer -- and it
       is also how a user retries after building the ancestor outside
       the editor, since any change and its undo both land here.

       The record survives an attempt that blocks again, which is what
       tells the second block it is not the first, and so not worth
       another warning; a compile that gets through clears it. *)
    val stillBlocked = case !depsBlocked of
        SOME (b as {mods, ...}) =>
          if declaredNames = mods then SOME b else NONE
      | NONE => NONE
    in
    case stillBlocked of
      SOME b => sendDepsBlocked uri b
    | NONE =>
    (* Nothing to do if the last parse ran to completion and nothing has
       marked a point needing re-elaboration.  An edit always arrives via
       `carryOverSnapshots`, which clears `done`, so the second condition
       is what lets a *non*-edit ask for a recompile of unchanged text --
       which is how discovering that a proof suspends gets acted on. *)
    if #done (#parse (!lastTrees)) andalso not (isSome (!minEditOffset)) then
      (!LSPExtension.notifyCompileStart (!minEditOffset);
       invalidateProofs {resumeStart = NONE, inProofBody = NONE};
       !LSPExtension.resetForCompile (); ())
    else let
    val _ = stopCompile compile
    val {text as {lines, ...}, parse = lastParse} = !lastTrees
    val {declSnapshots = lastSnaps, diags = oldDiags, ...} = lastParse
    (* Resume decision: pick the largest snapshot with `endByte <=
       !minEditOffset`.  If none, recompile the whole file. *)
    val resumeSnap =
      case !minEditOffset of
        NONE => NONE
      | SOME editOff =>
        (* `declSnapshots` is newest-first, so the first match walking
           the list is the largest `endByte <= editOff`. *)
        List.find (fn (s:declSnapshot) => #endByte s <= editOff) lastSnaps
    (* Recompiling the whole file starts from the state the file's
       first dec -- its header -- left behind, not from the boot state.
       The boot state is not a legitimate starting point once a compile
       has run in this process: `resetForCompile` rewinds
       `Meta.loadedMods`, so the holdep preload re-`quse`s the
       ancestors' generated `.sml` files.  Each of those ends in
       `Theory.load_complete`, which seals the theory in
       `KernelSig.sealed_ref` -- process-global, and deliberately
       outside `Context`, being a soundness gate rather than a cache.
       `TheoryReader` refuses the re-read, every ancestor behind it
       fails "not in ancestry", and the session stops answering
       goal-state and hover requests for good.

       Resuming from the header instead leaves the ancestors both
       loaded and in the theory graph, which makes re-running the
       header idempotent: its `open`s resolve against structures that
       are still present, and `new_theory` on the name it already holds
       restarts that segment.  An ancestor the user has *added* is
       still absent from `loadedMods`, so the preload loads it for the
       first time and `link_parents` puts it in the graph.  One the
       user has *removed* stays loaded: nothing can withdraw its
       constants, grammar and DB entries, so that case needs a fresh
       process.

       `lastSnaps` is newest-first, so its last element is the oldest
       dec captured.  That is the header unless the header itself
       drew a diagnostic, which suppresses its capture. *)
    val baseSnap = case lastSnaps of
        [] => NONE
      | _ => SOME (List.last lastSnaps)
    (* `restoreSnap` is run by the compile thread, not here -- whichever
       snapshot it is restoring.  Part of what a compile snapshot holds
       is the file's namespace layer -- `Theory foo` expands to
       `open HolKernel Parse boolLib bossLib`, whose bindings land there
       -- and that layer is thread-local (lsp_namespace.ML: a thread
       inherits nothing, so `snapshotLayer` captures on one thread for a
       thunk to install on another).  Installing it here would populate
       *this* thread and leave the compile with an empty layer, so the
       recompile could not see `ACCEPT_TAC`.

       Only the boot-state path needs no such care, because there the
       compile thread re-executes the `Theory` dec, opens and all --
       and that is now the rare case, taken only when the header drew a
       diagnostic and so was never captured. *)
    val (restoreSnap, initialTrees, resumeStart, oldDiags) =
      case resumeSnap of
        NONE => (
          !LSPExtension.notifyCompileStart (!minEditOffset);
          invalidateProofs {resumeStart = NONE,
                            inProofBody = proofBodyAt (#text text)
                                                      (!minEditOffset)};
          ((case baseSnap of
              NONE => (!LSPExtension.resetForCompile (); (fn () => ()))
            | SOME s =>
              (fn () => !LSPExtension.restoreCompileSnap (#compileSnap s))),
           emptyParseData 8, 0, oldDiags))
      | SOME snap => let
          val _ = !LSPExtension.notifyCompileStart (!minEditOffset)
          val _ = invalidateProofs
                    {resumeStart = SOME (#endByte snap),
                     inProofBody = proofBodyAt (#text text)
                                               (!minEditOffset)}
          val {endByte, builtTrees, diags = snapDiags, plugins,
               ...} = snap
          (* Seed `diags` with the frozen snapshot; leave `oldDiags`
             empty so no post-`endByte` stale diagnostics from the
             previous compile leak into the LSP publish stream. *)
          val seededDiags = DArray.clone (snapDiags, DArray.size snapDiags)
          val trees : parse_data = {
            done = false, pos = endByte, builtTrees = builtTrees,
            diags = seededDiags, plugins = plugins,
            declSnapshots =
              List.filter (fn (s':declSnapshot) => #endByte s' <= endByte)
                          lastSnaps}
          val emptyDiags = DArray.new (0, Completed)
        in (fn () => !LSPExtension.restoreCompileSnap (#compileSnap snap),
            trees, endByte, emptyDiags) end
    val _ = minEditOffset := NONE
    val _ = if dbg andalso resumeStart > 0 then
              send (mkNotif "$/compileResumedAt" (fn print => (
                print "{\"uri\":"; encString uri print;
                print ",\"version\":"; encInt (#version text) print;
                print ",\"pos\":"; encInt resumeStart print;
                print "}")))
            else ()
    val trees = ref initialTrees
    val cancelled = ref false

    fun compileThread () = ((let
      val () = restoreSnap ()
      fun encDiag (Error {hard, pos, msg}) print = (
          print "{\"range\":"; encRangeLC lines pos print;
          print ",\"severity\":"; encInt (if hard then ErrorSeverity else WarnSeverity) print;
          print ",\"message\":"; msg print; print "}")
        | encDiag _ _ = raise Fail "unexpected report kind"

      val holdepMode = !holdepMode
      val mods = case holdepMode of HoldepNone => [] | _ => getHoldep (#text text)
      (* Each planned file with the dependency that asked for it, so a
         failure while executing the plan is reported against the
         dependency that named the file rather than against the file. *)
      val files = DArray.new (8, ("", ""))
      val errors = DArray.new (1, Bind)
      (* The last byte the header claims, i.e. the end of the last name
         it declares. *)
      val headerEnd =
          foldl (fn ((_, (_, e)), m) => Int.max (e, m)) 0 declared
      val depFails = ref ([]: (string * (int * int) * exn) list)
      fun noteFail m e = (
        DArray.push (errors, e);
        case List.find (fn (n, _) => n = m) declared of
          NONE => ()
        | SOME (_, pos) => depFails := (m, pos, e) :: !depFails)
      val _ = app (fn m =>
        loadPlan (fn f => DArray.push (files, (f, m))) m
        handle e => noteFail m e) mods
      fun useFiles () = DArray.app (fn (f, m) =>
        qquse f handle e => noteFail m e) files
      val _ = if DArray.isEmpty files andalso DArray.isEmpty errors then () else (
        case holdepMode of
          HoldepList => send (mkNotif "$/holdep" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"version\":"; encInt (#version text) print;
            print ",\"files\":"; encDArray (encString o #1) files print;
            if DArray.isEmpty errors then () else (
              print ",\"errors\":"; encDArray (encDiag o exnToReport 0) errors print;
              DArray.clear errors);
            print "}")))
        | _ => ();
        useFiles ();
        case holdepMode of
          HoldepList => send (mkNotif "$/holdepCompleted" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"version\":"; encInt (#version text) print;
            if DArray.isEmpty errors then () else (
              print ",\"errors\":"; encDArray (encDiag o exnToReport 0) errors print);
            print "}")))
        | _ => ())

      fun beforeCompile () = let
        val ls = getPlugins ()
        in app (fn t => #beforeCompile t ()) ls; ls end
      fun afterCompile r ls = let
        val t = !trees
        fun f (t, map) = #afterCompile t (r, map)
        in trees := setPlugins (foldl f (#plugins t) ls) t; ls end

      fun updateDiags pos = let
        val {diags, ...} = !trees
        val n = DArray.size oldDiags
        val newDiags = DArray.clone (diags, DArray.size diags + n)
        fun loop i = if i >= n then () else let
          val x = DArray.sub (oldDiags, i)
          val keep = case x of Error {pos = (start, _), ...} => start >= pos | _ => true
          in if keep then DArray.push (newDiags, x) else (); loop (i+1) end
        in loop 0; DArray.replace (oldDiags, newDiags) end

      (* Only emit publishDiagnostics when the accumulated list has
         actually changed size since the last emit -- Progress events
         far past the point where an error was found still update
         `oldDiags` (by re-merging), but if the size didn't change,
         re-sending is pure noise for the client's log.  Both compile
         diagnostics AND walker-detected runtime squiggles contribute
         to the size we compare against. *)
      val lastSentSize = ref ~1
      (* Snapshot oldDiags for the writer thread.  A live reference
         races updateDiags on the next Progress event: DArray.replace
         mid-encode makes encDArray raise Subscript, which kills the
         writer and jams every subsequent send. *)
      fun sendDiags () = let
        val n = DArray.size oldDiags
        val wd = !walkerDiags
        val ws = Binarymap.numItems wd
        val total = n + ws
        in if total = !lastSentSize then () else (
          lastSentSize := total;
          let val snapshot = DArray.clone (oldDiags, total)
              val _ = Binarymap.app
                        (fn (_, r) => DArray.push (snapshot, r)) wd
              val snapshot = dedupReports snapshot
          in
          send (mkNotif "textDocument/publishDiagnostics" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"version\":"; encInt (#version text) print;
            print ",\"diagnostics\":"; encDArray encDiag snapshot print;
            print "}"))) end)
        end

      (* Standard LSP window/workDoneProgress: gives eglot a
         mode-line spinner + percentage while the compile runs. *)
      val totalSize = size (#text text)
      (* Token is a bare integer; some clients (eglot) concatenate
         title and token when reporting, so we keep the token free of
         label-like text. *)
      val progressToken = Int.toString (!progressIdCounter)
        before progressIdCounter := !progressIdCounter + 1
      (* Not sent until we know a compile is actually going to run: a
         file whose dependencies did not load never starts one, and a
         begin without work behind it just flickers the client's
         progress area. *)
      fun sendProgressBegin () = (
        send (Request {
          id = Id (allocRequestId ()),
          method = "window/workDoneProgress/create",
          params = fn print => (
            print "{\"token\":"; encString progressToken print; print "}")});
        send (mkNotif "$/progress" (fn print => (
          print "{\"token\":"; encString progressToken print;
          print ",\"value\":{\"kind\":\"begin\",\"title\":\"HOL compile\",";
          print "\"cancellable\":false,\"percentage\":0,\"message\":";
          encString (OS.Path.file uri) print;
          print "}}"))))
      val lastReportedPct = ref 0
      fun sendProgressReport pos =
        if totalSize <= 0 then () else let
          val pct = FixedInt.toInt (FixedInt.fromInt pos * 100 div FixedInt.fromInt totalSize)
          in if pct <= !lastReportedPct then () else (
            lastReportedPct := pct;
            send (mkNotif "$/progress" (fn print => (
              print "{\"token\":"; encString progressToken print;
              print ",\"value\":{\"kind\":\"report\",\"percentage\":";
              encInt pct print; print "}}"))))
          end
      fun sendProgressEnd () =
        send (mkNotif "$/progress" (fn print => (
          print "{\"token\":"; encString progressToken print;
          print ",\"value\":{\"kind\":\"end\"}}")))

      val ls = ref (beforeCompile ())
      val lastPos = ref resumeStart
      (* Abort a doomed dec: if the file's `Libs` / `Ancestors`
         `open`s fail (e.g., a dependency of an external HOL project
         hasn't been built yet, so `open jrhUtils` fails at the top),
         every subsequent name in the same dec-expansion produces a
         "not declared" error.  The user experience is a slow trickle
         of hundreds of diagnostics for what is really one broken
         open.  Count hard errors between successive Progress events
         (each Progress marks a completed outer dec).  If a single
         dec fires `runOfErrorsLimit` hard errors without progressing,
         the file's environment is broken — set the cancel flag and
         raise Thread.Interrupt.  Real files with legitimate isolated
         errors interleave them with progress and won't trigger. *)
      val runOfErrorsLimit = 10
      val runOfErrors = ref 0
      val abortedByRunOfErrors = ref false
      fun process (Progress i) = (
          if !cancelled then raise Thread.Interrupt else ();
          runOfErrors := 0;
          trees := setParsePos i (!trees);
          afterCompile (!lastPos before lastPos := i, i) (!ls);
          send (mkNotif "$/compileProgress" (fn print => (
            print "{\"uri\":"; encString uri print;
            print ",\"pos\":"; encPosLC lines i print;
            print "}")));
          sendProgressReport i;
          updateDiags i;
          sendDiags ();
          ls := beforeCompile ())
        | process (CompilerOut (_, ss)) = logMessage (concat (rev ss))
        | process (ToplevelOut (_, ss)) = logMessage (concat (rev ss))
        | process Completed = raise Bind
        | process Interrupted = raise Bind
        | process (msg as Error {hard = true, ...}) = (
            DArray.push (#diags (!trees), msg);
            runOfErrors := !runOfErrors + 1;
            if !runOfErrors >= runOfErrorsLimit then (
              logMessage ("compile aborted after "
                          ^ Int.toString (!runOfErrors)
                          ^ " errors from a single dec: "
                          ^ "likely a broken `open` in the header");
              abortedByRunOfErrors := true;
              cancelled := true;
              raise Thread.Interrupt)
            else ())
        | process (msg as Error _) = DArray.push (#diags (!trees), msg)
      fun processBuiltTree t = trees := addBuiltTree t (!trees)
      (* After each outer dec finishes, freeze a snapshot for the LSP
         to resume from on a later `didChange` with min-edit-offset >
         endByte.  Cloning `diags` at capture time keeps the resume
         seed independent of subsequent `updateDiags` mutations.

         Skip if the cumulative `trees.diags' is non-empty at capture
         time.  A partial-parse error early in the compile (e.g. a
         `Theory foo` still being typed, whose expansion raises
         `HOL_ERR "proposed theory name '' is not an identifier"' from
         the trailing `Theory.new_theory ""') puts the file into a
         "not yet valid" state whose subsequent decs' byte extents
         will change once the user completes their edit.  Capturing
         snapshots for the file's remaining decs would carry the
         stale error forward across every subsequent didChange, since
         resume-from-snapshot seeds `trees.diags' with the snapshot's
         frozen contents.  Conservative: no snapshots until the
         current compile has produced ZERO errors so far. *)
      fun captureSnap endByte = let
        val {builtTrees, plugins, diags, ...} = !trees
        val n = DArray.size diags
        (* Unconditional, unlike the resume snapshot below: completion
           wants the file's names even when it has errors. *)
        val () = (nsLayer := SOME (LSPNameSpace.snapshotLayer ());
                  nsGen := !nsGen + 1)
        in if n > 0 then ()
           else let
             val snap = {
               endByte = endByte,
               builtTrees = builtTrees,
               diags = DArray.new (0, Completed),
               plugins = plugins,
               compileSnap = !LSPExtension.captureCompileSnap ()}
             in trees := addDeclSnapshot snap (!trees)
             end
        end
      (* Flush any diagnostics accumulated since the last Progress.
         Progress events drive `updateDiags` + `sendDiags`, so errors
         from a dec that has been INTERRUPTED before its next Progress
         (typically a `runOfErrorsLimit'-triggered abort in the middle
         of a syntactically-broken tail) are still sitting in
         `trees.diags' and haven't been merged into `oldDiags`.
         Force a merge past end-of-file so those errors reach the
         client. *)
      fun flushDiags () = (updateDiags (size (#text text)); sendDiags ())
      (* Report the load failures themselves, against the header text
         that names them, in place of the compile: everything the file
         takes from a failed ancestor is absent, so elaborating would
         report each use of each of those names and pay for the whole
         file to do it. *)
      fun blockOnDeps fails = let
        val diags = #diags (!trees)
        fun describe (m, e) = "cannot load " ^ m ^ ": " ^ depExnMessage e
        fun blockedText (m, e) =
            describe (m, e) ^
            "\n\nnot compiling this file until its Ancestors / Libs change"
        val () = app (fn (m, pos, e) => DArray.push (diags, Error {
                       hard = true, pos = pos,
                       msg = encString (blockedText (m, e))})) fails
        val message = String.concatWith "; " (map (fn (m, _, e) =>
                        describe (m, e)) fails)
        in
          (* Same fence as the completion path below: a `didChange'
             during the load has already started a fresh compile that
             owns `lastTrees', and blocking on the text it replaced
             would stop that one from ever running. *)
          if !cancelled then () else (
            lastTrees := {text = text, parse = setParsePos 0 (!trees)};
            publishAllDiagnostics uri v;
            markDepsBlocked uri v {mods = declaredNames, message = message})
        end
      (* A module `load' could not find can still be there: anything
         baked into the running heap is in the namespace without being
         in `loadedMods', and the file's `open' will find it.  What
         decides the file's fate is whether the structure is there, so
         a load failure only counts when it isn't. *)
      fun stillMissing (m, _, _) =
          not (isSome (#lookupStruct LSPNameSpace.fileNS m))
      fun runCompile () = (
        sendProgressBegin ();
        compileForReport uri (#text text) resumeStart lastPos processBuiltTree captureSnap process;
        afterCompile (!lastPos, size (#text text)) (!ls);
        (* stopCompile no longer waits for the thread to exit, so
           we might land here on a stale thread whose applyEdit has
           already superseded the buffer we compiled.  Emit the
           completion events only if we're still current; otherwise
           the fresh compile that replaced us owns lastTrees. *)
        if !cancelled then () else (
          (* Elaboration is done, so hand whatever it deferred to the
             worker pool.  Only when we are still the current compile:
             a superseded pass's proofs were queued against text the
             user has already replaced.

             The pool settles proofs asynchronously and announces each
             outcome rather than making us poll; `send` is a
             mutex-guarded handoff to the sender thread, so being called
             from a worker is safe. *)
          LSPExtension.proofStateChanged :=
            (fn (st as {site, offset, status}) =>
               let
                 (* The proof did not produce the theorem elaboration
                    stood in for, so the declarations below it were built
                    against the wrong value -- including any proofs of
                    theirs we optimistically left running.  Give up from
                    here and re-elaborate with this proof run for real.

                    A suspension is the common case: a real build stashes
                    such a theorem rather than saving it, so everything
                    below was elaborated against something that would not
                    have been there.  A bare divergence gets the same
                    treatment for the same reason.

                    `offset` is the declaration's start, which is not
                    inside a proof body, so the recompile takes the
                    conservative branch of `invalidateProofs` and gives
                    up on everything below as well -- which is the point.

                    Only on the first sighting of the name, which is what
                    makes this terminate: the re-elaboration runs the
                    proof instead of enqueueing it, so no second report
                    arrives, and if that somehow fails to hold the name is
                    already in the set and we stop anyway. *)
                 fun retract () =
                     if LSPExtension.addNoCheatSite site then
                       (bumpMinEdit minEditOffset offset;
                        scheduleCompile uri v)
                     else ()
               in
                 (* Runs on the worker that settled the proof, so it must
                    not raise. *)
                 sendProofStates uri (#lines text) [st];
                 (case status of
                      LSPExtension.Suspended _ => retract ()
                    | LSPExtension.Diverged _ => retract ()
                    | _ => ())
                 handle _ => ()
               end);
          !LSPExtension.checkDeferred resumeStart;
          (* The file compiled, so whatever it was blocked on is
             resolved. *)
          depsBlocked := NONE;
          flushDiags ();
          sendProgressEnd ();
          send (mkNotif "$/compileCompleted" (fn print => (
            print "{\"uri\":"; encString uri print; print "}")));
          lastTrees := {text = text,
                        parse = setParseDone (size (#text text)) (!trees)}))
      in (
        case List.filter stillMissing (rev (!depFails)) of
          fails as (_::_) => blockOnDeps fails
        | [] => runCompile ()
      ) handle Thread.Interrupt => (
        sendProgressEnd ();
        (* When the compile aborted because a single dec produced a
           runaway cascade of errors, the diagnostics are complete
           (up to the abort) and clients should treat the compile as
           done, not interrupted.  A user-initiated cancel or a
           didChange-driven stop remain compileInterrupted. *)
        if !abortedByRunOfErrors then (
          flushDiags ();
          send (mkNotif "$/compileCompleted" (fn print => (
            print "{\"uri\":"; encString uri print; print "}")));
          lastTrees := {text = text,
                        parse = setParseDone (size (#text text)) (!trees)};
          (* Elaboration never got past the header: an ancestor that
             loads but whose `open' fails is the case holdep cannot
             see, so treat it exactly like a load failure and stop
             compiling until the header changes.  `lastPos' is the end
             of the last dec that completed, and the header dec runs
             past the last name it declares, so it not having reached
             `headerEnd' is precisely "the header did not compile". *)
          if !lastPos <= headerEnd andalso not (null declaredNames) then
            markDepsBlocked uri v
              {mods = declaredNames,
               message = "the theory header did not compile"}
          else ())
        else send (mkNotif "$/compileInterrupted" (fn print => (
          print "{\"uri\":"; encString uri print; print "}"))))
           | e => (
        logMessage ("compile aborted: " ^ exnMessage e);
        sendProgressEnd ();
        send (mkNotif "$/compileInterrupted" (fn print => (
          print "{\"uri\":"; encString uri print; print "}"))))
      end);
      (* Don't clobber `compile` here — stopCompile may have moved on
         and started another compile that installed a fresh SOME.
         The `cancelled` flag already fences correctness. *)
      ())
    val thread = Thread.fork (compileThread, [Thread.InterruptState Thread.InterruptDefer])
    in compile := SOME {parse = trees, text = text, thread = thread,
                        cancelled = cancelled} end
    end)

  (* Fire a compile after a debounce delay: rapid didChange bursts
     collapse to one compile. *)
  and scheduleCompile uri (v as {debounce, ...}: file_data) = let
    val () = debounce := !debounce + 1
    val myEpoch = !debounce
    val debounce_ms = Time.fromMilliseconds 300
    in Thread.fork (fn () =>
        ((OS.Process.sleep debounce_ms;
          if !debounce = myEpoch then startCompile uri v else ())
         handle _ => ()),
        []); ()
    end

  fun getState {compile, lastTrees, ...} endTarget = let
    fun getIfValid {parse as {pos, ...}, text} =
      if pos > 0 then let
        val offset = fromLineCol (#lines text) endTarget
        in if offset <= pos then SOME (parse, text, offset) else NONE end
      else NONE
    val state = case !compile of
      SOME {parse, text, ...} => getIfValid {parse = !parse, text = text}
    | NONE => NONE
    in case state of NONE => getIfValid (!lastTrees) | state => state end

  fun hover uri v (startTarget, endTarget) = let
    val ({plugins, builtTrees, ...}, text, endOffset) =
      case getState v endTarget of NONE => raise Empty | SOME s => s
    val startOffset = fromLineCol (#lines text) startTarget
    fun ppToString pp = let
      val mds = DArray.new (8, "")
      val _ = PolyML.prettyPrint (fn s => DArray.push (mds, s), textWidth) pp
      in concat (DArray.toList mds) end
    val ctx = {uri = uri, lines = #lines text, plugins = plugins,
               ppToString = ppToString, width = textWidth}
    val out = !LSPExtension.hover (ctx, (startOffset, endOffset))
    fun locToRange {startPosition, endPosition, ...} = (
      getLineCol (#lines text) (FixedInt.toInt startPosition),
      getLineCol (#lines text) (FixedInt.toInt endPosition))
    fun typeHover (loc, pp) = {range = SOME (locToRange loc), markdown = ppToString pp}
    fun process loc props = let
      fun fromProps [] out = out
        | fromProps (HOL_IDE.PType ty :: props) (isId, _) = fromProps props (isId, SOME ty)
        | fromProps (HOL_IDE.PRefId i :: props) (_, ty) = fromProps props (SOME i, ty)
        | fromProps (HOL_IDE.PDefId i :: props) (_, ty) = fromProps props (SOME i, ty)
        | fromProps (_ :: props) out = fromProps props out
      val (isId, ty) = fromProps props (NONE, NONE)
      val thyHov = case HOL_IDE.builtGetThy props of
        NONE => []
      | SOME name => [{range = SOME (locToRange loc), markdown = "Theory " ^ name}]
      val (id, value, help) = case isId of
        NONE => (NONE, NONE, [])
      | SOME i => let
        val {startPosition, endPosition, ...} = loc
        val startPos = FixedInt.toInt startPosition
        val endPos = FixedInt.toInt endPosition
        val id = String.substring (#text text, startPos, endPos - startPos)
        val help =
          if lastIndexOf #"." id < 0 then let
            fun validate str = let
              fun look [] = false
                | look (HOL_IDE.PStructureAt file :: props) = let
                  val basename = String.extract (file, lastIndexOf #"/" file + 1, NONE)
                  val stem = String.extract (basename, 0, SOME (lastIndexOf #"." basename))
                  in str = stem orelse look props end
                | look (_ :: props) = look props
              in look props end
            in !LSPExtension.helpLookup (id, validate) end
          else let
            val components = splitOn #"." id
            val fst = List.hd components
            in !LSPExtension.helpLookup (List.last components, fn s => s = fst) end
          handle _ => []
        val range = SOME (getLineCol (#lines text) startPos, getLineCol (#lines text) endPos)
        val help = map (fn d => {range = range, markdown = d}) help
        val isGlobalId = i = 0 orelse let
          fun look [] = NONE
            | look (HOL_IDE.PDeclaredAt loc :: _) = SOME loc
            | look (_ :: props) = look props
          fun lookRefs [] = false
            | lookRefs (HOL_IDE.PReferences exp :: _) = exp
            | lookRefs (_ :: props) = lookRefs props
          in
            case look props of
              NONE => false
            | SOME {startPosition, endPosition, ...} =>
              case HOL_IDE.builtNavigateTo' builtTrees
                  {startOffset = FixedInt.fromInt startPosition, endOffset = FixedInt.fromInt endPosition} of
                NONE => false
              | SOME (HOL_IDE.Built (_, declProps, _), _) => lookRefs declProps
          end
        (* Lookup via the LSP file layer, not `globalNameSpace`, so
           hovers on a deleted `val foo = …` return NONE instead of
           the retained Poly/ML binding.  The layer falls through to
           `globalNameSpace` for bindings from the LSP-boot session
           (bossLib etc.). *)
        val value = if isGlobalId then #lookupVal LSPNameSpace.fileNS id else NONE
        in (SOME id, value, help) end
      open PolyML
      val ty = Option.map (fn ty =>
        NameSpace.Values.printType (ty, printDepth, SOME globalNameSpace)) ty
      val value = case value of
          NONE => NONE
        | SOME value =>
          case NameSpace.Values.print (value, printDepth) of
            PrettyString "" => NONE
          | otherwise => SOME otherwise
      (* Values of type `thm` are opaque to PolyML.NameSpace.Values;
         the SML-side hover would show only "val name: thm = ?".
         When DB has a theorem by this name, replace the standard
         value-print with the theorem statement (rendered by
         Parse.thm_to_string on the LSP-init hook). *)
      val thmMd = case id of
          NONE => NONE
        | SOME id => (!LSPExtension.thmLookup id handle _ => NONE)
      val out = case (id, ty, value, thmMd) of
          (_, NONE, NONE, _) => []
        (* Type without an identifier is the walked-up enclosing
           expression's type (`Conv.conv`, `Thm.thm -> Thm.thm`, …).
           Never informative — the user's cursor missed a specific
           name and we've fallen up.  Return nothing. *)
        | (NONE, SOME _, NONE, _) => []
        | (SOME id, SOME ty, _, SOME md) => let
          (* Theorem: "val id: thm\n\n<statement>" as one markdown block.
             ppToString may leave a trailing newline; strip it before
             appending the separator so we get exactly one blank line. *)
          fun rtrim s = let
            val n = size s
            fun k i = if i > 0 andalso Char.contains "\n\r " (String.sub (s, i-1))
                      then k (i-1) else i
            in String.substring (s, 0, k n) end
          in [{range = SOME (locToRange loc),
               markdown = "val " ^ id ^ ": " ^ rtrim (ppToString ty)
                          ^ "\n\n" ^ md}]
          end
        | (SOME id, SOME ty, NONE, NONE) =>
          [typeHover (loc, PrettyBlock(0, true, [],
            [PrettyString ("val " ^ id ^ ":"), PrettyBreak(1, 2), ty]))]
        | (id, ty, SOME value, NONE) =>
          [typeHover (loc, PrettyBlock(2, true, [], [
            PrettyBlock(0, false, [],
              (case ty of
                 NONE => [PrettyString ("val " ^ Option.getOpt (id, "_"))]
                | SOME ty => [
                  PrettyString ("val " ^ Option.getOpt (id, "_") ^ ":"),
                  PrettyBreak(1, 2), ty])
              @ [PrettyBreak(1, 2), PrettyString "="]),
             PrettyBreak(1, 0), value]))]
        | _ => []
      in thyHov @ help @ out end
    fun crossesNewline (s, e) = let
      val txt = #text text
      fun loop i = i < e andalso
                   (String.sub (txt, i) = #"\n" orelse loop (i + 1))
      in loop s end
    (* Suppress hover on any Built node whose span crosses a newline —
       these are enclosing expressions (e.g. a whole `Proof … QED`
       tactic body typing as `tactic`) whose SML type is uninformative.
       Per-identifier / per-token nodes are single-line and unaffected. *)
    fun fromTree NONE = []
      | fromTree (pt as (SOME (HOL_IDE.Built ((s, e), props, _), _))) =
        if crossesNewline (FixedInt.toInt s, FixedInt.toInt e) then []
        else case process {startPosition = s, endPosition = e} props of
          [] => fromTree (HOL_IDE.builtMoveUp pt)
        | out => out
    val offset' = {startOffset = FixedInt.fromInt startOffset,
                   endOffset = FixedInt.fromInt endOffset}
    val innermost = HOL_IDE.builtNavigateTo' builtTrees offset'
    (* If the cursor sits on raw HOL-quotation text — the innermost
       built-tree node has PQuote — the SML tree hover would walk up
       to the enclosing expansion and return misleading info (e.g.
       "string" for the QUOTE-wrapped body).  Dispatch to the
       HOL-side Preterm hover instead; and if it can't produce a
       hover, return nothing rather than bogus SML type info. *)
    val inQuoteSpan =
      case innermost of
        SOME (HOL_IDE.Built (sp, props, _), _) =>
          if List.exists (fn HOL_IDE.PQuote => true | _ => false) props
          then SOME sp else NONE
      | _ => NONE
    fun fq (s, e) = let
      val qs = FixedInt.toInt s
      val qe = FixedInt.toInt e
      val quote = String.substring (#text text, qs, qe - qs)
      in !LSPExtension.hoverQuotation
           ({uri = uri, lines = #lines text, plugins = plugins,
             ppToString = ppToString, width = textWidth},
            {quote = quote, quoteStart = qs, target = startOffset}) end
    fun f () = fromTree innermost
    val out =
      case (out, inQuoteSpan) of
        (_::_, _)     => out
      | ([], SOME sp) => fq sp
      | ([], NONE)    => f ()
    val _ = case out of [] => raise Empty | _ => ()
    fun merge ({range = NONE, ...}, a) = a
      | merge ({range = a, ...}, NONE) = a
      | merge ({range = SOME (lo1, hi1), ...}, SOME (lo2, hi2)) =
        SOME (if leLC lo1 lo2 then lo1 else lo2, if leLC hi1 hi2 then hi2 else hi1)
    val markdown = String.concatWith "\n\n---\n\n" (map #markdown out)
    in SOME {markdown = markdown, range = foldl merge NONE out} end
    handle Empty => NONE

  fun gotoDefinition uri v target = let
    fun fromFileLine {origin, file, line} = let
      val range = ((line, 0), (line+1, 0))
      in {origin = origin, uri = SOME file, range = range, selRange = range} end
    val ({plugins, builtTrees, ...}, text, offset) =
      case getState v target of NONE => raise Empty | SOME s => s
    val ctx = {uri = uri, lines = #lines text, plugins = plugins, fromFileLine = fromFileLine}
    val out = !LSPExtension.gotoDefinition (ctx, offset)
    fun f () = let
      fun fromProps [] r = r
        | fromProps (HOL_IDE.PDeclaredAt loc :: _) (file, ty, _) = (file, ty, SOME loc)
        | fromProps (HOL_IDE.PStructureAt file :: props) (_, ty, df) =
          fromProps props (SOME file, ty, df)
        | fromProps (HOL_IDE.PType ty :: props) (file, _, df) = fromProps props (file, SOME ty, df)
        | fromProps (_ :: props) r = fromProps props r
      val offset' = {startOffset = FixedInt.fromInt offset, endOffset = FixedInt.fromInt offset}
      val (HOL_IDE.Built ((startPosition, endPosition), props, _), _) =
        case HOL_IDE.builtNavigateTo' builtTrees offset' of NONE => raise Empty | SOME pt => pt
      val start = FixedInt.toInt startPosition
      val stop = FixedInt.toInt endPosition
      val origin = SOME (getLineCol (#lines text) start, getLineCol (#lines text) stop)
      val (file, ty, loc) = case fromProps props (NONE, NONE, NONE) of
        (_, _, NONE) => raise Empty
      | (file, ty, SOME loc) => (file, ty, loc)
      fun fromPolyLoc {file, startLine, startPosition, endPosition, ...} =
        if file = "" then let
          val range = (getLineCol (#lines text) startPosition, getLineCol (#lines text) endPosition)
          in {origin = origin, uri = NONE, range = range, selRange = range} end
        else fromFileLine {origin = origin, file = file, line = startLine - 1}
      val newLoc = case (file, ty) of
        (SOME file, SOME _) =>
        !LSPExtension.fixupTheoremLink {uri = file, text = #text text, start = start, stop = stop}
      | _ => NONE
      val newLoc = case newLoc of
        NONE => fromPolyLoc loc
      | SOME {file, line} => fromFileLine {origin = origin, file = file, line = line}
      in [newLoc] end
    in case out of [] => f () | _ => out end
    handle Empty => []

  (* Unlike `getState', goalStateAtPos doesn't gate on the compile
     having reached the cursor -- the walker uses `declSnapshots'
     (which survive `carryOverSnapshots') for Context and parses
     the Proof body directly from the current buffer text.
     Requiring `pos >= offset' would stall the auto-follow-cursor
     pane for the ~300 ms debounce after every keystroke. *)
  fun goalStateAtPos uri ({lastTrees, depsBlocked, ...}:file_data)
                     (target, width) =
    (* Nothing to walk against: the file was never compiled, so the
       theorem's context does not exist and the walker would compile
       each tactic against a namespace missing whatever the failed
       ancestor was to supply.  Answering NONE also stops an
       auto-following goals pane from asking on every cursor move. *)
    if isSome (!depsBlocked) then NONE else let
    val {parse, text} = !lastTrees
    val {plugins, declSnapshots, ...} = parse
    val offset = fromLineCol (#lines text) target
    fun ppToString pp = let
      val mds = DArray.new (8, "")
      val _ = PolyML.prettyPrint (fn s => DArray.push (mds, s), textWidth) pp
      in concat (DArray.toList mds) end
    val ctx = {uri = uri, lines = #lines text, plugins = plugins,
               ppToString = ppToString, width = width}
    (* Largest declSnapshot with endByte < theoremStart.  Restoring
       this before invoking the walker means the walker's tactics
       (in particular `simp[]` via `srw_ss()`) see the same Context
       — including srw_ss extensions — that existed when the file
       compile reached the theorem's dec.  Without this, later
       `export_rewrites` in the same file skew simp's normal form
       and slow tactics like METIS_TAC to a crawl. *)
    fun snapBefore ts = List.foldl
      (fn (s, best) =>
        if #endByte s >= ts then best
        else case best of
               NONE => SOME s
             | SOME b => if #endByte s > #endByte b then SOME s else best)
      NONE declSnapshots
    (* The user is looking at goal state here, so they are working on
       this proof: hold it back from the pool, because the walker below
       is about to replay that very tactic and a worker doing it too is
       duplicated effort.  Moving to a different proof, or out of one
       altogether, releases the previous one at raised priority --
       setFocus handles the transition.

       Note this depends on the client asking for goal state; if it
       stops asking (the pane is closed, say) the last-focused proof
       stays held rather than being checked.  A timer would fix that;
       it is not worth the machinery yet. *)
    in case findEnclosingTheorem (#done parse) (#text text) offset of
         NONE => (!LSPExtension.setProofFocus NONE; NONE)
       | SOME (decStart, thm as {quoteStart, ...}) =>
         let val () = !LSPExtension.setProofFocus (SOME decStart)
             val restoreLater = !LSPExtension.captureCompileSnap ()
             val () = case snapBefore quoteStart of
               NONE => ()
             | SOME s => !LSPExtension.restoreCompileSnap (#compileSnap s)
             val r = !LSPExtension.goalStateAtPos (ctx, thm)
                     handle e => (restoreLater (); raise e)
             val () = restoreLater ()
         in r end
    end handle Empty => NONE

  (* The buffer's outline, parsed at most once per text version: the
     outline is asked for on every edit, and `workspace/symbol' asks
     every open buffer on every keystroke of the search box. *)
  fun symbolsOf ({lastTrees, symbols, ...}: file_data) = let
    val {text = {text, version, ...}, ...} = !lastTrees
    fun parse () = let val syms = bufferSymbols text
                   in symbols := SOME (version, syms); syms end
    in
      case !symbols of
        SOME (v, syms) => if v = version then syms else parse ()
      | NONE => parse ()
    end

  (* `workspace/symbol'.  Answers from what HOL knows exists -- see
     `LSPExtension.ideSymbols' -- unioned with the declarations of the
     buffers this process has open, so a theorem written a minute ago in
     a file that does not compile is still findable.

     A very short query is refused: the underlying search matches
     substrings, so one or two characters asks for most of the
     database. *)
  val maxWorkspaceSymbols = 200
  fun workspaceSymbols query =
    if size query < 2 then []
    else let
      val q = CharVector.map Char.toLower query
      val hits = !LSPExtension.ideSymbols
                   {query = query, prefixOnly = false,
                    limit = maxWorkspaceSymbols}
      (* A recorded path that no longer exists would give the user a
         dead link, which is worse than one missing entry. *)
      fun accessible f = OS.FileSys.access (f, []) handle _ => false
      fun located ({file, line, name, theory, class, visible}
                     : LSPExtension.ide_symbol) =
          case file of
            NONE => NONE
          | SOME f =>
            if not (accessible f) then NONE
            else SOME {name = name,
                       container = theory ^ "Theory" ^
                                   (if visible then ""
                                    else " (not an ancestor)"),
                       kind = if class = "Def" then symFunction
                              else symConstant,
                       uri = "file://" ^ f,
                       line = Int.max (0, line - 1)}
      val fromHol = List.mapPartial located hits
      (* The open buffers, by their own text rather than by anything
         built. *)
      val open_ = withFileInfo (fn fi => (fi, Binarymap.listItems fi))
      fun ofBuffer (uri, v) = let
        val {text = {lines, ...}, ...} = !(#lastTrees (v: file_data))
        fun keep (Sym {name, span, ...}) =
            if String.isSubstring q (CharVector.map Char.toLower name)
            then SOME {name = name, container = "this file",
                       kind = symConstant, uri = uri,
                       line = #1 (LSPExtension.getLineCol lines (#1 span))}
            else NONE
        in List.mapPartial keep (symbolsOf v) end
        handle _ => []
      val fromBuffers = List.concat (map ofBuffer open_)
      (* A buffer hit points at editable text, so it wins over the
         built record of the same name. *)
      fun step (h, (acc, seen)) =
          if Binaryset.member (seen, #name h) then (acc, seen)
          else (h :: acc, Binaryset.add (seen, #name h))
      val all = rev (#1 (List.foldl step ([], Binaryset.empty String.compare)
                                    (fromBuffers @ fromHol)))
      in List.take (all, maxWorkspaceSymbols) handle Subscript => all end

  fun encWorkspaceSymbol {name, container, kind, uri, line} print = (
      print "{\"name\":"; encString name print;
      print ",\"kind\":"; encInt kind print;
      print ",\"containerName\":"; encString container print;
      print ",\"location\":{\"uri\":"; encString uri print;
      print ",\"range\":{\"start\":{\"line\":"; encInt line print;
      print ",\"character\":0},\"end\":{\"line\":"; encInt line print;
      print ",\"character\":0}}}}")

  (* `textDocument/completion'.  Two sources: the SML names in scope for
     this file, and the theorem names HOL knows.

     The namespace layer is thread-local (lsp_namespace.ML), so a
     request thread sees globals only until the compile thread's layer
     is installed on it -- which is what `nsLayer' carries.  Installing
     just the layer is deliberate: restoring a whole compile snapshot
     here, as the goal-state handler does, would rewind the Context out
     from under a compile that is very likely running, and completion
     fires on every keystroke. *)
  val maxCompletions = 200
  fun identPrefixAt text offset = let
    val n = size text
    fun back i = if i > 0 andalso isIdentChar (String.sub (text, i - 1))
                 then back (i - 1) else i
    val st = back (Int.min (offset, n))
    val prefix = String.substring (text, st, Int.min (offset, n) - st)
    val qual =
      if st > 0 andalso String.sub (text, st - 1) = #"." then let
        val qs = back (st - 1)
        in SOME (String.substring (text, qs, st - 1 - qs)) end
      else NONE
    in {prefix = prefix, qual = qual} end

  (* Every name in scope for the file, with its CompletionItemKind,
     computed once per `nsLayer' generation.  `#allVal' and friends
     merge the file layer with the whole global namespace and filter
     the shadowed globals out, which is thousands of entries -- far too
     much to redo on each keystroke, and it only changes when a
     declaration finishes compiling. *)
  fun scopeNames ({nsGen, nsNames, ...}: file_data) = let
    val gen = !nsGen
    fun collect () = let
      val ns = LSPNameSpace.fileNS
      fun tagged kind names = map (fn (nm, _) => (nm, kind)) names
      val all = tagged 6 (#allVal ns ()) @
                tagged 9 (#allStruct ns ()) @
                tagged 22 (#allType ns ())
      in nsNames := SOME (gen, all); all end
    in
      case !nsNames of
        SOME (g, names) => if g = gen then names else collect ()
      | NONE => collect ()
    end

  fun completionsAt uri (v as {lastTrees, nsLayer, ...}: file_data) pos = let
    val {text = {text, lines, ...}, ...} = !lastTrees
    val offset = fromLineCol lines pos
    val {prefix, qual} = identPrefixAt text offset
    in
      (* Nothing typed yet: the answer would be the whole namespace, and
         the client re-asks as soon as there is a character. *)
      if prefix = "" andalso qual = NONE then {items = [], incomplete = true}
      else let
        val () = case !nsLayer of SOME restore => restore () | NONE => ()
        val items = ref ([]: {label: string, kind: int,
                              detail: string option} list)
        val count = ref 0
        fun add it = if !count >= maxCompletions then ()
                     else (items := it :: !items; count := !count + 1)
        fun addNames kind names =
            app (fn (nm, _) => if String.isPrefix prefix nm
                               then add {label = nm, kind = kind,
                                         detail = NONE}
                               else ()) names
        val ns = LSPNameSpace.fileNS
        val () = case qual of
            NONE =>
            app (fn (nm, kind) =>
                    if String.isPrefix prefix nm
                    then add {label = nm, kind = kind, detail = NONE}
                    else ())
                (scopeNames v)
          | SOME q =>
            (case #lookupStruct ns q of
               NONE => ()
             | SOME st => let
                 val sub = PolyML.NameSpace.Structures.contents st
                 in addNames 6 (#allVal sub ());
                    addNames 22 (#allType sub ())
                 end handle _ => ())
        (* Theorem names.  A qualified `fooTheory.' asks that theory. *)
        val dbq = case qual of
            SOME q => if String.isSuffix "Theory" q
                      then String.substring (q, 0, size q - 6) ^ "$" ^ prefix
                      else prefix
          | NONE => prefix
        val () =
          if prefix = "" then ()
          else app (fn ({name, theory, class, visible, ...}
                          : LSPExtension.ide_symbol) =>
                       add {label = name, kind = 21,
                            detail = SOME (theory ^ "Theory" ^
                                           (if visible then ""
                                            else " (not an ancestor)"))})
                   (!LSPExtension.ideSymbols
                      {query = dbq, prefixOnly = true, limit = 100})
        in {items = rev (!items), incomplete = !count >= maxCompletions}
        end
    end handle _ => {items = [], incomplete = true}

  fun encCompletionItem {label, kind, detail} print = (
      print "{\"label\":"; encString label print;
      print ",\"kind\":"; encInt kind print;
      (case detail of
         NONE => ()
       | SOME d => (print ",\"detail\":"; encString d print));
      print "}")

  fun encCompletionList {items, incomplete} print = (
      print "{\"isIncomplete\":"; print (if incomplete then "true" else "false");
      print ",\"items\":"; encArray encCompletionItem items print;
      print "}")

  fun eval id {uri, code, incr, holdep} = let
    val lines = mkLineCounter code

    val mods = case holdep of HoldepNone => [] | _ => getHoldep code
    val files = DArray.new (8, "")
    val _ = app (fn m =>
      loadPlan (fn f => DArray.push (files, f)) m
      handle e => logMessage ("ignoring load error: " ^ exnMessage e)) mods
    val _ = case holdep of
      HoldepList => send (mkNotif "$/eval/holdep" (fn print => (
        print "{\"uri\":"; encString uri print;
        print ",\"id\":"; encReqId id print;
        print ",\"files\":"; encDArray encString files print; print "}")))
    | _ => ()
    val _ = DArray.app (fn f =>
      qquse f handle e => logMessage ("ignoring load error: " ^ exnMessage e)) files
    val _ = case holdep of
      HoldepList => send (mkNotif "$/eval/holdepCompleted" (fn print => (
        print "{\"uri\":"; encString uri print;
        print ",\"id\":"; encReqId id print; print "}")))
    | _ => ()

    fun encReport (Error {hard, pos, msg}) print = (
        print "{\"kind\":\"error\"";
        print ",\"hard\":"; print (if hard then "true" else "false");
        print ",\"pos\":"; encRangeLC lines pos print;
        print ",\"msg\":"; msg print; print "}")
      | encReport (CompilerOut (pos, s)) print = (
        print "{\"kind\":\"compilerOut\"";
        print ",\"pos\":"; encPosLC lines pos print;
        print ",\"body\":"; encString (concat (rev s)) print; print "}")
      | encReport (ToplevelOut (pos, s)) print = (
        print "{\"kind\":\"toplevelOut\"";
        print ",\"pos\":"; encPosLC lines pos print;
        print ",\"body\":"; encString (concat (rev s)) print; print "}")
      | encReport (Progress i) print = (
        print "{\"kind\":\"compileProgress\"";
        print ",\"pos\":"; encPosLC lines i print; print "}")
      | encReport Completed print = print "{\"kind\":\"compileCompleted\"}"
      | encReport Interrupted print = print "{\"kind\":\"interrupted\"}"

    val compile = compileForReport uri code 0 (ref 0) (fn _ => ()) (fn _ => ())
    in
      case incr of
        IncrNone => let
        val buf = DArray.new (8, Completed)
        val _ = compile (fn Progress _ => () | msg => mergeInto msg buf) handle
          Thread.Interrupt => DArray.push (buf, Interrupted)
        in Ok (encDArray encReport buf) end
      | IncrChunk => (
        spawnJobCore id (fn () => let
          val buf = DArray.new (8, Completed)
          val prev = ref 0
          fun clearBuf complete i = let
            fun params print = (
              print "{\"id\":"; encReqId id print;
              print ",\"pos\":"; encRangeLC lines (!prev before prev := i, i) print;
              print ",\"out\":"; encDArray encReport buf print;
              if complete then print ",\"complete\":true" else (); print "}")
            in send (mkNotif "$/eval/P" params); DArray.clear buf end
          val _ = compile (fn Progress i => clearBuf false i | msg => mergeInto msg buf)
            handle Thread.Interrupt => DArray.push (buf, Interrupted)
          in clearBuf true (size code) end);
        Ok encNull)
      | IncrStream => (
        spawnJobCore id (fn () => let
          fun sendMsg msg = send (mkNotif "$/eval/1" (fn print => (
            print "{\"id\":"; encReqId id print;
            print ",\"out\":"; encReport msg print; print "}")))
          val ok = (compile sendMsg; true) handle
            Thread.Interrupt => (sendMsg Interrupted; false)
          in if ok then sendMsg Completed else () end);
        Ok encNull)
    end

  fun recvExit () =
    case recv () of
      Notification {method = "exit", ...} => ()
    | _ => (diag "ignoring message after shutdown"; recvExit ())

  exception Shutdown
  fun main () = (
    (case recv () of
      Request {method = "shutdown", id, ...} => (
        diag "received shutdown request";
        send (mkResponse id (Ok encNull));
        recvExit ();
        raise Shutdown)
    | Request {method = "textDocument/hover", id, params} =>
      spawnJob id params textDocumentPositionParams (fn {uri, pos} => let
        val hov = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => NONE
        | SOME v => hover uri v (pos, pos)
        in Ok (encOrNull encHover hov) end)
    | Request {method = "textDocument/definition", id, params} =>
      spawnJob id params textDocumentPositionParams (fn {uri, pos} => let
        val ls = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => []
        | SOME v => gotoDefinition uri v pos
        in Ok (encArray (encLocationLink uri) ls) end)
    | Request {method = "textDocument/documentSymbol", id, params} =>
      spawnJob id params textDocumentId (fn uri =>
        case withFileInfo (fn fileInfo =>
               (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => Ok (fn print => print "[]")
        | SOME v => let
            val {text = {lines, ...}, ...} = !(#lastTrees (v: file_data))
            val syms = symbolsOf v
          in
            Ok (if !hierarchicalSymbols
                then encArray (encDocumentSymbol lines) syms
                else encArray
                       (fn (c, sym) => encSymbolInformation uri lines c sym)
                       (flatSymbols syms))
          end)
    | Request {method = "workspace/symbol", id, params} =>
      spawnJob id params workspaceSymbolParams (fn query =>
        Ok (encArray encWorkspaceSymbol (workspaceSymbols query)))
    | Request {method = "textDocument/completion", id, params} =>
      spawnJob id params textDocumentPositionParams (fn {uri, pos} =>
        case withFileInfo (fn fileInfo =>
               (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => Ok (encCompletionList {items = [], incomplete = true})
        | SOME v => Ok (encCompletionList (completionsAt uri v pos)))
    | Request {method = "$/setConfig", id, params} => ((
      case JSONDecode.decode (JSONDecode.fieldO "elabOn" elabOn) params of
        NONE => ()
      | SOME v => elabOnRef := v;
      send (mkResponse id (Ok encNull)))
      handle JSONDecode.JSONError _ =>
        send (mkResponse id (mkErr InvalidParams "json decode failed")))
    | Request {method = "$/eval", id, params} =>
      spawnJob id params evalParams (eval id)
    | Request {method = "$/hol/goalState", id, params} =>
      spawnJob id params goalStateParams (fn {uri, pos, width} => let
        val (v_opt, resp) = case withFileInfo (fn fileInfo =>
              (fileInfo, Binarymap.peek (fileInfo, uri))) of
            NONE => (NONE, NONE)
          | SOME v => (SOME v, goalStateAtPos uri v (pos, width))
        (* Fold the walker's failure/success into per-file walker
           diagnostics keyed by theorem name so a user-fix removes
           the squiggle without waiting for the next compile.  Emit
           publishDiagnostics whenever the walker's slot changes. *)
        val () = case (v_opt, resp) of
            (SOME (v: file_data), SOME {theorem, failedRange, error, ...}) => let
              val wd = !(#walkerDiags v)
              val prev = Binarymap.peek (wd, theorem)
              val next = case (failedRange, error) of
                  (SOME (s, e), SOME msg) => SOME (Error {
                    hard = true, pos = (s, e), msg = encString msg })
                | _ => NONE
              val changed = case (prev, next) of
                  (NONE, NONE) => false
                | (SOME _, NONE) => true
                | (NONE, SOME _) => true
                | _ => true  (* re-emit even if same theorem — text may differ *)
              val () = case next of
                  NONE => #walkerDiags v := Binarymap.foldl
                    (fn (k, r, m) => if k = theorem then m
                                     else Binarymap.insert (m, k, r))
                    (Binarymap.mkDict String.compare) wd
                | SOME r => #walkerDiags v := Binarymap.insert (wd, theorem, r)
            in if changed then publishAllDiagnostics uri v else () end
          | _ => ()
        in Ok (encOrNull encGoalStateResponse resp) end)
    | Request {method, id, ...} =>
      send (mkResponse id (mkErr InvalidRequest ("unknown method: " ^ method)))
    | Notification {method = "$/cancelRequest", params} => let
      val id = JSONDecode.decode cancelParams params
      in app (fn (j,th) => if j = id then Thread.interrupt th else ()) (jobs I) end
    | Notification {method = "textDocument/didOpen", params} => let
      val {uri, text, version} = JSONDecode.decode textDocumentParams params
      val () = checkSingleFile uri
      val (v, existed) = withFileInfo (fn fileInfo =>
        case Binarymap.peek (fileInfo, uri) of
          SOME v => (fileInfo, (v, true))
        | NONE => let val v = newFile text version
                  in (Binarymap.insert (fileInfo, uri, v), (v, false)) end)
      val () = if existed then applyEdit v version [{range = NONE, text = text}]
               else augmentLoadPathForUri uri
      in if !elabOnRef = ElabOnChange then startCompile uri v else () end
    | Notification {method = "textDocument/didChange", params} => let
      val {uri, version, changes} = JSONDecode.decode didChangeParams params
      val _ = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
        NONE => ()
      | SOME v => (
        applyEdit v version changes;
        (* Debounce so keystroke bursts don't kick off a compile per
           character; only the last edit in a 300 ms window fires. *)
        if !elabOnRef = ElabOnChange then scheduleCompile uri v else ())
      in () end
    (* Escape hatch for a block cleared outside the editor: the user
       has built the missing ancestor and wants the file compiled
       without having to touch its header. *)
    | Notification {method = "$/hol/retryCompile", params} => let
      val uri = JSONDecode.decode textDocumentId params
      val _ = case withFileInfo (fn fileInfo =>
                     (fileInfo, Binarymap.peek (fileInfo, uri))) of
        NONE => ()
      | SOME (v: file_data) => (#depsBlocked v := NONE; startCompile uri v)
      in () end
    | Notification {method = "textDocument/didClose", params} => let
      val uri = JSONDecode.decode textDocumentId params
      val _ = withFileInfo (fn fileInfo => (
        case Binarymap.peek (fileInfo, uri) of
          NONE => (fileInfo, ())
        | SOME {compile, ...} =>
          (stopCompile compile; (#1 (Binarymap.remove (fileInfo, uri)), ()))))
      in () end
    | Notification {method = "textDocument/didSave", params} =>
      if !elabOnRef <> ElabOnSave then () else let
        val uri = JSONDecode.decode textDocumentId params
        val _ = case withFileInfo (fn fileInfo => (fileInfo, Binarymap.peek (fileInfo, uri))) of
          NONE => ()
        | SOME v => startCompile uri v
        in () end
    | Response _ => diag "response to unknown request"
    | Notification {method, ...} => diag ("unknown method: " ^ method))
    handle
      e as Shutdown => PolyML.Exception.reraise e
    | e => logMessage ("ignored exception " ^ exnMessage e);
    main ())
  in
    main () handle
      Shutdown => ()
    | Channel.Disconnected => diag "early abort"
  end

end (* struct *)
