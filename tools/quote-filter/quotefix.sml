structure quotefix :> quotefix =
struct
open HolParser
open ToSML Simple

fun K a _ = a

fun run read write = let
  val {read, readAt} = mkDoubleReader read 0
  val feed = mkParser {read = read, pos = ~1, parseError = K (K ())}
  val pos = ref 0
  fun push p = (readAt (!pos) p (write o Substring.string o #2); pos := p)

  fun doQuote (QBody {toks, ...}) =
    app (fn QuoteAntiq (_, Paren {decls, ...}) => doDecls decls | _ => ()) toks
  and doQuotes l r p (quote as QBody {start, stop, ...}) q = (
    push p; write l; pos := start;
    doQuote quote;
    push stop; write r; pos := q)
  and doDecl d = case d of
      DefinitionDecl {quote, termination = SOME {decls, ...}, ...} =>
        (doQuote quote; doDecls decls)
    | DefinitionDecl {quote, termination = NONE, ...} => doQuote quote
    | DatatypeDecl {quote, ...} => doQuote quote
    | QuoteDecl {quote, ...} => doQuote quote
    | QuoteEqnDecl {quote, ...} => doQuote quote
    | InductiveDecl {quote, ...} => doQuote quote
    | TheoremDecl {quote, body, ...} => (doQuote quote; doDecls body)
    | BeginType _ => ()
    | BeginSimpleThm _ => ()
    | Chunk _ => ()
    | Semi _ => ()
    | String _ => ()
    | LinePragma _ => ()
    | LinePragmaWith _ => ()
    | FilePragma _ => ()
    | FilePragmaWith _ => ()
    | FullQuote {head = (p, _), quote, stop, ...} =>
      doQuotes "\226\128\156" "\226\128\157" p quote stop
    | Quote {head = (p, _), quote, stop, ...} =>
      doQuotes "\226\128\152" "\226\128\153" p quote stop
  and doDecls (Decls {decls, ...}) = app doDecl decls

  fun loop () =
    case feed () of
      TopDecl d => (doDecl d; loop ())
    | Simple.EOF p => push p
  in loop () end

end
