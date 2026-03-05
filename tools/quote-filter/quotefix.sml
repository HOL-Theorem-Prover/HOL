structure quotefix :> quotefix =
struct
open HOLAst

fun K a _ = a

fun run read write = let
  val {parseDec, body, ...} = HOLParser.parseSML "" read (K (K (K ()))) HOLParser.initialScope
  val pos = ref 0
  fun push p = (write (DString.extract (body, !pos, SOME p)); pos := p)
  fun replace l (p, s) = if l = s then () else (push p; write l; pos := p + size s)
  fun doExp (Wild _) = ()
    | doExp (IntegerConstant _) = ()
    | doExp (WordConstant _) = ()
    | doExp (StringConstant _) = ()
    | doExp (CharConstant _) = ()
    | doExp (RealConstant _) = ()
    | doExp (Unit _) = ()
    | doExp (Ident _) = ()
    | doExp (List {elems, ...}) = app doExp (#args elems)
    | doExp (Tuple {elems, ...}) = app doExp (#args elems)
    | doExp (Record {elems, ...}) = app doRow (#args elems)
    | doExp (Parens {exp, ...}) = doExp exp
    | doExp (Infix {left, right, ...}) = (doExp left; doExp right)
    | doExp (Typed {exp, ...}) = doExp exp
    | doExp (Layered {pat, ...}) = doExp pat
    | doExp (Or elems) = app doExp (#args elems)
    | doExp (Select _) = ()
    | doExp (Sequence {elems, ...}) = app doExp (#args elems)
    | doExp (LetInEnd {dec, exps, ...}) = (app doDec dec; app doExp (#args exps))
    | doExp (App (f, a)) = (doExp f; doExp a)
    | doExp (AndAlso {left, right, ...}) = (doExp left; doExp right)
    | doExp (OrElse {left, right, ...}) = (doExp left; doExp right)
    | doExp (Handle {exp, elems, ...}) = (doExp exp; app doArm elems)
    | doExp (Raise {exp, ...}) = doExp exp
    | doExp (IfThenElse {exp1, exp2, else_, ...}) =
      (doExp exp1; doExp exp2; Option.app (doExp o #exp3) else_)
    | doExp (While {exp1, exp2, ...}) = (doExp exp1; doExp exp2)
    | doExp (Case {exp, elems, ...}) = (doExp exp; app doArm elems)
    | doExp (Fn {elems, ...}) = app doArm elems
    | doExp (HOLFullQuote {head, quote, end_tok, ...}) =
      (replace "\226\128\156" head; app doQDecl quote; Option.app (replace "\226\128\157") end_tok)
    | doExp (HOLQuote {head, quote, end_tok, ...}) =
      (replace "\226\128\152" head; app doQDecl quote; Option.app (replace "\226\128\153") end_tok)
    | doExp (HOLLinePragma _) = ()
    | doExp (HOLLinePragmaWith _) = ()
    | doExp (HOLFilePragma _) = ()
    | doExp (HOLFilePragmaWith _) = ()
    | doExp (ExpEmpty _) = ()
    | doExp (ExpBad _) = ()
    | doExp (ExpExpansion {orig, ...}) = doExp orig
  and doRow (DotDotDot _) = ()
    | doRow (LabEq {exp, ...}) = doExp exp
    | doRow (LabAs {aspat, ...}) = Option.app (doExp o #exp) aspat
    | doRow (LabExpansion {orig, ...}) = doRow orig
  and doArm {pat, exp, ...} = (doExp pat; doExp exp)
  and doDec (DecSemi _) = ()
    | doDec (DecVal {elems, ...}) = app doValBind (#args elems)
    | doDec (DecFun {fvalbind, ...}) = app (app doFValArm) (#args fvalbind)
    | doDec (DecType _) = ()
    | doDec (DecEqtype _) = ()
    | doDec (DecDatatype _) = ()
    | doDec (DecAbstype _) = ()
    | doDec (DecException _) = ()
    | doDec (DecLocal {dec1, dec2, ...}) = (app doDec dec1; app doDec dec2)
    | doDec (DecOpen _) = ()
    | doDec (DecInfix _) = ()
    | doDec (DecInfixr _) = ()
    | doDec (DecNonfix _) = ()
    | doDec (DecStructure {elems, ...}) =
      app (Option.app (doStrExp o #strexp) o #bind) (#args elems)
    | doDec (DecSignature _) = ()
    | doDec (DecInclude _) = ()
    | doDec (Sharing _) = ()
    | doDec (DecFunctor {elems, ...}) = app (Option.app (doStrExp o #strexp) o #bind) (#args elems)
    | doDec (DecExp e) = doExp e
    | doDec (HOLTheory _) = ()
    | doDec (HOLTheoryEnd _) = ()
    | doDec (HOLDefinition {quote, termination, ...}) =
      (app doQDecl quote; Option.app (doExp o #tac) termination)
    | doDec (HOLDatatype {quote, ...}) = app doQDecl quote
    | doDec (HOLQuoteDecl {bind, quote, ...}) = (Option.app (doExp o #exp) bind; app doQDecl quote)
    | doDec (HOLInductiveDecl {quote, ...}) = app doQDecl quote
    | doDec (HOLType {bind, ...}) = Option.app (doExp o #exp) bind
    | doDec (HOLSimpleThm {bind, ...}) = Option.app (doExp o #exp) bind
    | doDec (HOLTheoremDecl {quote, tac, ...}) = (app doQDecl quote; doExp tac)
    | doDec (HOLResume {tac, ...}) = doExp tac
    | doDec (HOLFinalise _) = ()
    | doDec (DecBad _) = ()
    | doDec (DecExpansion {orig, ...}) = doDec orig
  and doValBind {pat, eq, ...} = (doExp pat; Option.app (doExp o #exp) eq)
  and doFValArm {pat, exp, ...} = (doExp pat; doExp exp)
  and doStrExp (StrIdent _) = ()
    | doStrExp (StrStruct {strdec, ...}) = app doDec strdec
    | doStrExp (StrConstraint {strexp, ...}) = doStrExp strexp
    | doStrExp (FunAppExp {strexp, ...}) = doStrExp strexp
    | doStrExp (FunAppDec {strdec, ...}) = app doDec strdec
    | doStrExp (StrLetInEnd {strdec, strexp, ...}) = (app doDec strdec; doStrExp strexp)
  and doQDecl (QuoteAntiq {exp, ...}) = doExp exp
    | doQDecl _ = ()
  fun loop () = case parseDec () of
    NONE => push (DString.size body)
  | SOME d => (doDec d; loop ())
  in loop () end

end
