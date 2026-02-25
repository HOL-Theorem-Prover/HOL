structure HOLPrinter :> HOLPrinter = struct
open HOLAst

fun K a _ = a
fun C f x y = f y x

type printer = {token: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit}

fun mkPrinter {str, startSpan, stopSpan} = {
  token = fn s => (str s; str " "),
  startSpan = startSpan, stopSpan = stopSpan }

fun token s (pr: printer) = #token pr s

fun spanned sp f (pr: printer) = let
  val _ = #startSpan pr sp
  val a = f pr
  in #stopSpan pr (); a end

fun ident (p, id) = spanned (p, p + size id) (token id)

fun otoken NONE _ _ = ()
  | otoken (SOME _) s pr = token s pr

fun delimited left args f delim right pr = (
  left pr;
  case args of
    [] => ()
  | e :: args => (f e pr; app (fn e => (delim pr; f e pr)) args);
  right pr)

fun delimitedBar left args f right pr = let
  fun go [] = ()
    | go [e] = f NONE e pr
    | go (e :: args) = (f (SOME true) e pr; token "|" pr; go args)
  in left pr; go args; right pr end

fun seq _ Empty _ = ()
  | seq f (One a) pr = f true a pr
  | seq f (Many {elems, ...}) pr = delimited
     (token "(") (#args elems) (f false) (token ",") (token ")") pr

fun parenIf false f pr = f (false, pr)
  | parenIf true f pr = (token "(" pr; f (true, pr); token ")" pr)

fun printTyCore _ (TyVar id) pr = ident id pr
  | printTyCore _ (TyRecord {elems = {args, ...}, ...}) pr = let
    fun f {start, lab, ty, ...} pr = let
      val lab = Option.getOpt (lab, (start, "_"))
      in ident lab pr; token ":" pr; printTy false ty pr end
    in delimited (token "{") args f (token ",") (token "}") pr end
  | printTyCore prec (TyTuple {args, ...}) pr =
    parenIf prec (delimited (K ()) args (printTy true) (token "*") (K ()) o #2) pr
  | printTyCore _ (TyCon {args, id}) pr = (seq printTy args pr; ident id pr)
  | printTyCore prec (TyArrow {from, to, ...}) pr =
    parenIf prec (fn (_,pr) => (printTy true from pr; token "->" pr; printTy false to pr)) pr
  | printTyCore prec (TyParens {ty, ...}) pr = printTy prec ty pr
  | printTyCore _ (BadTy _) pr = token "bad" pr
and printTy prec ty pr = spanned (tySpan ty) (printTyCore prec ty) pr
val printTy = printTy false

fun printTyBind ({tyvars, tycon, bind}:tybind) pr = (
  seq (K ident) tyvars pr; ident tycon pr;
  Option.app (fn {ty, ...} => (token "=" pr; printTy ty pr)) bind)

fun printTypeDec kw {args, ...} = delimited (token kw) args printTyBind (token "and") (K ())

fun printDatBinds kw {args, ...} wt pr = let
  fun f {op_, id, arg, ...} pr = (
    otoken op_ "op" pr; ident id pr;
    Option.app (fn {ty, ...} => (token "of" pr; printTy ty pr)) arg)
  fun g ({tyvars, tycon, rhs, ...}:datbind) pr = (
    seq (K ident) tyvars pr; ident tycon pr; token "=" pr;
    case rhs of
      DatvalDatatype {id, ...} => (token "datatype" pr; ident id pr)
    | DatvalElems args => delimited (K ()) args f (token "|") (K ()) pr)
  val _ = delimited (token kw) args g (token "and") (K ()) pr
  in Option.app (fn {tybind, ...} => printTypeDec "withtype" tybind pr) wt end

fun print parseError = let

val atomicPrec = 7
val appPrec = 6
val infixPrec = 5
val typedPrec = 4
val kwPrec = 3
val andPrec = 2
val orPrec = 1
val handlePrec = 0

fun resetTrail true _ = NONE
  | resetTrail false trail = trail

fun printExp trail = printExp' (trail, handlePrec)
and printExp' (prec:bool option * int) e = spanned (expSpan e) (printExpCore prec e)
and printExpCore (_:bool option * int) (Wild _) pr = token "_" pr
  | printExpCore _ (IntegerConstant (_, s)) pr = token s pr
  | printExpCore _ (WordConstant (_, s)) pr = token s pr
  | printExpCore _ (StringConstant (_, s)) pr = let
    val s = decodeStr parseError s 1 (size s - 1)
    in token (encodeStr (Substring.full s) "\"" "\"") pr end
  | printExpCore _ (CharConstant (_, s)) pr = let
    val s = decodeStr parseError s 2 (size s - 1)
    in token (encodeStr (Substring.full s) "#\"" "\"") pr end
  | printExpCore _ (RealConstant (_, s)) pr = token s pr
  | printExpCore _ (Unit _) pr = token "()" pr
  | printExpCore _ (Ident {op_, id}) pr = (otoken op_ "op" pr; ident id pr)
  | printExpCore _ (List {elems = {args, ...}, ...}) pr =
    delimited (token "[") args (printExp NONE) (token ",") (token "]") pr
  | printExpCore _ (Tuple {elems = {args, ...}, ...}) pr =
    delimited (token "(") args (printExp NONE) (token ",") (token ")") pr
  | printExpCore _ (Record {elems = {args, ...}, ...}) pr =
    delimited (token "{") args printRow (token ",") (token "}") pr
  | printExpCore prec (Parens {exp, left, stop, ...}) pr =
    parenIf (expSpan exp <> (left, stop)) (fn (paren, pr) =>
      printExp' (if paren then (NONE, handlePrec) else prec) exp pr) pr
  | printExpCore (trail, prec) (Infix {left, id, right}) pr =
    parenIf (prec > infixPrec) (fn (paren, pr) => (
      printExp' (SOME false, appPrec) left pr; ident id pr;
      printExp' (resetTrail paren trail, appPrec) right pr)) pr
  | printExpCore (_, prec) (Typed {exp, ty, ...}) pr = parenIf (prec > typedPrec) (fn (_,pr) => (
    printExp' (SOME false, typedPrec) exp pr; token ":" pr; printTy ty pr)) pr
  | printExpCore (trail, prec) (Layered {op_, id, ty, pat, ...}) pr =
    parenIf (prec > typedPrec) (fn (paren, pr) => (
      otoken op_ "op" pr; ident id pr;
      Option.app (fn {ty, ...} => (token ":" pr; printTy ty pr)) ty;
      token "as" pr; printExp (resetTrail paren trail) pat pr)) pr
  | printExpCore _ (Or _) _ = raise Fail "unexpanded or pattern"
  | printExpCore _ (Select {label, ...}) pr = (token "#" pr; ident label pr)
  | printExpCore _ (Sequence {elems = {args, ...}, ...}) pr =
    delimited (token "(") args (printExp NONE) (token ";") (token ")") pr
  | printExpCore _ (LetInEnd {dec, exps = {args, ...}, ...}) pr = (
    token "let" pr; printDecs dec pr; token "in" pr;
    case args of [] => token "()" pr | _ =>
      delimited (K ()) args (printExp NONE) (token ";") (K ()) pr;
    token "end" pr)
  | printExpCore (trail, prec) (App (f, e)) pr =
    parenIf (prec > appPrec) (fn (paren, pr) => (
      printExp' (SOME false, appPrec) f pr;
      printExp' (resetTrail paren trail, atomicPrec) e pr)) pr
  | printExpCore (trail, prec) (AndAlso {left, right, ...}) pr =
    parenIf (prec > andPrec) (fn (paren, pr) => (
      printExp' (SOME false, kwPrec) left pr; token "andalso" pr;
      printExp' (resetTrail paren trail, andPrec) right pr)) pr
  | printExpCore (trail, prec) (OrElse {left, right, ...}) pr =
    parenIf (prec > orPrec) (fn (paren, pr) => (
      printExp' (SOME false, andPrec) left pr; token "orelse" pr;
      printExp' (resetTrail paren trail, orPrec) right pr)) pr
  | printExpCore (trail, prec) (Handle {exp, elems, ...}) pr =
    parenIf (trail <> NONE orelse prec > handlePrec) (fn (_, pr) => (
      printExp' (SOME false, orPrec) exp pr; token "handle" pr;
      printArms elems pr)) pr
  | printExpCore (trail, prec) (Raise {exp, ...}) pr =
    parenIf (trail = SOME false orelse prec > kwPrec) (fn (paren, pr) => (
      token "raise" pr; printExp (resetTrail paren trail) exp pr)) pr
  | printExpCore (trail, prec) (IfThenElse {exp1, exp2, else_, ...}) pr =
    parenIf (trail = SOME false orelse prec > kwPrec) (fn (paren, pr) => (
      token "if" pr; printExp NONE exp1 pr; token "then" pr;
      printExp NONE exp2 pr; token "else" pr;
      case else_ of
        NONE => token "()" pr
      | SOME {exp3, ...} => printExp (resetTrail paren trail) exp3 pr)) pr
  | printExpCore (trail, prec) (While {exp1, exp2, ...}) pr =
    parenIf (trail = SOME false orelse prec > kwPrec) (fn (paren, pr) => (
      token "while" pr; printExp NONE exp1 pr;
      token "do" pr; printExp (resetTrail paren trail) exp2 pr)) pr
  | printExpCore (trail, prec) (Case {exp, elems, ...}) pr =
    parenIf (trail <> NONE orelse prec > kwPrec) (fn (_, pr) => (
      token "case" pr; printExp NONE exp pr; token "of" pr;
      printArms elems pr)) pr
  | printExpCore (trail, prec) (Fn {elems, ...}) pr =
    parenIf (trail <> NONE orelse prec > kwPrec) (fn (_, pr) => (
      token "fn" pr; printArms elems pr)) pr
  | printExpCore _ (HOLFullQuote _)      _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLQuote _)          _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLLinePragma _)     _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLLinePragmaWith _) _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLFilePragma _)     _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLFilePragmaWith _) _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (ExpEmpty _)          pr = token "(raise Fail \"empty\")" pr
  | printExpCore _ (ExpBad _)            pr = token "(raise Fail \"malformed expression\")" pr
  | printExpCore prec (ExpExpansion {orig, result}) pr =
    spanned (expSpan orig) (printExpCore prec result) pr

and printExpFunPat (prec:bool option*int) e = spanned (expSpan e) (printExpFunPatCore prec e)
and printExpFunPatCore (trail, prec) (App (f, e)) pr =
    parenIf (prec > appPrec) (fn (paren, pr) => (
      printExpFunPat (SOME false, appPrec) f pr;
      printExp' (resetTrail paren trail, atomicPrec) e pr)) pr
  | printExpFunPatCore prec (Parens {exp, ...}) pr = printExpFunPat prec exp pr
  | printExpFunPatCore (trail, prec) (Infix {left, id, right}) pr =
    parenIf (prec > infixPrec) (fn (paren, pr) => (
      printExp' (SOME false, atomicPrec) left pr; ident id pr;
      printExp' (resetTrail paren trail, atomicPrec) right pr)) pr
  | printExpFunPatCore prec e pr = printExpCore prec e pr

and printRow (DotDotDot _) pr = token "..." pr
  | printRow (LabEq {lab, eq = _, exp}) pr = (ident lab pr; token "=" pr; printExp NONE exp pr)
  | printRow (LabAs {id, ty, aspat}) pr = (
    ident id pr;
    Option.app (fn {ty, ...} => (token ":" pr; printTy ty pr)) ty;
    Option.app (fn {exp, ...} => (token "as" pr; printExp NONE exp pr)) aspat)
  | printRow (LabExpansion {result, ...}) pr = printRow result pr

and printArms arms = let
  fun f trail {pat, exp, ...} pr = (printExp NONE pat pr; token "=>" pr; printExp trail exp pr)
  in delimitedBar (K ()) arms f (K ()) end

and printDecs ds pr = app (fn d => printDec d pr) ds

and printDec dec = spanned (decSpan dec) (printDecCore dec)
and printDecCore (DecSemi _) pr = token ";" pr
  | printDecCore (DecVal {tyvars, elems = {args, ...}, ...}) pr = let
    fun f {rec_, pat, eq} pr = (
      otoken rec_ "rec" pr; printExp (SOME false) pat pr;
      Option.app (fn {exp, ...} => (token "=" pr; printExp NONE exp pr)) eq)
    in token "val" pr; seq (K ident) tyvars pr; delimited (K ()) args f (token "and") (K ()) pr end
  | printDecCore (DecFun {tyvars, fvalbind = {args, ...}, ...}) pr = let
    fun f nobar {pat, exp, ...} pr =
      (printExpFunPat (SOME false, handlePrec) pat pr; token "=" pr; printExp nobar exp pr)
    fun g arms = delimitedBar (K ()) arms f (K ())
    in token "fun" pr; seq (K ident) tyvars pr; delimited (K ()) args g (token "and") (K ()) pr end
  | printDecCore (DecType {tybind, ...}) pr = printTypeDec "type" tybind pr
  | printDecCore (DecEqtype {tybind, ...}) pr = printTypeDec "eqtype" tybind pr
  | printDecCore (DecDatatype {datbind, withtype_, ...}) pr =
    printDatBinds "datatype" datbind withtype_ pr
  | printDecCore (DecAbstype {datbind, withtype_, dec, ...}) pr = (
    printDatBinds "abstype" datbind withtype_ pr;
    token "with" pr; printDecs dec pr; token "end" pr)
  | printDecCore (DecException {elems = {args, ...}, ...}) pr = let
    fun f (ExnNew {op_, id, arg}) pr = (
        otoken op_ "op" pr; ident id pr;
        Option.app (fn {ty, ...} => (token "of" pr; printTy ty pr)) arg)
      | f (ExnReplicate {op_, id, tgt, ...}) pr = (
        otoken op_ "op" pr; ident id pr; token "=" pr; ident tgt pr)
    in token "exception" pr; delimited (K ()) args f (token "and") (K ()) pr end
  | printDecCore (DecLocal {dec1, dec2, ...}) pr = (
    token "local" pr; printDecs dec1 pr; token "in" pr; printDecs dec2 pr; token "end" pr)
  | printDecCore (DecOpen {elems, ...}) pr = (token "open" pr; app (C ident pr) elems)
  | printDecCore (DecInfix {prec, elems, ...}) pr = (
    token "infix" pr; Option.app (C ident pr) prec; app (C ident pr) elems)
  | printDecCore (DecInfixr {prec, elems, ...}) pr = (
    token "infixr" pr; Option.app (C ident pr) prec; app (C ident pr) elems)
  | printDecCore (DecNonfix {elems, ...}) pr = (token "nonfix" pr; app (C ident pr) elems)
  | printDecCore (DecStructure {elems = {args, ...}, ...}) pr = let
    fun f {id, constraint, bind} pr = (
      ident id pr; printConstraint constraint pr;
      Option.app (fn {strexp, ...} => (token "=" pr; printStrExp strexp pr)) bind)
    in delimited (token "structure") args f (token "and") (K ()) pr end
  | printDecCore (DecSignature {elems = {args, ...}, ...}) pr = let
    fun f {id, bind} pr = (
      ident id pr;
      Option.app (fn {sigexp, ...} => (token "=" pr; printSigExp sigexp pr)) bind)
    in delimited (token "signature") args f (token "and") (K ()) pr end
  | printDecCore (DecInclude {sigexps, ...}) pr = (token "include" pr; app (C printSigExp pr) sigexps)
  | printDecCore (Sharing {type_, elems = {args, ...}, ...}) pr = (
    token "sharing" pr; delimited (otoken type_ "type") args ident (token "=") (K ()) pr)
  | printDecCore (DecFunctor {elems = {args, ...}, ...}) pr = let
    fun f {id, funarg, constraint, bind, ...} pr = (
      ident id pr; token "(" pr;
      case funarg of
        ArgIdent {strid, ty} => (
        ident strid pr;
        Option.app (fn {sigexp, ...} => (token ":" pr; printSigExp sigexp pr)) ty)
      | ArgSpec dec => printDecs dec pr;
      token ")" pr; printConstraint constraint pr;
      Option.app (fn {strexp, ...} => (token "=" pr; printStrExp strexp pr)) bind)
    in delimited (token "functor") args f (token "and") (K ()) pr end
  | printDecCore (DecExp _)           _ = raise Fail "unexpanded top-level expression"
  | printDecCore (HOLTheory _)        _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLTheoryEnd _)     _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLDefinition _)    _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLDatatype _)      _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLQuoteDecl _)     _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLInductiveDecl _) _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLType _)          _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLSimpleThm _)     _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLTheoremDecl _)   _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLResume _)        _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (HOLFinalise _)      _ = raise Fail "unexpanded HOL syntax"
  | printDecCore (DecBad _)           _ = raise Fail "unexpanded bad declaration"
  | printDecCore (DecExpansion {orig, result}) pr = spanned (decSpan orig) (printDecs result) pr

  and printConstraint NONE _ = ()
    | printConstraint (SOME {colon = (_, Colon), sigexp}) pr =
      (token ":" pr; printSigExp sigexp pr)
    | printConstraint (SOME {colon = (_, ColonGt), sigexp}) pr =
      (token ":>" pr; printSigExp sigexp pr)

  and printSigExp (SigIdent id) pr = ident id pr
    | printSigExp (Spec {spec, ...}) pr = (token "sig" pr; printDecs spec pr; token "end" pr)
    | printSigExp (WhereType {sigexp, elems = {args, ...}, ...}) pr = let
      fun f {tybind, ...} pr = (token "type" pr; printTyBind tybind pr)
      in printSigExp sigexp pr; delimited (token "where") args f (token "and") (K ()) pr end

  and printStrExp (StrIdent id) pr = ident id pr
    | printStrExp (StrStruct {strdec, ...}) pr = (
      token "struct" pr; printDecs strdec pr; token "end" pr)
    | printStrExp (StrConstraint {strexp, kind}) pr = (
      printStrExp strexp pr; printConstraint (SOME kind) pr)
    | printStrExp (FunAppExp {funid, strexp, ...}) pr = (
      ident funid pr; token "(" pr; printStrExp strexp pr; token ")" pr)
    | printStrExp (FunAppDec {funid, strdec, ...}) pr = (
      ident funid pr; token "(" pr; printDecs strdec pr; token ")" pr)
    | printStrExp (StrLetInEnd {strdec, strexp, ...}) pr = (
      token "let" pr; printDecs strdec pr; token "in" pr; printStrExp strexp pr; token "end" pr)

in {printDec = printDec, printDecs = printDecs} end
val printDec = #printDec o print
val printDecs = #printDecs o print
end;
