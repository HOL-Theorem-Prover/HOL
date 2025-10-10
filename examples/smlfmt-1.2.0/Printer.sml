structure Printer = struct
open Ast

datatype lazyseq =
    Nil
  | String of string * (unit -> lazyseq)

fun str s = String (s, fn () => Nil)
fun ch c = str (String.str c)

fun append Nil y = y ()
  | append (String (s, x)) y = String (s, fn () => append (x ()) y)

fun flatmap _ [] = Nil
  | flatmap f (x :: xs) = append (f x) (fn () => flatmap f xs)

type printer = {token: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit}

fun mkPrinter {str, startSpan, stopSpan} = {
  token = fn s => (str s; str " "),
  startSpan = startSpan, stopSpan = stopSpan }

fun token s (pr: printer) = #token pr s

fun spanned sp f (pr: printer) = let
  val _ = #startSpan pr sp
  val a = f pr
  in #stopSpan pr (); a end

fun ident id = token (#2 id)

fun otoken NONE _ _ = ()
  | otoken (SOME _) s pr = token s pr

fun delimited left args f delim right pr = (
  left pr;
  case args of
    [] => ()
  | e :: args => (f e pr; app (fn e => (delim pr; f e pr)) args);
  right pr)

fun seq _ Empty _ = ()
  | seq f (One a) pr = f a pr
  | seq f (Many {elems, ...}) pr = delimited (token "(") (#args elems) f (token ",") (token ")") pr

fun parenIf false f pr = f pr
  | parenIf true f pr = (token "(" pr; f pr; token ")" pr)

fun printTyCore _ (TyVar id) pr = ident id pr
  | printTyCore _ (TyRecord {elems = {args, ...}, ...}) pr = let
    fun f {start, lab, ty, ...} pr = let
      val lab = Option.getOpt (lab, (start, "_"))
      in ident lab pr; token ":" pr; printTy false ty pr end
    in delimited (token "{") args f (token ",") (token "]") pr end
  | printTyCore prec (TyTuple {args, ...}) pr =
    parenIf prec (delimited (K ()) args (printTy true) (token "*") (K ())) pr
  | printTyCore _ (TyCon {args, id}) pr = (seq (printTy false) args pr; ident id pr)
  | printTyCore prec (TyArrow {from, to, ...}) pr =
    parenIf prec (fn pr => (printTy true from pr; token "->" pr; printTy false to pr)) pr
  | printTyCore prec (TyParens {ty, ...}) pr = printTy prec ty pr
  | printTyCore _ (BadTy _) pr = token "bad" pr
and printTy prec ty pr = spanned (tySpan ty) (printTyCore prec ty) pr
val printTy = printTy false

fun printTyBind ({tyvars, tycon, bind}:tybind) pr = (
  seq ident tyvars pr; ident tycon pr;
  Option.app (fn {ty, ...} => (token "=" pr; printTy ty pr)) bind)

fun printTypeDec kw {args, ...} = delimited (token kw) args printTyBind (token "and") (K ())

fun printDatBinds kw {args, ...} wt pr = let
  fun f {op_, id, arg, ...} pr = (
    otoken op_ "op" pr; ident id pr;
    Option.app (fn {ty, ...} => (token "of" pr; printTy ty pr)) arg)
  fun g ({tyvars, tycon, rhs, ...}:datbind) pr = (
    seq ident tyvars pr; ident tycon pr; token "=" pr;
    case rhs of
      DatvalDatatype {id, ...} => (token "datatype" pr; ident id pr)
    | DatvalElems args => delimited (token kw) args f (token "|") (K ()) pr)
  val _ = delimited (token kw) args g (token "and") (K ()) pr
  in Option.app (fn {tybind, ...} => printTypeDec "withtype" tybind pr) wt end

fun printDecs parseError = let

val atomicPrec = 7
val appPrec = 6
val infixPrec = 5
val typedPrec = 4
val kwPrec = 3
val andPrec = 2
val orPrec = 1
val handlePrec = 0

fun printExpCore _ (Wild _) pr = token "_" pr
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
    delimited (token "[") args printExp (token ",") (token "]") pr
  | printExpCore _ (Tuple {elems = {args, ...}, ...}) pr =
    delimited (token "(") args printExp (token ",") (token ")") pr
  | printExpCore _ (Record {elems = {args, ...}, ...}) pr =
    delimited (token "{") args printRow (token ",") (token "}") pr
  | printExpCore prec (Parens {exp, ...}) pr = printExp' prec exp pr
  | printExpCore prec (Infix {left, id, right}) pr = parenIf (prec > infixPrec) (fn pr => (
    printExp' appPrec left pr; ident id pr; printExp' appPrec right pr)) pr
  | printExpCore prec (Typed {exp, ty, ...}) pr = parenIf (prec > typedPrec) (fn pr => (
    printExp' typedPrec exp pr; token ":" pr; printTy ty pr)) pr
  | printExpCore prec (Layered {op_, id, ty, pat, ...}) pr = parenIf (prec > typedPrec) (fn pr => (
    otoken op_ "op" pr; ident id pr;
    Option.app (fn {ty, ...} => (token ":" pr; printTy ty pr)) ty;
    printExp pat pr)) pr
  | printExpCore _ (Or _) _ = raise Fail "unexpanded or pattern"
  | printExpCore _ (Select {label, ...}) pr = (token "#" pr; ident label pr)
  | printExpCore _ (Sequence {elems = {args, ...}, ...}) pr =
    delimited (token "(") args printExp (token ";") (token ")") pr
  | printExpCore _ (LetInEnd {dec, exps = {args, ...}, ...}) pr = (
    token "let" pr; printDecs dec pr; token "in" pr;
    case args of [] => token "()" pr | _ =>
      delimited (K ()) args printExp (token ";") (K ()) pr;
    token "end" pr)
  | printExpCore prec (App (f, e)) pr = parenIf (prec > appPrec) (fn pr => (
    printExp' appPrec f pr; printExp' atomicPrec e pr)) pr
  | printExpCore prec (AndAlso {left, right, ...}) pr = parenIf (prec > andPrec) (fn pr => (
    printExp' kwPrec left pr; token "andalso" pr; printExp' andPrec right pr)) pr
  | printExpCore prec (OrElse {left, right, ...}) pr = parenIf (prec > orPrec) (fn pr => (
    printExp' andPrec left pr; token "orelse" pr; printExp' orPrec right pr)) pr
  | printExpCore prec (Handle {exp, elems, ...}) pr = parenIf (prec > handlePrec) (fn pr => (
    printExp' orPrec exp pr; token "handle" pr; printArms elems pr)) pr
  | printExpCore prec (Raise {exp, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "raise" pr; printExp exp pr)) pr
  | printExpCore prec (IfThenElse {exp1, exp2, else_, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "if" pr; printExp exp1 pr; token "then" pr; printExp exp2 pr;
    case else_ of
      NONE => (token "else" pr; token "()" pr)
    | SOME {exp3, ...} => (token "else" pr; printExp exp3 pr))) pr
  | printExpCore prec (While {exp1, exp2, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "while" pr; printExp exp1 pr; token "do" pr; printExp exp2 pr)) pr
  | printExpCore prec (Case {exp, elems, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "case" pr; printExp exp pr; token "of" pr; printArms elems pr)) pr
  | printExpCore prec (Fn {elems, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "fn" pr; printArms elems pr)) pr
  | printExpCore _ (HOLFullQuote _)      _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLQuote _)          _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLLinePragma _)     _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLLinePragmaWith _) _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLFilePragma _)     _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (HOLFilePragmaWith _) _ = raise Fail "unexpanded HOL syntax"
  | printExpCore _ (EmptyExp _)          pr = token "(raise Fail \"empty\")" pr
  | printExpCore _ (BadExp _)            pr = token "(raise Fail \"malformed expression\")" pr

and printExp' prec e pr = spanned (expSpan e) (printExpCore prec e) pr

and printExp e = printExp' handlePrec e

and printRow (DotDotDot _) pr = token "..." pr
  | printRow (LabEq {lab, eq = _, exp}) pr = (ident lab pr; token "=" pr; printExp exp pr)
  | printRow (LabAs {id, ty, aspat}) pr = (
    ident id pr;
    Option.app (fn {ty, ...} => (token ":" pr; printTy ty pr)) ty;
    Option.app (fn {exp, ...} => (token "as" pr; printExp exp pr)) aspat)

and printArms arms = let
  fun f {pat, exp, ...} pr = (printExp pat pr; token "=>" pr; printExp exp pr)
  in delimited (K ()) arms f (token "|") (K ()) end

and printDecs ds pr = app (fn d => spanned (decSpan d) (printDec d) pr) ds

and printDec (DecSemi _) pr = token ";" pr
  | printDec (DecVal {tyvars, elems = {args, ...}, ...}) pr = let
    fun f {rec_, pat, eq} pr = (
      otoken rec_ "rec" pr; printExp pat pr;
      Option.app (fn {exp, ...} => (token "=" pr; printExp exp pr)) eq)
    in token "val" pr; seq ident tyvars pr; delimited (K ()) args f (token "and") (K ()) pr end
  | printDec (DecFun {tyvars, fvalbind = {args, ...}, ...}) pr = let
    fun f {pat, exp, ...} pr = (printExp pat pr; token "=" pr; printExp exp pr)
    fun g arms = delimited (K ()) arms f (token "|") (K ())
    in token "fun" pr; seq ident tyvars pr; delimited (K ()) args g (token "and") (K ()) pr end
  | printDec (DecType {tybind, ...}) pr = printTypeDec "type" tybind pr
  | printDec (DecEqtype {tybind, ...}) pr = printTypeDec "eqtype" tybind pr
  | printDec (DecDatatype {datbind, withtype_, ...}) pr =
    printDatBinds "datatype" datbind withtype_ pr
  | printDec (DecAbstype {datbind, withtype_, dec, ...}) pr = (
    printDatBinds "abstype" datbind withtype_ pr;
    token "with" pr; printDecs dec pr; token "end" pr)
  | printDec (DecException {elems = {args, ...}, ...}) pr = let
    fun f (ExnNew {op_, id, arg}) pr = (
        otoken op_ "op" pr; ident id pr;
        Option.app (fn {ty, ...} => (token "of" pr; printTy ty pr)) arg)
      | f (ExnReplicate {op_, id, tgt, ...}) pr = (
        otoken op_ "op" pr; ident id pr; token "=" pr; ident tgt pr)
    in token "exception" pr; delimited (K ()) args f (token "and") (K ()) pr end
  | printDec (DecLocal {dec1, dec2, ...}) pr = (
    token "local" pr; printDecs dec1 pr; token "in" pr; printDecs dec2 pr; token "end" pr)
  | printDec (DecOpen {elems, ...}) pr = (token "open" pr; app (C ident pr) elems)
  | printDec (DecInfix {prec, elems, ...}) pr = (
    token "infix" pr; Option.app (C ident pr) prec; app (C ident pr) elems)
  | printDec (DecInfixr {prec, elems, ...}) pr = (
    token "infixr" pr; Option.app (C ident pr) prec; app (C ident pr) elems)
  | printDec (DecNonfix {elems, ...}) pr = (token "nonfix" pr; app (C ident pr) elems)
  | printDec (DecStructure {elems = {args, ...}, ...}) pr = let
    fun f {id, constraint, bind} pr = (
      ident id pr; printConstraint constraint pr;
      Option.app (fn {strexp, ...} => (token "=" pr; printStrExp strexp pr)) bind)
    in delimited (token "structure") args f (token "and") (K ()) pr end
  | printDec (DecSignature {elems = {args, ...}, ...}) pr = let
    fun f {id, bind} pr = (
      ident id pr;
      Option.app (fn {sigexp, ...} => (token "=" pr; printSigExp sigexp pr)) bind)
    in delimited (token "signature") args f (token "and") (K ()) pr end
  | printDec (DecInclude {sigexps, ...}) pr = (token "include" pr; app (C printSigExp pr) sigexps)
  | printDec (Sharing {type_, elems = {args, ...}, ...}) pr = (
    token "sharing" pr; otoken type_ "type" pr;
    delimited (otoken type_ "type") args ident (token "=") (K ()) pr)
  | printDec (DecFunctor {elems = {args, ...}, ...}) pr = let
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
  | printDec (DecExp _)           _ = raise Fail "unexpended top-level expression"
  | printDec (HOLTheory _)        _ = raise Fail "unexpanded HOL syntax"
  | printDec (HOLDefinition _)    _ = raise Fail "unexpanded HOL syntax"
  | printDec (HOLDatatype _)      _ = raise Fail "unexpanded HOL syntax"
  | printDec (HOLQuoteDecl _)     _ = raise Fail "unexpanded HOL syntax"
  | printDec (HOLInductiveDecl _) _ = raise Fail "unexpanded HOL syntax"
  | printDec (HOLType _)          _ = raise Fail "unexpanded HOL syntax"
  | printDec (HOLSimpleThm _)     _ = raise Fail "unexpanded HOL syntax"
  | printDec (HOLTheoremDecl _)   _ = raise Fail "unexpanded HOL syntax"

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

in printDecs end

end;
