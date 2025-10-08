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

type printer = {token: string -> unit}

fun token s (pr: printer) = #token pr s
fun ident id = token (#2 id)

fun otoken NONE _ _ = ()
  | otoken (SOME _) s pr = token s pr

fun delimited left {args, ...} f delim right pr = (
  left pr;
  case args of
    [] => ()
  | e :: args => (f e pr; app (fn e => (delim pr; f e pr)) args);
  right pr)

fun seq _ Empty _ = ()
  | seq f (One a) pr = f a pr
  | seq f (Many {elems, ...}) pr = delimited (token "(") elems f (token ",") (token ")") pr

fun parenIf false f pr = f pr
  | parenIf true f pr = (token "(" pr; f pr; token ")" pr)

fun fromTy _ (TyVar id) pr = ident id pr
  | fromTy _ (TyRecord {elems, ...}) pr = let
    fun f {start, lab, ty, ...} pr = let
      val lab = Option.getOpt (lab, (start, "_"))
      in ident lab pr; token ":" pr; fromTy false ty pr end
    in delimited (token "{") elems f (token ",") (token "]") pr end
  | fromTy prec (TyTuple args) pr =
    parenIf prec (delimited (K ()) args (fromTy true) (token "*") (K ())) pr
  | fromTy _ (TyCon {args, id}) pr = (seq (fromTy false) args pr; ident id pr)
  | fromTy prec (TyArrow {from, to, ...}) pr =
    parenIf prec (fn pr => (fromTy true from pr; token "->" pr; fromTy false to pr)) pr
  | fromTy prec (TyParens {ty, ...}) pr = fromTy prec ty pr
  | fromTy _ (BadTy _) pr = token "bad" pr
val fromTy = fromTy false

fun fromTyBind ({tyvars, tycon, bind}:tybind) pr = (
  seq ident tyvars pr; ident tycon pr;
  Option.app (fn {ty, ...} => (token "=" pr; fromTy ty pr)) bind)

fun fromTypeDec kw binds = delimited (token kw) binds fromTyBind (token "and") (K ())

fun fromDatBinds kw dat wt pr = let
  fun f {op_, id, arg, ...} pr = (
    otoken op_ "op" pr; ident id pr;
    Option.app (fn {ty, ...} => (token "of" pr; fromTy ty pr)) arg)
  fun g ({tyvars, tycon, rhs, ...}:datbind) pr = (
    seq ident tyvars pr; ident tycon pr; token "=" pr;
    case rhs of
      DatvalDatatype {id, ...} => (token "datatype" pr; ident id pr)
    | DatvalElems args => delimited (token kw) {args = args, delims = []} f (token "|") (K ()) pr)
  val _ = delimited (token kw) dat g (token "and") (K ()) pr
  in Option.app (fn {tybind, ...} => fromTypeDec "withtype" tybind pr) wt end

val atomicPrec = 9
val appPrec = 8
val infixPrec = 7
val typedPrec = 6
val layeredPrec = 5
(* val orPatPrec = 4 *)
val kwPrec = 3
val andPrec = 2
val orPrec = 1
val handlePrec = 0

fun fromExp' _ (Wild _) pr = token "_" pr
  | fromExp' _ (IntegerConstant (_, s)) pr = token s pr
  | fromExp' _ (WordConstant (_, s)) pr = token s pr
  | fromExp' _ (StringConstant (_, s)) pr = let
    val s = decodeStr s 1 (size s - 1)
    in token (encodeStr (Substring.full s) "\"" "\"") pr end
  | fromExp' _ (CharConstant (_, s)) pr = let
    val s = decodeStr s 2 (size s - 1)
    in token (encodeStr (Substring.full s) "#\"" "\"") pr end
  | fromExp' _ (RealConstant (_, s)) pr = token s pr
  | fromExp' _ (Unit _) pr = token "()" pr
  | fromExp' _ (Ident {op_, id}) pr = (otoken op_ "op" pr; ident id pr)
  | fromExp' _ (List {elems, ...}) pr =
    delimited (token "[") elems fromExp (token ",") (token "]") pr
  | fromExp' _ (Tuple {elems, ...}) pr =
    delimited (token "(") elems fromExp (token ",") (token ")") pr
  | fromExp' _ (Record {elems, ...}) pr =
    delimited (token "{") elems fromRow (token ",") (token "}") pr
  | fromExp' _ (Parens {exp, ...}) pr = fromExp exp pr
  | fromExp' prec (Infix {left, id, right}) pr = parenIf (prec > infixPrec) (fn pr => (
    fromExp' appPrec left pr; ident id pr; fromExp' atomicPrec right pr)) pr
  | fromExp' prec (Typed {exp, ty, ...}) pr = parenIf (prec > typedPrec) (fn pr => (
    fromExp' appPrec exp pr; token ":" pr; fromTy ty pr)) pr
  | fromExp' prec (Layered {op_, id, ty, pat, ...}) pr = parenIf (prec > typedPrec) (fn pr => (
    otoken op_ "op" pr; ident id pr;
    Option.app (fn {ty, ...} => (token ":" pr; fromTy ty pr)) ty;
    fromExp pat pr)) pr
  | fromExp' _ (Or _) _ = raise Fail "unexpanded or pattern"
  | fromExp' _ (Select {label, ...}) pr = (token "#" pr; ident label pr)
  | fromExp' _ (Sequence {elems, ...}) pr =
    delimited (token "(") elems fromExp (token ";") (token ")") pr
  | fromExp' _ (LetInEnd {dec, exps, ...}) pr = (
    token "let" pr; fromDecs dec pr; token "in" pr;
    case #args exps of [] => token "()" pr | _ =>
      delimited (K ()) exps fromExp (token ";") (K ()) pr;
    token "end" pr)
  | fromExp' prec (App (f, e)) pr = parenIf (prec > appPrec) (fn pr => (
    fromExp' appPrec f pr; fromExp' atomicPrec e pr)) pr
  | fromExp' prec (AndAlso {left, right, ...}) pr = parenIf (prec > andPrec) (fn pr => (
    fromExp' kwPrec left pr; token "andalso" pr; fromExp' andPrec right pr)) pr
  | fromExp' prec (OrElse {left, right, ...}) pr = parenIf (prec > orPrec) (fn pr => (
    fromExp' andPrec left pr; token "orelse" pr; fromExp' orPrec right pr)) pr
  | fromExp' prec (Handle {exp, elems, ...}) pr = parenIf (prec > handlePrec) (fn pr => (
    fromExp' orPrec exp pr; token "handle" pr; fromArms elems pr)) pr
  | fromExp' prec (Raise {exp, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "raise" pr; fromExp exp pr)) pr
  | fromExp' prec (IfThenElse {exp1, exp2, else_, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "if" pr; fromExp exp1 pr; token "then" pr; fromExp exp2 pr;
    case else_ of
      NONE => (token "else" pr; token "()" pr)
    | SOME {exp3, ...} => (token "else" pr; fromExp exp3 pr))) pr
  | fromExp' prec (While {exp1, exp2, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "while" pr; fromExp exp1 pr; token "do" pr; fromExp exp2 pr)) pr
  | fromExp' prec (Case {exp, elems, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "case" pr; fromExp exp pr; token "of" pr; fromArms elems pr)) pr
  | fromExp' prec (Fn {elems, ...}) pr = parenIf (prec > kwPrec) (fn pr => (
    token "fn" pr; fromArms elems pr)) pr
  | fromExp' _ (HOLFullQuote _)      _ = raise Fail "unexpanded HOL syntax"
  | fromExp' _ (HOLQuote _)          _ = raise Fail "unexpanded HOL syntax"
  | fromExp' _ (HOLLinePragma _)     _ = raise Fail "unexpanded HOL syntax"
  | fromExp' _ (HOLLinePragmaWith _) _ = raise Fail "unexpanded HOL syntax"
  | fromExp' _ (HOLFilePragma _)     _ = raise Fail "unexpanded HOL syntax"
  | fromExp' _ (HOLFilePragmaWith _) _ = raise Fail "unexpanded HOL syntax"
  | fromExp' _ (EmptyExp _)          _ = raise Fail "missing expression"
  | fromExp' _ (BadExp _)            _ = raise Fail "malformed expression"

and fromExp e = fromExp' handlePrec e

and fromRow (DotDotDot _) pr = token "..." pr
  | fromRow (LabEq {lab, eq = _, exp}) pr = (ident lab pr; token "=" pr; fromExp exp pr)
  | fromRow (LabAs {id, ty, aspat}) pr = (
    ident id pr;
    Option.app (fn {ty, ...} => (token ":" pr; fromTy ty pr)) ty;
    Option.app (fn {exp, ...} => (token "as" pr; fromExp exp pr)) aspat)

and fromArms arms = let
  fun f {pat, exp, ...} pr = (fromExp pat pr; token "=>" pr; fromExp exp pr)
  in delimited (K ()) {args = arms, delims = []} f (token "|") (K ()) end

and fromDecs ds pr = app (fn d => fromDec d pr) ds

and fromDec (DecSemi _) pr = token ";" pr
  | fromDec (DecVal {tyvars, elems, ...}) pr = let
    fun f {rec_, pat, eq} pr = (
      otoken rec_ "rec" pr; fromExp pat pr;
      Option.app (fn {exp, ...} => fromExp exp pr) eq)
    in token "val" pr; seq ident tyvars pr; delimited (K ()) elems f (token "and") (K ()) pr end
  | fromDec (DecFun {tyvars, fvalbind, ...}) pr = let
    fun f {pat, exp, ...} pr = (fromExp pat pr; token "=" pr; fromExp exp pr)
    fun g arms = delimited (K ()) {args = arms, delims = []} f (token "|") (K ())
    in token "fun" pr; seq ident tyvars pr; delimited (K ()) fvalbind g (token "and") (K ()) pr end
  | fromDec (DecType {tybind, ...}) pr = fromTypeDec "type" tybind pr
  | fromDec (DecEqtype {tybind, ...}) pr = fromTypeDec "eqtype" tybind pr
  | fromDec (DecDatatype {datbind, withtype_, ...}) pr =
    fromDatBinds "datatype" datbind withtype_ pr
  | fromDec (DecAbstype {datbind, withtype_, dec, ...}) pr = (
    fromDatBinds "abstype" datbind withtype_ pr;
    token "with" pr; fromDecs dec pr; token "end" pr)
  | fromDec (DecException {elems, ...}) pr = let
    fun f (ExnNew {op_, id, arg}) pr = (
        otoken op_ "op" pr; ident id pr;
        Option.app (fn {ty, ...} => (token "of" pr; fromTy ty pr)) arg)
      | f (ExnReplicate {op_, id, tgt, ...}) pr = (
        otoken op_ "op" pr; ident id pr; token "=" pr; ident tgt pr)
    in token "exception" pr; delimited (K ()) elems f (token "and") (K ()) pr end
  | fromDec (DecLocal {dec1, dec2, ...}) pr = (
    token "local" pr; fromDecs dec1 pr; token "in" pr; fromDecs dec2 pr; token "end" pr)
  | fromDec (DecOpen {elems, ...}) pr = (token "open" pr; app (C ident pr) elems)
  | fromDec (DecInfix {prec, elems, ...}) pr = (
    token "infix" pr; Option.app (C ident pr) prec; app (C ident pr) elems)
  | fromDec (DecInfixr {prec, elems, ...}) pr = (
    token "infixr" pr; Option.app (C ident pr) prec; app (C ident pr) elems)
  | fromDec (DecNonfix {elems, ...}) pr = (token "nonfix" pr; app (C ident pr) elems)
  | fromDec (DecStructure {elems, ...}) pr = let
    fun f {id, constraint, bind} pr = (
      ident id pr; fromConstraint constraint pr;
      Option.app (fn {strexp, ...} => (token "=" pr; fromStrExp strexp pr)) bind)
    in delimited (token "structure") elems f (token "and") (K ()) pr end
  | fromDec (DecSignature {elems, ...}) pr = let
    fun f {id, bind} pr = (
      ident id pr;
      Option.app (fn {sigexp, ...} => (token "=" pr; fromSigExp sigexp pr)) bind)
    in delimited (token "signature") elems f (token "and") (K ()) pr end
  | fromDec (DecInclude {sigexps, ...}) pr = (token "include" pr; app (C fromSigExp pr) sigexps)
  | fromDec (Sharing {type_, elems, ...}) pr = (
    token "sharing" pr; otoken type_ "type" pr;
    delimited (otoken type_ "type") elems ident (token "=") (K ()) pr)
  | fromDec (DecFunctor {elems, ...}) pr = let
    fun f {id, funarg, constraint, bind, ...} pr = (
      ident id pr; token "(" pr;
      case funarg of
        ArgIdent {strid, ty} => (
        ident strid pr;
        Option.app (fn {sigexp, ...} => (token ":" pr; fromSigExp sigexp pr)) ty)
      | ArgSpec dec => fromDecs dec pr;
      token ")" pr; fromConstraint constraint pr;
      Option.app (fn {strexp, ...} => (token "=" pr; fromStrExp strexp pr)) bind)
    in delimited (token "functor") elems f (token "and") (K ()) pr end
  | fromDec (DecExp _)           _ = raise Fail "unexpended top-level expression"
  | fromDec (HOLTheory _)        _ = raise Fail "unexpanded HOL syntax"
  | fromDec (HOLDefinition _)    _ = raise Fail "unexpanded HOL syntax"
  | fromDec (HOLDatatype _)      _ = raise Fail "unexpanded HOL syntax"
  | fromDec (HOLQuoteDecl _)     _ = raise Fail "unexpanded HOL syntax"
  | fromDec (HOLInductiveDecl _) _ = raise Fail "unexpanded HOL syntax"
  | fromDec (HOLType _)          _ = raise Fail "unexpanded HOL syntax"
  | fromDec (HOLSimpleThm _)     _ = raise Fail "unexpanded HOL syntax"
  | fromDec (HOLTheoremDecl _)   _ = raise Fail "unexpanded HOL syntax"

  and fromConstraint NONE _ = ()
    | fromConstraint (SOME {colon = (_, Colon), sigexp}) pr =
      (token ":" pr; fromSigExp sigexp pr)
    | fromConstraint (SOME {colon = (_, ColonGt), sigexp}) pr =
      (token ":>" pr; fromSigExp sigexp pr)

  and fromSigExp (SigIdent id) pr = ident id pr
    | fromSigExp (Spec {spec, ...}) pr = (token "sig" pr; fromDecs spec pr; token "end" pr)
    | fromSigExp (WhereType {sigexp, elems, ...}) pr = let
      fun f {tybind, ...} pr = (token "type" pr; fromTyBind tybind pr)
      in fromSigExp sigexp pr; delimited (token "where") elems f (token "and") (K ()) pr end

  and fromStrExp (StrIdent id) pr = ident id pr
    | fromStrExp (StrStruct {strdec, ...}) pr = (
      token "struct" pr; fromDecs strdec pr; token "end" pr)
    | fromStrExp (StrConstraint {strexp, kind}) pr = (
      fromStrExp strexp pr; fromConstraint (SOME kind) pr)
    | fromStrExp (FunAppExp {funid, strexp, ...}) pr = (
      ident funid pr; token "(" pr; fromStrExp strexp pr; token ")" pr)
    | fromStrExp (FunAppDec {funid, strdec, ...}) pr = (
      ident funid pr; token "(" pr; fromDecs strdec pr; token ")" pr)
    | fromStrExp (StrLetInEnd {strdec, strexp, ...}) pr = (
      token "let" pr; fromDecs strdec pr; token "in" pr; fromStrExp strexp pr; token "end" pr)

end;
