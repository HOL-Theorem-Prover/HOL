
structure AstNew = struct

  (* (start, content) *)
  type ident = int * string

  type 'exp delimited = {args: 'exp list, delims: int list}

  datatype 'a seq =
    Empty
  | One of 'a
  | Many of {left: int, elems: 'a delimited, right: int option, stop: int}

  datatype ty =
    TyVar of ident
  | TyRecord of (** { lab : ty, ..., lab : ty } *)
      { left: int,
        elems: {lab: ident option, colon: int option, ty: ty} delimited,
        right: int option, stop: int }
  | TyTuple of ty delimited (** ty * ... * ty *)
  | TyCon of {args: ty seq, id: ident} (** tyseq longtycon *)
  | TyArrow of {from: ty, arrow: int, to: ty} (** ty -> ty *)
  | TyParens of {left: int, ty: ty, right: int option, stop: int} (** ( ty ) *)
  | BadTy of {start: int, stop: int} (** ( ty ) *)

  (** tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
  type tybind = {tyvars: ident seq, tycon: ident, bind: {eq: int, ty: ty} option}

  (** [op] vid [of ty] [| [op] vid [of ty] ...] *)
  type conbind = {bar: ident option, op_: int option, id: ident, arg: {of_: int, ty: ty} option}

  (** tyvarseq tycon = conbind [and tyvarseq tycon = conbind ...] *)
  type datbind = {tyvars: ident seq, tycon: ident, eq: int, elems: conbind list}

  datatype exbind =
    ExnNew of {op_: int option, id: ident, arg: {of_: int, ty: ty} option}
  | ExnReplicate of {op_: int option, left_id: ident, eq: int, right_id: ident}

  datatype constraint = Colon | ColonGt

  datatype defn_label_id =
    HOLConjLabel of int * string
  | HOLLabel of {tilde_: int option, id: int * string}

  datatype exp =
    Wild of int
  | IntegerConstant of int * string (* 123 *)
  | WordConstant of int * string (* 0w123 *)
  | StringConstant of int * string (* "hallå" (includes utf-8) *)
  | CharConstant of int * string (* #"a" *)
  | RealConstant of int * string (* 1.5 *)
  | Unit of {left: int, right: int} (** () *)
  | Ident of {op_: int option, id: ident}  (** [op] longvid *)
  | List of {left: int, elems: exp delimited, right: int option, stop: int}
    (** [ exp, ..., exp ] *)
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

  | BadExp of {start: int, stop: int}

  and row =
    DotDotDot of int (** can only appear at end of record pattern *)
  | LabEq of {lab: ident, eq: int, exp: exp}
  | LabAs of {id: ident, ty: {colon: int, ty: ty} option, aspat: {as_: int, exp: exp} option}

  and dec =
    DecSemi of int (** ; *)
  | DecVal of {val_: int, tyvars: ident seq, elems: valbind delimited}
    (** val tyvarseq [rec] pat = exp [and [rec] pat = exp ...] *)
  | DecFun of {fun_: int, tyvars: ident seq, fvalbind: fvalarm list delimited}
    (** fun tyvarseq [op]vid atpat ... atpat [: ty] = exp [| ...] *)
  | DecType of {type_: int, tybind: tybind delimited}
    (** type tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
  | DecEqtype of {eqtype_: int, tybind: tybind delimited}
    (** eqtype tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
  | DecDatatype of {
      datatype_: int, datbind: datbind list delimited,
      withtype_: {withtype_: int, tybind: tybind delimited} option }
    (** datatype datbind [withtype typbind] *)
  | DecReplicateDatatype of {
      left_datatype_: int, left_id: ident, eq: int,
      right_datatype_: int, right_id: ident}
    (** datatype tycon = datatype longtycon *)
  | DecAbstype of {
      abstype_: int, datbind: datbind list delimited,
      withtype_: {withtype_: int, typbind: tybind delimited} option,
      with_: int, dec: dec list, end_: int}
    (** abstype datbind [withtype typbind] with dec end *)
  | DecException of {exception_: int, elems: exbind delimited}
    (** exception exbind *)
  | DecLocal of {local_: int, left_dec: dec list, in_: int, right_dec: dec list, end_: int}
    (** local dec in dec end *)
  | DecOpen of {open_: int, elems: ident list}
    (** open longstrid [longstrid ...] *)
  | DecInfix of {infix_: int, precedence: (int * string) option, elems: ident list}
    (** infix [d] vid [vid ...] *)
  | DecInfixr of {infixr_: int, precedence: (int * string) option, elems: ident list}
    (** infixr [d] vid [vid ...] *)
  | DecNonfix of {nonfix_: int, elems: ident list} (** nonfix vid [vid ...] *)
  | DecStructure of {
      structure_: int, elems: {
        id: ident, constraint: struct_kind option,
        bind: {eq: int, strexp: strexp} option} delimited}
    (** structure strid : sigexp = strexp [and strid : sigep = strexp ...] *)
  | DecSignature of {signature_: int, elems: {ident: ident, eq: int, sigexp: sigexp} delimited}
    (** signature sigid = sigexp [and ...] *)
  | IncludeIds of {include_: int, sigexps: sigexp list}
    (** include sigid ... sigid *)
  | Sharing of {sharing_: int, type_: int option, elems: ident delimited}
    (** sharing [type] longstrid = ... = longstrid *)
  | DecFunctor of {
      functor_: int, elems: {
        id: ident, lparen: int, funarg: funarg, rparen: int,
        constraint: struct_kind option, eq: int, strexp: strexp} delimited}
    (** functor id(funarg) [:> sigexp] = strexp [and ...] *)
  | DecExp of exp (** exp (only at top level) *)

  | HOLDefinition of {
      head: int * string, quote: qbody, termination: {tok: int, tac: exp} option,
      end_: int option, stop: int}
    (** Definition foo[attrs]: ... [Termination tac] End *)
  | HOLDatatype of {head: int * string, quote: qbody, end_tok: int option, stop: int}
    (** Datatype foo: ... End *)
  | HOLQuoteDecl of {head: int * string, quote: qbody, end_tok: int option, stop: int}
    (** Quote id: ... End *)
  | HOLQuoteEqnDecl of {head: int * string, quote: qbody, end_tok: int option, stop: int}
    (** Quote id = foo: ... End *)
  | HOLInductiveDecl of {head: int * string, quote: qbody, end_tok: int option, stop: int}
    (** [Co]Inductive id[, id]*: ... End *)
  | HOLType of {head: int * string, exp: exp} (** Type id[attrs] = exp *)
  | HOLSimpleThm of {head: int * string, exp: exp} (** Theorem id[attrs] = exp *)
  | HOLTheoremDecl of {
      head: int * string, quote: qbody, proof_: (int * string) option,
      tac: exp, qed_: int option, stop: int}
    (** Theorem foo[attrs]: ... [Proof[attrs] tac] QED *)

  and valbind =
    ValBind of {rec_: int option, pat: exp, eq: int, exp: exp}
  | ValSpec of {vid: ident, colon: int option, ty: ty}

  and funarg =
    ArgIdent of {strid: ident, colon: int, sigexp: sigexp}
  | ArgSpec of dec list

  and sigexp =
    SigIdent of ident
  | Spec of {sig_: int, spec: dec list, end_: int}
    (** sig spec end *)
  | WhereType of {
    sigexp: sigexp, elems: {
      where_: int, type_: int, tyvars: ident seq,
      tycon: ident, eq: int, ty: ty} list}
    (** sigexp where type tyvarseq tycon = ty [where type ...] *)

  and strexp =
    StrIdent of ident
  | StrStruct of {struct_: int, strdec: dec list, end_: int}
  | StrConstraint of {strexp: strexp, kind: struct_kind}
  | FunAppExp of {funid: ident, lparen: int, strexp: strexp, rparen: int}
  | FunAppDec of {funid: ident, lparen: int, strdec: dec list, rparen: int}
  | StrLetInEnd of {let_: int, strdec: dec list, in_: int, strexp: strexp, end_: int}

  and fname_args =
    PrefixedFun of {op_: int option, id: ident, args: exp list} (** fun [op]name arg1 arg2 arg3 *)
  | InfixedFun of {larg: exp, id: ident, rarg: exp} (** fun larg name rarg *)
  | CurriedInfixedFun of
    {lparen: int, larg: exp, id: int, rarg: exp, rparen: int, args: exp list}
    (** fun (larg name rarg) arg1 arg2 *)

  and qdecl =
    QuoteAntiq of {caret_: int, exp: exp, stop: int}
  | DefinitionLabel of {left: int, label: defn_label_id option,
      args: {left: int, ids: (int * string) delimited, right: int option, stop: int} option,
      colon: int option, right: int option, stop: int}
    (** [id[x,y,z]:] *)

  withtype struct_kind = {colon: int * constraint, sigexp: sigexp}

  and arm = {bar: int option, pats: exp delimited, arrow: int option, exp: exp}

  and fvalarm = {
    bar: int option, fname_args: fname_args,
    ty: {colon: int, ty: ty} option, eq: int, exp: exp}

  and qbody = {start: int, toks: qdecl list, stop: int}

end


structure ParserNew = struct
open AstNew

exception Unreachable
fun parseSML body parseError = let
  val pos = ref 0
  fun cur () = String.sub (body, !pos) handle Subscript => #"\000"
  fun ahead i = String.sub (body, !pos + i) handle Subscript => #"\000"
  fun next () = pos := !pos + 1
  fun nextn i = pos := !pos + i
  fun takeWhile f = if f (cur ()) then (next (); takeWhile f) else ()
  fun ws () = takeWhile Char.isSpace
  fun isIdRest c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'"
  val isIdSym = Char.contains "'_!%&$#+-/:<=>?@\\~`^|*"
  fun colZero start = start = 0 orelse String.sub (body, start) = #"\n"
  val _ = ws ()

  fun finishString p = case cur () of
    #"\000" => parseError (p, !pos) "unclosed string literal"
  | #"\"" => next ()
  | #"\\" => (next (); case cur () of
      #"\n" => (next (); ws (); (case cur () of #"\\" => next () | _ => ()); finishString p)
    | _ => (next (); finishString p))
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
    if Char.isDigit c then (next (); finishInt ()) else
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

      | _ => Regular)
    end

  val lookahead = ref NONE
  val token = fn () => case !lookahead of
    NONE => token ()
  | SOME tk => (lookahead := NONE; tk)
  fun unread tk = lookahead := SOME tk

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

  fun parseSymbolStop c err = let
    val r = parseSymbol c (SOME err)
    val stop = case r of
      SOME n => n+1
    | NONE => (case token() of tk => (unread tk; #1 tk))
    in (r, stop) end

  fun parseDelimitedClose args delims (f as {elem, delim, close}) =
    case token () of tk =>
      if close tk then ({args = rev args, delims = rev delims}, SOME (#1 tk), !pos)
      else case ((unread tk; elem ()), token ()) of (e, tk) =>
        if close tk then ({args = rev (e :: args), delims = rev delims}, SOME (#1 tk), !pos)
        else if delim tk then parseDelimitedClose (e :: args) (#1 tk :: delims) f
        else (
          parseError (#1 tk, !pos) "expected close delimiter";
          unread tk; ({args = rev (e :: args), delims = rev delims}, NONE, #1 tk))

  fun parseDelimited args delims (f as {elem, delim}) =
    case (elem (), token ()) of (e, tk) =>
      if delim tk then parseDelimited (e :: args) (#1 tk :: delims) f
      else (unread tk; {args = rev (e :: args), delims = rev delims})

  fun parseTy (prec: bool): ty = let
    val lhs = case token () of
      (start, TyVarTk) => TyVar (start, ident start)
    | (start, Symbol #"(") => let
      val (elems, right, stop) = parseDelimitedClose [] [] {
        elem = fn () => parseTy false,
        delim = fn (_, Symbol #",") => true | _ => false,
        close = fn (_, Symbol #")") => true | _ => false }
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
        delim = fn (_, Symbol #",") => true | _ => false,
        close = fn (_, Symbol #"}") => true | _ => false }
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
          rhs (TyTuple (parseDelimited [lhs] [start] {
            elem = fn () => parseTy true,
            delim = fn (s, IdentTk) => ident s = "*" | _ => false }))
      | ("->", _) => if prec then (unread tk; lhs) else
          rhs (TyArrow {from = lhs, arrow = start, to = parseTy false})
      | (id, Regular) => rhs (TyCon {args = One lhs, id = (#1 tk, id)})
      | _ => (unread tk; lhs))
    | tk => (unread tk; lhs)
    in rhs lhs end
  val parseTy = fn () => parseTy false

  fun parseIdentifier () = let
    val tk = token ()
    (* In case of failure, record an error and return the empty string *)
    fun fail () = (parseError (#1 tk, !pos) "expected identifier"; unread tk; (#1 tk, ""))
    in
      case tk of
        (start, IdentTk) =>
          (case identKind start of (id, Regular) => (start, id) | _ => fail ())
      | _ => fail ()
    end

  val infixes = (* FIXME *)
    map (fn x => (x, 0, false)) ["++", "&&", "|->", "THEN", "THEN1",
      "THENL", "THEN_LT", "THENC", "ORELSE", "ORELSE_LT", "ORELSEC", "THEN_TCL",
      "ORELSE_TCL", "?>", "|>", "|>>", "||>", "||->",
      ">>", ">-", ">|", "\\\\", ">>>", ">>-", "??", ">~", ">>~", ">>~-"] @
    [("by", 8, false), ("suffices_by", 8, false), ("$", 1, true)]
  type scope = (string * int * bool) list

  fun parseExp sc (pat: bool): exp = let

    fun parseRecordLabel () = case token () of
      (start, IntTk) => (start, ident start)
    | tk => (unread tk; parseIdentifier ())

    fun parseArmList acc = case (parseKeyword "|" NONE, acc) of
      (NONE, _::_) => rev acc
    | (bar, acc) => let
      val (pats, arrow, _) = parseDelimitedClose [] [] {
        elem = fn () => parseExp sc true,
        delim = fn (s, IdentTk) => ident s = "|" | _ => false,
        close = fn (s, IdentTk) => ident s = "=>" | _ => false }
      val exp = parseExp sc false
      in parseArmList ({bar = bar, pats = pats, arrow = arrow, exp = exp} :: acc) end

    fun parseAtomic pat force = case token () of
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
        delim = fn (_, Symbol #",") => true | _ => false,
        close = fn (_, Symbol #"]") => true | _ => false }
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
        delim = fn (_, Symbol #",") => true | _ => false,
        close = fn (_, Symbol #"}") => true | _ => false }
      in Record {left = start, elems = elems, right = right, stop = stop} end
    | (start, Symbol #"#") => (case parseSymbol #"(" NONE of
        SOME startParen => let
        val res = case token () of
          (kw, IdentTk) => (case ident kw of
            "LINE" => (case parseKeyword "=" NONE of
              SOME eq_ => let
              val line = parseInt (SOME "expected a number")
              val col = Option.map
                (fn comma_ => {comma_ = comma_, col = parseInt (SOME "expected a number")})
                (parseSymbol #"," NONE)
              val (right, stop) = parseSymbolStop #")" "expected ')'"
              in HOLLinePragmaWith {
                hash_ = start, left = startParen, line_ = kw,
                eq_ = eq_, line = line, col = col, right = right, stop = stop }
              end
            | NONE => let
              val (right, stop) = parseSymbolStop #")" "expected ')'"
              in HOLLinePragma {
                hash_ = start, left = startParen, line_ = kw,
                right = right, stop = stop}
              end)
          | "FILE" => (case parseKeyword "=" NONE of
              SOME eq_ => let
              val file = parseIdent (SOME "expected an identifier")
              val (right, stop) = parseSymbolStop #")" "expected ')'"
              in HOLFilePragmaWith {
                hash_ = start, left = startParen, file_ = kw,
                eq_ = eq_, file = file, right = right, stop = stop }
              end
            | NONE => let
              val (right, stop) = parseSymbolStop #")" "expected ')'"
              in HOLFilePragma {
                hash_ = start, left = startParen, file_ = kw,
                right = right, stop = stop}
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
    | (start, IdentTk) => (case ident start of
        "let" => let
        val let_ = start
        val (sc', dec) = parseDecs false sc []
        val in_ = parseKeyword "in" (SOME "expected keyword in")
        val (exps, end_, stop) = parseDelimitedClose [] [] {
          elem = fn () => parseExp sc' false,
          delim = fn (_, Symbol #";") => true | _ => false,
          close = fn (start, IdentTk) => ident start = "end" | _ => false }
        in LetInEnd {let_ = let_, dec = dec, in_ = in_, exps = exps, end_ = end_, stop = stop} end
      | id => Ident {
        op_ = if id = "op" then SOME start else (unread (start, IdentTk); NONE),
        id = parseIdentifier () })
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
      val (toks, right) = parseQuoteBody sc start s
      val quote = {start = left, toks = toks, stop = right}
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
      unread tk; BadExp {start = #1 tk, stop = #1 tk})

    fun parseInfix pat = let

      fun peekInfix () = let
        val (start, tk) = token ()
        val r = case tk of
          IdentTk => let
          val s = ident start
          in List.find (fn x => #1 x = s) sc end
        | _ => NONE
        in unread (start, tk); (start, r) end

      fun parseApp lhs =
        case peekInfix () of
          (_, SOME _) => lhs
        | (_, NONE) => case parseAtomic pat false of
            BadExp _ => lhs
          | rhs => parseApp (App (lhs, rhs))
      val parseApp = fn () => parseApp (parseAtomic pat true)

      fun tail prec lhs =
        case peekInfix () of
          (start, SOME (opr, prec', _)) => if prec' < prec then lhs else let
          val _ = token ()
          val rhs = tail2 prec' (parseApp ())
          in tail prec (Infix {left = lhs, id = (start, opr), right = rhs}) end
        | _ => lhs
      and tail2 prec rhs =
        case peekInfix () of
          (_, SOME (_, prec', rassoc)) =>
          if prec' + (if rassoc then 1 else 0) > prec then
            tail2 prec (tail (prec + (if prec' > prec then 1 else 0)) rhs)
          else rhs
        | _ => rhs

      in tail 0 (parseApp ()) end

    fun parseTyped lhs =
      case parseKeyword ":" NONE of
        NONE => lhs
      | SOME colon => parseTyped (Typed {exp = lhs, colon = colon, ty = parseTy ()})

    fun parseLayered pat lhs = if not pat then lhs else let
      fun finish {op_, id} ty = case parseKeyword "as" NONE of
          NONE => lhs
        | SOME as_ =>
          Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = parseExp sc true}
      in
        case lhs of
          Ident id => finish id NONE
        | Typed {exp = Ident id, colon, ty} => finish id (SOME {colon = colon, ty = ty})
        | _ => lhs
      end

    fun parseExp1 pat = parseLayered pat (parseTyped (parseInfix pat))

    fun parseKwExp () =
      case token () of tk as (start, _) =>
      case case #2 tk of IdentTk => ident start | _ => "" of
        "raise" => Raise {raise_ = start, exp = parseExp sc false}
      | "if" => IfThenElse {
        if_ = start,
        exp1 = parseExp sc false,
        then_ = parseKeyword "then" (SOME "expected keyword then"),
        exp2 = parseExp sc false,
        else_ = parseKeyword "else" (SOME "expected keyword else"),
        exp3 = parseExp sc false }
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
      | _ => (unread tk; parseExp1 false)

    fun parseAndAlso () =
      case parseKwExp () of left =>
      case parseKeyword "andalso" NONE of
        SOME andalso_ => AndAlso {left = left, andalso_ = andalso_, right = parseAndAlso ()}
      | NONE => left

    fun parseOrElse () =
      case parseAndAlso () of left =>
      case parseKeyword "orelse" NONE of
        SOME orelse_ => OrElse {left = left, orelse_ = orelse_, right = parseOrElse ()}
      | NONE => left

    in
      if pat then parseExp1 true else
      case parseOrElse () of exp =>
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
        val (elems, right, stop) = parseDelimitedClose [exp] [startComma] {
          elem = fn () => parseExp sc pat,
          delim = fn (_, Symbol #",") => true | _ => false,
          close = fn (_, Symbol #")") => true | _ => false }
        in Tuple {left = startOpen, elems = elems, right = right, stop = stop} end
      | (startSemi, Symbol #";") => let
        val (elems, right, stop) = parseDelimitedClose [exp] [startSemi] {
          elem = fn () => parseExp sc pat,
          delim = fn (_, Symbol #";") => true | _ => false,
          close = fn (_, Symbol #")") => true | _ => false }
        in Sequence {left = startOpen, elems = elems, right = right, stop = stop} end
      | tk => (
        parseError (#1 tk, #1 tk) "expected closing parenthesis";
        unread tk;
        Parens {left = startOpen, exp = exp, right = NONE, stop = #1 tk}))

  and parseQuoteBody sc start s = let
    datatype qtoken = EOF | EndTk | AntiqIdent | AntiqParen | OpenBrack
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
        if cm = 0 andalso colZero (!pos) then (!pos, (next (); OpenBrack))
        else (next (); qtoken cm)
      | #"E" =>
        if colZero (!pos) andalso checkKW "End" 1 then (!pos, (nextn 3; EndTk))
        else (next (); qtoken cm)
      | #"T" =>
        if colZero (!pos) andalso checkKW "Termination" 1 then (!pos, (nextn 11; EndTk))
        else (next (); qtoken cm)
      | #"P" =>
        if colZero (!pos) andalso checkKW "Proof" 1 then (!pos, (nextn 5; EndTk))
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

    fun go acc =
      case qtoken 0 of
        (p, EOF) => (parseError (start, p) "unclosed quotation"; (rev acc, p))
      | (p, EndTk) => (
        if s = ident p then () else parseError (p, !pos) ("expected ["^s^"]");
        (rev acc, p))
      | (p, AntiqIdent) => let
        val exp = case identKind (p + 1) of
          (s, Regular) => Ident {op_ = NONE, id = (p+1, s)}
        | _ => (parseError (p+1, !pos) "expected identifier"; BadExp {start = p+1, stop = !pos})
        in go (QuoteAntiq {caret_ = p, exp = exp, stop = !pos} :: acc) end
      | (p, AntiqParen) => let
        val e = parseParen sc false (p+1)
        val stop = case e of
          Unit {right, ...} => right+1
        | Parens {stop, ...} => stop
        | Tuple {stop, ...} => stop
        | Sequence {stop, ...} => stop
        | _ => raise Unreachable
        in go (QuoteAntiq {caret_ = p, exp = e, stop = stop} :: acc) end
      | (p, OpenBrack) => let
        val _ = ws ()
        val label =
          if checkKW "/\\" 0 then
            SOME (HOLConjLabel (!pos, (nextn 2; ident (!pos - 2))))
          else if checkKW "\226\136\167" 0 then
            SOME (HOLConjLabel (!pos, (nextn 3; ident (!pos - 3))))
          else if cur () = #"~" andalso Char.isAlpha (ahead 1) then
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
            elem = parseIdentifier,
            delim = fn (_, Symbol #",") => true | _ => false,
            close = fn (_, Symbol #"]") => true | _ => false }
          in SOME {left = left, ids = ids, right = right, stop = stop} end
        val colon = parseKeyword ":" NONE
        val (right, stop) = parseSymbolStop #"]" "expected ']'"
        val _ = pos := stop
        val r = DefinitionLabel {
          left = p, label = label, args = args,
          colon = colon, right = right, stop = stop }
        in go (r :: acc) end
    in go [] end

  and parseDecs (inSig: bool) sc (acc: dec list): scope * dec list =
    case token () of
      (start, IdentTk) => (case ident start of
        "val" => let
        val pat = parseExp sc true
        val tyvars = Empty
        in
          case parseKeyword "=" NONE of
            SOME eq => let
            val exp = parseExp sc false
            val elem = ValBind {rec_ = NONE, pat = pat, eq = eq, exp = exp}
            val elems = {args = [elem], delims = []}
            in parseDecs inSig sc (DecVal {val_ = start, tyvars = tyvars, elems = elems} :: acc) end
          | NONE => let
            val colon = parseKeyword ":" (SOME "expected a colon")
            val Ident {op_ = NONE, id} = pat
            val ty = parseTy ()
            val elem = ValSpec {vid = id, colon = colon, ty = ty}
            val elems = {args = [elem], delims = []}
            in parseDecs inSig sc (DecVal {val_ = start, tyvars = tyvars, elems = elems} :: acc) end
        end
      | _ => raise Todo)
    | _ => raise Todo
  in () end

end
