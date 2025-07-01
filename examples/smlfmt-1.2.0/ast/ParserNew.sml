
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
  | HOLLinePragma of int (* #(LINE) *)
  (* | HOLLinePragmaWith of int * string *) (* #(LINE=3) this is BS *)
  | HOLFilePragma of int (* #(FILE) *)
  (* | HOLFilePragmaWith of int * string *) (* #(FILE=foo.sml) this is BS *)

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
    QuoteAntiq of exp
  | DefinitionLabel of int * string
  | QuoteComment of int * int

  withtype struct_kind = {colon: int * constraint, sigexp: sigexp}

  and arm = {bar: int option, pat: exp, arrow: int, exp: exp}

  and fvalarm = {
    bar: int option, fname_args: fname_args,
    ty: {colon: int, ty: ty} option, eq: int, exp: exp}

  and qbody = {start: int, toks: qdecl list, stop: int}

end


structure ParserNew = struct
open AstNew

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

  fun finishString () = case cur () of
    #"\000" => ()
  | #"\"" => next ()
  | #"\\" => (next (); case cur () of
      #"\n" => (next (); ws (); (case cur () of #"\\" => next () | _ => ()); finishString ())
    | _ => (next (); finishString ()))
  | _ => (next (); finishString ())

  fun finishComment () = case cur () of
    #"\000" => ()
  | #"*" => (next (); if cur () = #")" then next () else finishComment ())
  | #"(" => (next (); if cur () = #"*" then (next (); finishComment ()) else (); finishComment ())
  | _ => (next (); finishComment ())

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
  | QuoteTk
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
  | #"\"" => (!pos, (next (); finishString (); StringTk))
  | #"~" => (!pos, (next (); case cur () of
      #"0" => (next (); finishIntAfterZero ())
    | c =>
      if Char.isDigit c then (next (); finishInt ()) else
      (takeWhile isIdSym; finishId (); IdentTk)))
  | #"0" => (!pos, (next (); finishIntAfterZero ()))
  | #"'" => (!pos, (next (); takeWhile isIdRest; TyVarTk))
  | #"." => (!pos, (next (); takeWhile (fn c => c = #"."); IdentTk))
  | #"#" => (!pos, (next (); case cur () of
      #"\"" => (next (); finishString (); CharTk)
    | _ => (takeWhile isIdSym; finishId (); IdentTk)))
  | #"(" => let
    val start = !pos
    val _ = next ()
    in if cur () = #"*" then (next (); finishComment (); token ()) else (start, Symbol #"(") end
  | #"`" => (!pos, (next (); case cur () of
      #"`" => (next (); QuoteTk)
    | _ => QuoteTk))
  | #"\226" => (!pos, (case (ahead 1, ahead 2) of
      (#"\128", #"\152") => (nextn 3; QuoteTk)
    | (#"\128", #"\153") => (nextn 3; QuoteTk)
    | (#"\128", #"\156") => (nextn 3; QuoteTk)
    | (#"\128", #"\157") => (nextn 3; QuoteTk)
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

  fun parseExp (pat: bool): exp = let
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

    fun parseRecordLabel () = case token () of
      (start, IntTk) => (start, ident start)
    | tk => (unread tk; parseIdentifier ())

    fun parseArmList () = raise Todo

    fun parseAtomic pat force = case token () of
      (start, Symbol #"_") => Wild start
    | (start, IntTk) => IntegerConstant (start, ident start)
    | (start, WordTk) => WordConstant (start, ident start)
    | (start, StringTk) => StringConstant (start, ident start)
    | (start, CharTk) => CharConstant (start, ident start)
    | (start, RealTk) => RealConstant (start, ident start)
    | (startOpen, Symbol #"(") => (case token () of
        (startClose, Symbol #")") => Unit {left = startOpen, right = startClose}
      | tk =>
        case (unread tk; parseExp pat) of exp =>
        case token () of
          (startClose, Symbol #")") =>
          Parens {left = startOpen, exp = exp, right = SOME startClose, stop = startClose+1}
        | (startComma, Symbol #",") => let
          val (elems, right, stop) = parseDelimitedClose [exp] [startComma] {
            elem = fn () => parseExp pat,
            delim = fn (_, Symbol #",") => true | _ => false,
            close = fn (_, Symbol #")") => true | _ => false }
          in Tuple {left = startOpen, elems = elems, right = right, stop = stop} end
        | (startSemi, Symbol #";") => let
          val (elems, right, stop) = parseDelimitedClose [exp] [startSemi] {
            elem = fn () => parseExp pat,
            delim = fn (_, Symbol #";") => true | _ => false,
            close = fn (_, Symbol #")") => true | _ => false }
          in Sequence {left = startOpen, elems = elems, right = right, stop = stop} end
        | tk => (
          parseError (#1 tk, #1 tk) "expected closing parenthesis";
          unread tk;
          Parens {left = startOpen, exp = exp, right = NONE, stop = #1 tk}))
    | (start, Symbol #"[") => let
      val (elems, right, stop) = parseDelimitedClose [] [] {
        elem = fn () => parseExp pat,
        delim = fn (_, Symbol #",") => true | _ => false,
        close = fn (_, Symbol #"]") => true | _ => false }
      in List {left = start, elems = elems, right = right, stop = stop} end
    | (start, Symbol #"{") => let
      val (elems, right, stop) = parseDelimitedClose [] [] {
        elem = fn () =>
        case parseRecordLabel () of
          (start, "...") => DotDotDot start
        | id => case parseKeyword "=" NONE of
            SOME eq => LabEq {lab = id, eq = eq, exp = parseExp pat}
          | NONE => LabAs {
            id = id,
            ty = Option.map (fn c => {colon = c, ty = parseTy ()}) (parseKeyword ":" NONE),
            aspat = Option.map (fn c => {as_ = c, exp = parseExp pat}) (parseKeyword "as" NONE) },
        delim = fn (_, Symbol #",") => true | _ => false,
        close = fn (_, Symbol #"}") => true | _ => false }
      in Record {left = start, elems = elems, right = right, stop = stop} end
    | (start, Symbol #"#") => Select {hash = start, label = parseRecordLabel ()}
    | (start, IdentTk) => (case ident start of
        "let" => let
        val let_ = start
        val dec = parseDec false []
        val in_ = parseKeyword "in" (SOME "expected keyword in")
        val (exps, end_, stop) = parseDelimitedClose [] [] {
          elem = fn () => parseExp false,
          delim = fn (_, Symbol #";") => true | _ => false,
          close = fn (start, IdentTk) => ident start = "end" | _ => false }
        in LetInEnd {let_ = let_, dec = dec, in_ = in_, exps = exps, end_ = end_, stop = stop} end
      | id => Ident {
        op_ = if id = "op" then SOME start else (unread (start, IdentTk); NONE),
        id = parseIdentifier () })
    | tk => (
      if force then parseError (#1 tk, #1 tk) "expected an expression" else ();
      unread tk; BadExp {start = #1 tk, stop = #1 tk})

    fun parseInfix pat = let

      val infixes = (* FIXME *)
        map (fn x => (x, 0, false)) ["++", "&&", "|->", "THEN", "THEN1",
          "THENL", "THEN_LT", "THENC", "ORELSE", "ORELSE_LT", "ORELSEC", "THEN_TCL",
          "ORELSE_TCL", "?>", "|>", "|>>", "||>", "||->",
          ">>", ">-", ">|", "\\\\", ">>>", ">>-", "??", ">~", ">>~", ">>~-"] @
        [("by", 8, false), ("suffices_by", 8, false), ("$", 1, true)]

      fun peekInfix () = let
        val (start, tk) = token ()
        val r = case tk of
          IdentTk => let
          val s = ident start
          in List.find (fn x => #1 x = s) infixes end
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
          Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = parseExp true}
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
        "raise" => Raise {raise_ = start, exp = parseExp false}
      | "if" => IfThenElse {
        if_ = start,
        exp1 = parseExp false,
        then_ = parseKeyword "then" (SOME "expected keyword then"),
        exp2 = parseExp false,
        else_ = parseKeyword "else" (SOME "expected keyword else"),
        exp3 = parseExp false }
      | "while" => While {
        while_ = start,
        exp1 = parseExp false,
        do_ = parseKeyword "do" (SOME "expected keyword do"),
        exp2 = parseExp false }
      | "case" => Case {
        case_ = start,
        exp = parseExp false,
        of_ = parseKeyword "of" (SOME "expected keyword of"),
        elems = parseArmList () }
      | "fn" => Fn {fn_ = start, elems = parseArmList ()}
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
        SOME handle_ => Handle {exp = exp, handle_ = handle_, elems = parseArmList ()}
      | NONE => exp
    end

  and parseDec (inSig: bool) (acc: dec list): dec list =
    case token () of
      (start, IdentTk) => (case ident start of
        "val" => let
        val pat = parseExp true
        val tyvars = Empty
        in
          case parseKeyword "=" NONE of
            SOME eq => let
            val exp = parseExp false
            val elem = ValBind {rec_ = NONE, pat = pat, eq = eq, exp = exp}
            val elems = {args = [elem], delims = []}
            in parseDec inSig (DecVal {val_ = start, tyvars = tyvars, elems = elems} :: acc) end
          | NONE => let
            val colon = parseKeyword ":" (SOME "expected a colon")
            val Ident {op_ = NONE, id} = pat
            val ty = parseTy ()
            val elem = ValSpec {vid = id, colon = colon, ty = ty}
            val elems = {args = [elem], delims = []}
            in parseDec inSig (DecVal {val_ = start, tyvars = tyvars, elems = elems} :: acc) end
        end
      | _ => raise Todo)
    | _ => raise Todo
  in () end

end
