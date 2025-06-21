
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
  | TyError of {start: int, stop: int} (** ( ty ) *)

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
  | Tuple of {left: int, elems: exp delimited, right: int} (** ( exp, ..., exp ) *)
  | Record of {left: int, elems: row delimited, right: int}
    (** { lab = exp, ..., lab = exp } *)
  | Parens of {left: int, exp: exp, right: int} (** ( exp ) *)
  | Con of {op_: int option, id: ident, atpat: exp} (** [op] longvid atpat *)
  | Infix of {left: exp, id: ident, right: exp} (** exp vid exp *)
  | Typed of {exp: exp, colon: int, ty: ty} (** exp : ty *)
  | Layered of {op_: int option, id: ident, ty: {colon: int, ty: ty} option, as_: int, pat: exp}
    (** [op] vid [:ty] as pat *)
  | Or of exp delimited (** SuccessorML "or patterns": pat | pat | ... | pat *)
  | Select of {hash: int, label: ident} (** # label *)
  | Sequence of {left: int, elems: exp delimited, right: int} (** (exp; ...; exp) *) (* TODO: this is stupid *)
  | LetInEnd of {let_: int, dec: dec list, in_: int, exps: exp delimited, end_: int}
    (** let dec in exp [; exp ...] end *)
  | App of exp * exp (** exp exp *)
  | Andalso of {left: exp, andalso_: int, right: exp} (** exp andalso exp *)
  | Orelse of {left: exp, orelse_: int, right: exp} (** exp orelse exp *)
  | Handle of {exp: exp, handle_: int, elems: arm list}
    (** exp handle pat => exp [| pat => exp ...] *)
  | Raise of {raise_: int, exp: exp} (** raise exp *)
  | IfThenElse of {if_: int, exp1: exp, then_: int, exp2: exp, else_: int, exp3: exp}
    (** if exp then exp else exp *)
  | While of {while_: int, exp1: exp, do_: int, exp2: exp} (** while exp do exp *)
  | Case of {case_: int, exp: exp, of_: int, elems: arm list}
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
      #"x" => if Char.isHexDigit (ahead 2) then (nextn 3; takeWhile Char.isHexDigit; WordTk) else IntTk
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

  fun parseSymbol s err = let
    val tk = token ()
    val r = case tk of (start, Symbol c) => if c = s then SOME start else NONE | _ => NONE
    val _ = case r of SOME _ => () | NONE => (
      case err of NONE => () | SOME e => parseError (#1 tk, !pos) e;
      unread tk)
    in r end

  fun parseKeyword s err = let
    val tk = token ()
    val r = case tk of (start, IdentTk) => if ident start = s then SOME start else NONE | _ => NONE
    val _ = case r of SOME _ => () | NONE => (
      case err of NONE => () | SOME e => parseError (#1 tk, !pos) e;
      unread tk)
    in r end

  fun parseDelimitedClose {elem, delim, close} = let
    fun go args delims = case token () of tk =>
      if close tk then ({args = rev args, delims = rev delims}, SOME (#1 tk), !pos)
      else case ((unread tk; elem ()), token ()) of (e, tk) =>
        if close tk then ({args = rev (e :: args), delims = rev delims}, SOME (#1 tk), !pos)
        else if delim tk then go (e :: args) (#1 tk :: delims)
        else (
          parseError (#1 tk, !pos) "expected close delimiter";
          unread tk; ({args = rev (e :: args), delims = rev delims}, NONE, #1 tk))
    in go [] [] end

  fun parseDelimited (f as {elem, delim}) args delims =
    case (elem (), token ()) of (e, tk) =>
      if delim tk then parseDelimited f (e :: args) (#1 tk :: delims)
      else (unread tk; {args = rev (e :: args), delims = rev delims})

  fun parseTy (prec: bool): ty = let
    val lhs = case token () of
      (start, TyVarTk) => TyVar (start, ident start)
    | (start, Symbol #"(") => let
      val (elems, right, stop) = parseDelimitedClose {
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
            unread tk; TyError {start = start, stop = stop})
      end
    | (start, Symbol #"{") => let
      val (elems, right, stop) = parseDelimitedClose {
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
        unread tk; TyError {start = #1 tk, stop = #1 tk})
    fun rhs lhs = case token () of
      tk as (start, IdentTk) => (case identKind start of
        ("*", _) => if prec then (unread tk; lhs) else
          rhs (TyTuple (parseDelimited {
            elem = fn () => parseTy true,
            delim = fn (s, IdentTk) => ident s = "*" | _ => false } [lhs] [start]))
      | ("->", _) => if prec then (unread tk; lhs) else
          rhs (TyArrow {from = lhs, arrow = start, to = parseTy false})
      | (id, Regular) => rhs (TyCon {args = One lhs, id = (#1 tk, id)})
      | _ => (unread tk; lhs))
    | tk => (unread tk; lhs)
    in rhs lhs end
  val parseTy = fn () => parseTy false

  fun parseExp (pat: bool): exp =
    case token () of
      (start, Symbol #"_") => Wild start
    | (start, IntTk) => IntegerConstant (start, ident start)
    | (start, WordTk) => WordConstant (start, ident start)
    | (start, StringTk) => StringConstant (start, ident start)
    | (start, CharTk) => CharConstant (start, ident start)
    | (start, RealTk) => RealConstant (start, ident start)
    | (start, Symbol #"(") => (case token () of
        (startClose, Symbol #")") => Unit {left = start, right = startClose}
      | _ => raise Todo)
    | (start, Symbol #"[") => let
      val (elems, right, stop) = parseDelimitedClose {
        elem = fn () => parseExp pat,
        delim = fn (_, Symbol #",") => true | _ => false,
        close = fn (_, Symbol #"]") => true | _ => false
      }
      in List {left = start, elems = elems, right = right, stop = stop} end
    | _ => raise Todo

  fun parseDec (inSig: bool) (acc: dec list): dec list =
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
