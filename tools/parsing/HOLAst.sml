structure HOLAst :> HOLAst = struct

(* Defines an AST for Standard ML and the HOL-specific extensions such as
   Definition, Theorem, Inductive, and so on.

   The AST is capable of representing ill-formed files. For example, Lists
   contain a record that holds `right: int option` and `stop: int`. If the
   closing bracket is missing, `right` will be `None`, and `stop` will indicate
   where the parser guesses the list should have ended.

   The basic shape of the AST is based on Sam Westrick's excellent smlfmt, which
   is released under the MIT license. *)


(* (start, content) *)
type ident = int * string

type fileline = {file: string, line: int, col: int}

exception Unreachable

type 'exp delimited = {args: 'exp list, delims: int option list, stop: int}

datatype 'a seq =
  Empty
| One of 'a
| Many of {left: int, elems: 'a delimited, right: int option, stop: int}

datatype ty =
  TyVar of ident
| TyRecord of (** { lab : ty, ..., lab : ty } *)
    { left: int,
      elems: {start: int, lab: ident option, colon: int option, ty: ty} delimited,
      right: int option, stop: int }
| TyTuple of ty delimited (** ty * ... * ty *)
| TyCon of {args: ty seq, id: ident} (** tyseq longtycon *)
| TyArrow of {from: ty, arrow: int, to: ty} (** ty -> ty *)
| TyParens of {left: int, ty: ty, right: int option, stop: int} (** ( ty ) *)
| BadTy of {start: int, stop: int} (** ( ty ) *)

(** tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
type tybind = {tyvars: ident seq, tycon: ident, bind: {eq: int, ty: ty} option}

(** [op] vid [of ty] [| [op] vid [of ty] ...] *)
type conbind = {bar: int option, op_: int option, id: ident, arg: {of_: int, ty: ty} option}

datatype datval =
  DatvalElems of conbind list
  (** datatype tycon = conbind | conbind ... *)
| DatvalDatatype of {datatype_: int, id: ident}
  (** datatype tycon = datatype x *)

(** tyvarseq tycon = conbind [and tyvarseq tycon = conbind ...] *)
type datbind = {tyvars: ident seq, tycon: ident, eq: int option, rhs: datval}

datatype exbind =
  ExnNew of {op_: int option, id: ident, arg: {of_: int, ty: ty} option}
| ExnReplicate of {op_: int option, id: ident, eq: int, tgt: ident}

datatype constraint = Colon | ColonGt

datatype defn_label_id =
  HOLConjLabel of int * string
| HOLLabel of {tilde_: int option, id: int * string}

type 'a attrs = {
  left: int,
  attrs: 'a delimited,
  right: int option, stop: int} option
type kvals = {key: ident, bind: {eq_: int, vals: ident list} option}

datatype maybe_quoted =
  UnquotedId of ident
| QuotedId of int * string

type header_elem = {id: ident, attrs: kvals attrs}

datatype header =
  HOLAncestors of {ancestors_: int, attrs: kvals attrs, elems: header_elem list}
| HOLLibs of {libs_: int, attrs: kvals attrs, elems: header_elem list}

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
| Handle of {exp: exp, handle_: int, elems: arm list, stop: int}
  (** exp handle pat => exp [| pat => exp ...] *)
| Raise of {raise_: int, exp: exp} (** raise exp *)
| IfThenElse of {
    if_: int, exp1: exp, then_: int option, exp2: exp, else_: {else_: int, exp3: exp} option}
  (** if exp then exp else exp *)
| While of {while_: int, exp1: exp, do_: int option, exp2: exp} (** while exp do exp *)
| Case of {case_: int, exp: exp, of_: int option, elems: arm list, stop: int}
  (** case exp of pat => exp [| pat => exp ...] *)
| Fn of {fn_: int, elems: arm list, stop: int} (** fn pat => exp [| pat => exp ...] *)

| HOLFullQuote of {
    head: int * string, type_q: int option,
    quote: qdecl list, end_tok: (int * string) option, stop: int}
| HOLQuote of {head: int * string, quote: qdecl list, end_tok: (int * string) option, stop: int}
| HOLLinePragma of {
    hash_: int, left: int, line_: int, right: int option, stop: int} (* #(LINE) *)
| HOLLinePragmaWith of {
    hash_: int, left: int, line_: int, eq_: int,
    line: int * string option, col: {comma_: int, col: int * string option} option,
    right: int option, stop: int} (* #(LINE=3) this is BS *)
| HOLFilePragma of {hash_: int, left: int, file_: int, right: int option, stop: int} (* #(FILE) *)
| HOLFilePragmaWith of {
    hash_: int, left: int, file_: int, eq_: int,
    file: int * string option, right: int option, stop: int} (* #(FILE=foo.sml) this is BS *)

| ExpExpansion of {orig: exp, result: exp}
| ExpEmpty of int
| ExpBad of {start: int, stop: int}

and row =
  DotDotDot of int (** can only appear at end of record pattern *)
| LabEq of {lab: ident, eq: int, exp: exp}
| LabAs of {id: ident, ty: {colon: int, ty: ty} option, aspat: {as_: int, exp: exp} option}
| LabExpansion of {orig: row, result: row}

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
    datatype_: int, datbind: datbind delimited,
    withtype_: {withtype_: int, tybind: tybind delimited} option }
  (** datatype datbind [withtype typbind] *)
| DecAbstype of {
    abstype_: int, datbind: datbind delimited,
    withtype_: {withtype_: int, tybind: tybind delimited} option,
    with_: int option, dec: dec list, end_: int option, stop: int}
  (** abstype datbind [withtype typbind] with dec end *)
| DecException of {exception_: int, elems: exbind delimited}
  (** exception exbind *)
| DecLocal of {
    local_: int, dec1: dec list, in_: int option,
    dec2: dec list, end_: int option, stop: int}
  (** local dec in dec end *)
| DecOpen of {open_: int, elems: ident list}
  (** open longstrid [longstrid ...] *)
| DecInfix of {infix_: int, prec: (int * string) option, elems: ident list}
  (** infix [d] vid [vid ...] *)
| DecInfixr of {infixr_: int, prec: (int * string) option, elems: ident list}
  (** infixr [d] vid [vid ...] *)
| DecNonfix of {nonfix_: int, elems: ident list} (** nonfix vid [vid ...] *)
| DecStructure of {
    structure_: int, elems: {
      id: ident, constraint: struct_kind option,
      bind: {eq: int, strexp: strexp} option} delimited}
  (** structure strid : sigexp = strexp [and strid : sigep = strexp ...] *)
| DecSignature of {
    signature_: int,
    elems: {id: ident, bind: {eq: int, sigexp: sigexp} option} delimited}
  (** signature sigid = sigexp [and ...] *)
| DecInclude of {include_: int, sigexps: sigexp list}
  (** include sigid ... sigid *)
| Sharing of {sharing_: int, type_: int option, elems: ident delimited}
  (** sharing [type] longstrid = ... = longstrid *)
| DecFunctor of {
    functor_: int, elems: {
      id: ident, lparen: int option, funarg: funarg, rparen: int option,
      constraint: struct_kind option,
      bind: {eq: int, strexp: strexp} option} delimited}
  (** functor id(funarg) [:> sigexp] = strexp [and ...] *)
| DecExp of exp (** exp (only at top level) *)

| HOLTheory of {theory_: int, id: ident, attrs: kvals attrs, elems: header list}
  (** Theory foo[attrs] [elems ...] *)
| HOLTheoryEnd of {theory_: int, stop: int, noSigDocs: bool}
  (** phantom EndTheory at EOF *)
| HOLDefinition of {
    definition_: int, id: ident, attrs: kvals attrs, colon: int option,
    quote: qdecl list, termination: {termination_: int, tac: exp} option,
    end_: int option, stop: int}
  (** Definition foo[attrs]: ... [Termination tac] End *)
| HOLDatatype of {
    datatype_: int, colon: int option, quote: qdecl list, end_: int option, stop: int}
  (** Datatype: ... End *)
| HOLQuoteDecl of {
    quote_: int, id: ident, bind: {eq: int, exp: exp} option, colon: int option,
    quote: qdecl list, end_: int option, stop: int}
  (** Quote id [= foo]: ... End *)
| HOLInductiveDecl of {
    co: bool, inductive_: int, id: ident, colon: int option,
    quote: qdecl list, end_: int option, stop: int}
  (** [Co]Inductive id: ... End *)
| HOLType of {
    overload: bool, type_: int, id: maybe_quoted, attrs: ident attrs,
    bind: {eq: int, exp: exp} option} (** Type id[attrs] = exp *)
| HOLSimpleThm of {
    triv: bool, theorem_: int, id: ident, attrs: kvals attrs,
    bind: {eq: int, exp: exp} option} (** Theorem id[attrs] = exp *)
| HOLTheoremDecl of {
    triv: bool, theorem_: int, id: ident, attrs: kvals attrs, colon: int,
    quote: qdecl list, proof_: {proof_: int, attrs: kvals attrs} option,
    tac: exp, qed_: int option, stop: int}
  (** Theorem foo[attrs]: ... [Proof[attrs] tac] QED *)
| HOLResume of {
    resume_: int, id: ident, attrs: kvals attrs, colon: int option, tac: exp,
    qed_: int option, stop: int}
  (** Resume to_suspend[rtp_q,smlname=qsubgoal]: ... QED *)
| HOLFinalise of {finalise_: int, id: ident, attrs: kvals attrs, stop: int}
  (** Finalise to_suspend[simp] *)

| DecBad of {start: int, stop: int}
| DecExpansion of {orig: dec, result: dec list}

and funarg =
  ArgIdent of {strid: ident, ty: {colon: int, sigexp: sigexp} option}
| ArgSpec of dec list

and sigexp =
  SigIdent of ident
| Spec of {sig_: int, spec: dec list, end_: int option, stop: int}
  (** sig spec end *)
| WhereType of {
  sigexp: sigexp, where_: int,
  elems: {type_: int option, tybind: tybind} delimited}
  (** sigexp where type tyvarseq tycon = ty [and type ...] *)

and strexp =
  StrIdent of ident
| StrStruct of {struct_: int, strdec: dec list, end_: int option, stop: int}
| StrConstraint of {strexp: strexp, kind: struct_kind}
| FunAppExp of {funid: ident, lparen: int, strexp: strexp, rparen: int option, stop: int}
| FunAppDec of {funid: ident, lparen: int, strdec: dec list, rparen: int option, stop: int}
| StrLetInEnd of {
    let_: int, strdec: dec list, in_: int option, strexp: strexp, end_: int option, stop: int}

and qdecl =
  QuoteLiteral of int * string
| QuoteAntiq of {caret_: int, exp: exp}
| DefinitionLabel of {left: int, label: defn_label_id option, attrs: ident attrs,
    colon: int option, right: int option, stop: int}
  (** [id[x,y,z]:] *)

withtype struct_kind = {colon: int * constraint, sigexp: sigexp}

and valbind = {rec_: int option, pat: exp, eq: {eq: int, exp: exp} option}

and arm = {bar: int option, pat: exp, arrow: int option, exp: exp}

and fvalarm = {bar: int option, pat: exp, eq: int option, exp: exp}

fun mkIdent s = Ident {op_ = NONE, id = s}

local
  fun toEnd s p = case String.sub (s, p) of
    #"\\" => p+1
  | c => if Char.isSpace c then toEnd s (p+1) else raise Unreachable

  fun parseDec s p n res =
    if n = 0 then if res > 255 then NONE else SOME (chr res) else
    case String.sub (s, p) handle Subscript => #"\000" of c =>
    if #"0" <= c andalso c <= #"9" then
      parseDec s (p+1) (n-1) (res * 10 + ord c - ord #"0")
    else NONE
in
fun decodeStr parseError s start stop = let
  fun push start p acc =
    if start = p then acc else String.substring (s, start, p - start) :: acc
  fun loop start p acc =
    if p = stop then push start p acc else
    case String.sub (s, p) of
      #"\\" => (
      case String.sub (s, p+1) of
        #"a" => loop (p+2) (p+2) ("\a" :: push start p acc)
      | #"b" => loop (p+2) (p+2) ("\b" :: push start p acc)
      | #"t" => loop (p+2) (p+2) ("\t" :: push start p acc)
      | #"n" => loop (p+2) (p+2) ("\n" :: push start p acc)
      | #"v" => loop (p+2) (p+2) ("\v" :: push start p acc)
      | #"f" => loop (p+2) (p+2) ("\f" :: push start p acc)
      | #"r" => loop (p+2) (p+2) ("\r" :: push start p acc)
      | #"\\" => loop (p+2) (p+2) ("\\" :: push start p acc)
      | #"\"" => loop (p+2) (p+2) ("\"" :: push start p acc)
      | #"^" => (
        case ord (String.sub (s, p+2)) handle Subscript => 0 of c =>
        if 64 <= c andalso c <= 95 then
          loop (p+3) (p+3) (String.str (chr (c - 64)) :: push start p acc)
        else loop start (p+2) acc)
      | #"u" => (parseError (p, p + 2) "unicode escapes are not supported"; loop start (p+2) acc)
      | c =>
        if Char.isSpace c then
          case push start p acc of acc =>
          case toEnd s (p+2) of q => loop q q acc
        else if #"0" <= c andalso c <= #"2" then
          case parseDec s (p+1) 3 0 of
            NONE => loop start (p+2) acc
          | SOME c => loop (p+4) (p+4) (String.str c :: push start p acc)
        else loop start (p+2) acc)
    | _ => loop start (p+1) acc
  in String.concat (rev (loop start start [])) end
end

fun encodeStr ss bef aft = let
  val (s, start, len) = Substring.base ss
  val stop = start + len
  fun push start p acc =
    if start = p then acc else String.substring (s, start, p - start) :: acc
  fun loop start p acc =
    if p = stop then push start p acc else
      case String.sub (s, p) of c =>
      if chr 32 <= c andalso c <= chr 126 then
        case c of
          #"\\" => loop (p+1) (p+1) ("\\\\" :: push start p acc)
        | #"\"" => loop (p+1) (p+1) ("\\\"" :: push start p acc)
        | _ => loop start (p+1) acc
      else case c of
        #"\a" => loop (p+1) (p+1) ("\\a" :: push start p acc)
      | #"\b" => loop (p+1) (p+1) ("\\b" :: push start p acc)
      | #"\t" => loop (p+1) (p+1) ("\\t" :: push start p acc)
      | #"\n" => loop (p+1) (p+1) ("\\n" :: push start p acc)
      | #"\v" => loop (p+1) (p+1) ("\\v" :: push start p acc)
      | #"\f" => loop (p+1) (p+1) ("\\f" :: push start p acc)
      | #"\r" => loop (p+1) (p+1) ("\\r" :: push start p acc)
      | #"\\" => loop (p+1) (p+1) ("\\\\" :: push start p acc)
      | #"\"" => loop (p+1) (p+1) ("\\\"" :: push start p acc)
      | c => let
        val n = ord c
        val a = chr (n div 100 + ord #"0")
        val b = chr ((n div 10) mod 10 + ord #"0")
        val c = chr (n mod 10 + ord #"0")
        in loop (p+1) (p+1) (implode [#"\\", a, b, c] :: push start p acc) end
  in String.concat (rev (aft :: loop start start [bef])) end

fun mkString (p, s) = StringConstant (p, encodeStr (Substring.full s) "\"" "\"")
fun mkInt (p, s) = IntegerConstant (p, Int.toString s)

fun mkList (p, ls) =
  List {left = p, elems = {args = ls, delims = [], stop = p}, right = NONE, stop = p}
fun mkTuple (p, ls) =
  Tuple {left = p, elems = {args = ls, delims = [], stop = p}, right = NONE, stop = p}

fun mkApp f args = foldl (fn (arg, acc) => App (acc, arg)) f args

(* fun seqStart _ Empty = NONE
  | seqStart f (One p) = SOME (f p)
  | seqStart _ (Many {left, ...}) = SOME left *)

fun seqStop _ Empty = NONE
  | seqStop f (One p) = SOME (f p)
  | seqStop _ (Many {stop, ...}) = SOME stop

fun idStop (p, s) = p + size s
fun idSpan (p, s) = (p, p + size s)

fun tyStart (TyVar (p, _)) = p
  | tyStart (TyRecord {left, ...}) = left
  | tyStart (TyTuple {args = a::_, ...}) = tyStart a
  | tyStart (TyTuple {args = [], stop, ...}) = stop
  | tyStart (TyCon {args, id}) = (case seqStop tyStart args of SOME p => p | NONE => #1 id)
  | tyStart (TyArrow {from, ...}) = tyStart from
  | tyStart (TyParens {left, ...}) = left
  | tyStart (BadTy {start, ...}) = start

fun tyStop (TyVar id) = idStop id
  | tyStop (TyRecord {stop, ...}) = stop
  | tyStop (TyTuple {stop, ...}) = stop
  | tyStop (TyCon {id, ...}) = idStop id
  | tyStop (TyArrow {to, ...}) = tyStop to
  | tyStop (TyParens {stop, ...}) = stop
  | tyStop (BadTy {stop, ...}) = stop

fun tySpan ty = (tyStart ty, tyStop ty)

fun expStart (Wild p) = p
  | expStart (IntegerConstant (p, _)) = p
  | expStart (WordConstant (p, _)) = p
  | expStart (StringConstant (p, _)) = p
  | expStart (CharConstant (p, _)) = p
  | expStart (RealConstant (p, _)) = p
  | expStart (Unit {left, ...}) = left
  | expStart (Ident {op_ = SOME p, ...}) = p
  | expStart (Ident {op_ = NONE, id = (p, _)}) = p
  | expStart (List {left, ...}) = left
  | expStart (Tuple {left, ...}) = left
  | expStart (Record {left, ...}) = left
  | expStart (Parens {left, ...}) = left
  | expStart (Infix {left, ...}) = expStart left
  | expStart (Typed {exp, ...}) = expStart exp
  | expStart (Layered {op_ = SOME p, ...}) = p
  | expStart (Layered {op_ = NONE, id = (p, _), ...}) = p
  | expStart (Or {args, ...}) = expStart (hd args)
  | expStart (Select {hash, ...}) = hash
  | expStart (Sequence {left, ...}) = left
  | expStart (LetInEnd {let_, ...}) = let_
  | expStart (App (e, _)) = expStart e
  | expStart (AndAlso {left, ...}) = expStart left
  | expStart (OrElse {left, ...}) = expStart left
  | expStart (Handle {exp, ...}) = expStart exp
  | expStart (Raise {raise_, ...}) = raise_
  | expStart (IfThenElse {if_, ...}) = if_
  | expStart (While {while_, ...}) = while_
  | expStart (Case {case_, ...}) = case_
  | expStart (Fn {fn_, ...}) = fn_
  | expStart (HOLFullQuote {head = (p, _), ...}) = p
  | expStart (HOLQuote {head = (p, _), ...}) = p
  | expStart (HOLLinePragma {hash_, ...}) = hash_
  | expStart (HOLLinePragmaWith {hash_, ...}) = hash_
  | expStart (HOLFilePragma {hash_, ...}) = hash_
  | expStart (HOLFilePragmaWith {hash_, ...}) = hash_
  | expStart (ExpEmpty p) = p
  | expStart (ExpBad {start, ...}) = start
  | expStart (ExpExpansion {orig, ...}) = expStart orig

fun expStop (Wild p) = p + 1
  | expStop (IntegerConstant id) = idStop id
  | expStop (WordConstant id) = idStop id
  | expStop (StringConstant id) = idStop id
  | expStop (CharConstant id) = idStop id
  | expStop (RealConstant id) = idStop id
  | expStop (Unit {right, ...}) = right + 1
  | expStop (Ident {id, ...}) = idStop id
  | expStop (List {stop, ...}) = stop
  | expStop (Tuple {stop, ...}) = stop
  | expStop (Record {stop, ...}) = stop
  | expStop (Parens {stop, ...}) = stop
  | expStop (Infix {right, ...}) = expStop right
  | expStop (Typed {ty, ...}) = tyStop ty
  | expStop (Layered {pat, ...}) = expStop pat
  | expStop (Or {stop, ...}) = stop
  | expStop (Select {label, ...}) = idStop label
  | expStop (Sequence {stop, ...}) = stop
  | expStop (LetInEnd {stop, ...}) = stop
  | expStop (App (_, e)) = expStop e
  | expStop (AndAlso {right, ...}) = expStop right
  | expStop (OrElse {right, ...}) = expStop right
  | expStop (Handle {stop, ...}) = stop
  | expStop (Raise {exp, ...}) = expStop exp
  | expStop (IfThenElse {else_ = SOME {exp3, ...}, ...}) = expStop exp3
  | expStop (IfThenElse {else_ = NONE, exp2, ...}) = expStop exp2
  | expStop (While {exp2, ...}) = expStop exp2
  | expStop (Case {stop, ...}) = stop
  | expStop (Fn {stop, ...}) = stop
  | expStop (HOLFullQuote {stop, ...}) = stop
  | expStop (HOLQuote {stop, ...}) = stop
  | expStop (HOLLinePragma {stop, ...}) = stop
  | expStop (HOLLinePragmaWith {stop, ...}) = stop
  | expStop (HOLFilePragma {stop, ...}) = stop
  | expStop (HOLFilePragmaWith {stop, ...}) = stop
  | expStop (ExpEmpty p) = p
  | expStop (ExpBad {stop, ...}) = stop
  | expStop (ExpExpansion {orig, ...}) = expStop orig

fun expSpan e = (expStart e, expStop e)

fun exbindStop (ExnNew {arg = SOME {ty, ...}, ...}) = tyStop ty
  | exbindStop (ExnNew {arg = NONE, id, ...}) = idStop id
  | exbindStop (ExnReplicate {tgt, ...}) = idStop tgt

fun sigexpStart (SigIdent (p, _)) = p
  | sigexpStart (Spec {sig_, ...}) = sig_
  | sigexpStart (WhereType {sigexp, ...}) = sigexpStart sigexp

fun sigexpStop (SigIdent id) = idStop id
  | sigexpStop (Spec {stop, ...}) = stop
  | sigexpStop (WhereType {elems = {stop, ...}, ...}) = stop

fun sigexpSpan s = (sigexpStart s, sigexpStop s)

fun strexpSpan (StrIdent id) = idSpan id
  | strexpSpan (StrStruct {struct_, stop, ...}) = (struct_, stop)
  | strexpSpan (StrConstraint {strexp, kind = {sigexp, ...}, ...}) =
    (#1 (strexpSpan strexp), sigexpStop sigexp)
  | strexpSpan (FunAppExp {funid = (p, _), stop, ...}) = (p, stop)
  | strexpSpan (FunAppDec {funid = (p, _), stop, ...}) = (p, stop)
  | strexpSpan (StrLetInEnd {let_, stop, ...}) = (let_, stop)

fun headerElemStop {id, attrs = NONE} = idStop id
  | headerElemStop {attrs = SOME {stop, ...}, ...} = stop

fun headerStop (HOLAncestors {ancestors_, elems, ...}) =
    (headerElemStop (List.last elems) handle List.Empty => ancestors_ + 9)
  | headerStop (HOLLibs {libs_, elems, ...}) =
    (headerElemStop (List.last elems) handle List.Empty => libs_ + 4)

fun maybeQuotedStop (UnquotedId id) = idStop id
  | maybeQuotedStop (QuotedId id) = idStop id

fun decSpan (DecSemi p) = (p, p + 1)
  | decSpan (DecVal {val_, elems = {stop, ...}, ...}) = (val_, stop)
  | decSpan (DecFun {fun_, fvalbind = {stop, ...}, ...}) = (fun_, stop)
  | decSpan (DecType {type_, tybind = {stop, ...}, ...}) = (type_, stop)
  | decSpan (DecEqtype {eqtype_, tybind = {stop, ...}, ...}) = (eqtype_, stop)
  | decSpan (DecDatatype {datatype_, withtype_ = SOME {tybind = {stop, ...}, ...}, ...}) =
    (datatype_, stop)
  | decSpan (DecDatatype {datatype_, withtype_ = NONE, datbind = {stop, ...}, ...}) =
    (datatype_, stop)
  | decSpan (DecAbstype {abstype_, withtype_ = SOME {tybind = {stop, ...}, ...}, ...}) =
    (abstype_, stop)
  | decSpan (DecAbstype {abstype_, withtype_ = NONE, datbind = {stop, ...}, ...}) =
    (abstype_, stop)
  | decSpan (DecException {exception_, elems = {stop, ...}, ...}) = (exception_, stop)
  | decSpan (DecLocal {local_, stop, ...}) = (local_, stop)
  | decSpan (DecOpen {open_, elems, ...}) =
    (open_, idStop (List.last elems) handle List.Empty => open_ + 4)
  | decSpan (DecInfix {infix_, prec, elems, ...}) =
    (infix_, idStop (List.last elems) handle List.Empty =>
      case prec of SOME p => idStop p | NONE => infix_ + 5)
  | decSpan (DecInfixr {infixr_, prec, elems, ...}) =
    (infixr_, idStop (List.last elems) handle List.Empty =>
      case prec of SOME p => idStop p | NONE => infixr_ + 6)
  | decSpan (DecNonfix {nonfix_, elems, ...}) =
    (nonfix_, idStop (List.last elems) handle List.Empty => nonfix_ + 6)
  | decSpan (DecStructure {structure_, elems = {stop, ...}, ...}) = (structure_, stop)
  | decSpan (DecSignature {signature_, elems = {stop, ...}, ...}) = (signature_, stop)
  | decSpan (DecInclude {include_, sigexps, ...}) =
    (include_, sigexpStop (List.last sigexps) handle List.Empty => include_ + 7)
  | decSpan (Sharing {sharing_, elems = {stop, ...}, ...}) = (sharing_, stop)
  | decSpan (DecFunctor {functor_, elems = {stop, ...}, ...}) = (functor_, stop)
  | decSpan (DecExp e) = expSpan e
  | decSpan (HOLTheory {theory_, id, attrs, elems}) =
    (theory_, headerStop (List.last elems) handle List.Empty =>
      case attrs of NONE => idStop id | SOME {stop, ...} => stop)
  | decSpan (HOLTheoryEnd {stop, ...}) = (stop, stop)
  | decSpan (HOLDefinition {definition_, stop, ...}) = (definition_, stop)
  | decSpan (HOLDatatype {datatype_, stop, ...}) = (datatype_, stop)
  | decSpan (HOLQuoteDecl {quote_, stop, ...}) = (quote_, stop)
  | decSpan (HOLInductiveDecl {inductive_, stop, ...}) = (inductive_, stop)
  | decSpan (HOLType {type_, id, attrs, bind, ...}) =
    (type_, case bind of SOME {exp, ...} => expStop exp | NONE =>
      case attrs of SOME {stop, ...} => stop | NONE => maybeQuotedStop id)
  | decSpan (HOLSimpleThm {theorem_, id, attrs, bind, ...}) =
    (theorem_, case bind of SOME {exp, ...} => expStop exp | NONE =>
      case attrs of SOME {stop, ...} => stop | NONE => idStop id)
  | decSpan (HOLTheoremDecl {theorem_, stop, ...}) = (theorem_, stop)
  | decSpan (HOLResume {resume_, stop, ...}) = (resume_, stop)
  | decSpan (HOLFinalise {finalise_, stop, ...}) = (finalise_, stop)
  | decSpan (DecBad {start, stop}) = (start, stop)
  | decSpan (DecExpansion {orig, ...}) = decSpan orig

val decStart = #1 o decSpan
val decStop = #2 o decSpan

fun isOnlyComments s = let
  val (base, start, len) = Substring.base s
  val stop = start + len
  fun cur p = if p < stop then String.sub (base, p) else #"\000"
  fun go cm p =
    case cur p of
      #"\000" => true
    | #"(" => cur (p+1) = #"*" andalso go (cm + 1) (p+2)
    | #"*" => cm > 0 andalso if cur (p+1) = #")" then go (cm - 1) (p+2) else go cm (p+1)
    | c => (cm > 0 orelse Char.isSpace c) andalso go cm (p+1)
  in go 0 start end

datatype event =
  FileEvent of int * string
| LineEvent of int * int
| LineColEvent of int * int * int

type events = {
  initFile: string,
  evts: event DArray.darray }

type cursor = {
  body: DString.dstring, evts: events,
  file: string, pos: int, line: int, col: int, idx: int }

fun newCursor body evts: cursor =
  {body = body, evts = evts, file = #initFile evts, pos = 0, line = 0, col = 0, idx = 0}

fun eventPos (FileEvent (p, _)) = p
  | eventPos (LineEvent (p, _)) = p
  | eventPos (LineColEvent (p, _, _)) = p

fun updateCursorSimple ({body, evts, file, pos, line, col, idx}: cursor, p) = let
  fun countLines i line last =
    if i = p then (line, p - last) else
    if DString.sub (body, i) = #"\n" then countLines (i+1) (line+1) (i+1) else
    countLines (i+1) line last
  fun firstLine i =
    if i = p then (line, col + p - pos) else
    if DString.sub (body, i) = #"\n" then countLines (i+1) (line+1) (i+1) else
    firstLine (i+1)
  val (line, col) = firstLine pos
  in {body = body, evts = evts, file = file, pos = p, line = line, col = col, idx = idx} end

fun updateCursor (cur: cursor as {body, evts, pos, ...}, p): cursor =
  if p < pos then updateCursor (newCursor body evts, p) (* TODO walk backwards *)
  else let
    fun readEvts (cur as {evts, idx, ...}) =
      case SOME (DArray.sub (#evts evts, idx)) handle Subscript => NONE of
        NONE => updateCursorSimple (cur, p)
      | SOME e => if p < eventPos e then updateCursorSimple (cur, p) else let
        val {body, evts, file, pos, line, col, idx} = updateCursorSimple (cur, eventPos e)
        val cur = case e of
          FileEvent (_, file) =>
          {body = body, evts = evts, file = file, pos = pos, line = line, col = col, idx = idx+1}
        | LineEvent (_, line) =>
          {body = body, evts = evts, file = file, pos = pos, line = line, col = col, idx = idx+1}
        | LineColEvent (_, line, col) =>
          {body = body, evts = evts, file = file, pos = pos, line = line, col = col, idx = idx+1}
        in readEvts cur end
    in readEvts cur end

fun mkFileline body evts =
  case ref (newCursor body evts) of cur => fn p =>
  case updateCursor (!cur, p) of cur' as {file, line, col, ...} =>
  (cur := cur'; {file = file, line = line, col = col})

end
