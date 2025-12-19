signature HOLAst = sig

(* (start, content) *)
type ident = int * string

type fileline = {file: string, line: int, col: int}

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

val mkIdent: ident -> exp

val decodeStr: (int * int -> string -> unit) -> string -> int -> int -> string

val encodeStr: substring -> string -> string -> string

val mkString: int * string -> exp
val mkInt: int * int -> exp
val mkList: int * exp list -> exp
val mkTuple: int * exp list -> exp
val mkApp: exp -> exp list -> exp

val idStop: ident -> int
val idSpan: ident -> int * int
val tyStart: ty -> int
val tyStop: ty -> int
val tySpan: ty -> int * int
val expStart: exp -> int
val expStop: exp -> int
val expSpan: exp -> int * int
val exbindStop: exbind -> int
val sigexpStart: sigexp -> int
val sigexpStop: sigexp -> int
val sigexpSpan: sigexp -> int * int
val strexpSpan: strexp -> int * int
val headerStop: header -> int
val decStart: dec -> int
val decStop: dec -> int
val decSpan: dec -> int * int

val isOnlyComments: substring -> bool

datatype event =
  FileEvent of int * string
| LineEvent of int * int
| LineColEvent of int * int * int

val eventPos: event -> int

type events = {
  initFile: string,
  evts: event DArray.darray }

type cursor = {
  body: DString.dstring, evts: events,
  file: string, pos: int, line: int, col: int, idx: int }

val newCursor: DString.dstring -> events -> cursor
val updateCursor: cursor * int -> cursor

val mkFileline: DString.dstring -> events -> int -> fileline

end;
