(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)


(** Think of ASTs as sitting on top of a token sequence. Each node of the AST
  * represents a slice of tokens. Each token of the input should appear
  * exactly once. Traversing the AST can be used to recover the original token
  * sequence. This requires including tokens for mundane things (e.g. such as
  * the colons in type annotations) but is great for completely tracking
  * provenance!
  *)
structure AstType =
struct

  (** Used for syntactic classes that look like:
    *
    *   Xseq  ::=               -- empty
    *           | X             -- singleton
    *           | (X, ..., X)   -- sequence enclosed by parens
    *
    * e.g. tyseq, tyvarseq, etc.
    *)
  structure SyntaxSeq =
  struct
    datatype 'a t =
      Empty
    | One of 'a
    | Many of
        { left: Token.t (** open paren *)
        , elems: 'a Seq.t (** elements *)
        , delims: Token.t Seq.t (** commas between elements *)
        , right: Token.t (** close paren *)
        }
  end


  (** ======================================================================
    * Types.
    *)
  structure Ty =
  struct
    datatype ty =
      Var of Token.t

    (** { lab : ty, ..., lab : ty } *)
    | Record of
        { left: Token.t
        , elems: {lab: Token.t, colon: Token.t, ty: ty} Seq.t
        , delims: Token.t Seq.t
        , right: Token.t
        }

    (** ty * ... * ty *)
    | Tuple of {elems: ty Seq.t, delims: Token.t Seq.t}

    (** tyseq longtycon *)
    | Con of {args: ty SyntaxSeq.t, id: MaybeLongToken.t}

    (** ty -> ty *)
    | Arrow of {from: ty, arrow: Token.t, to: ty}

    (** ( ty ) *)
    | Parens of {left: Token.t, ty: ty, right: Token.t}

    type t = ty
  end


  (** ======================================================================
    * Patterns.
    *)
  structure Pat =
  struct

    datatype patrow =
      DotDotDot of Token.t (** can only appear at end of record pattern *)

    | LabEqPat of {lab: Token.t, eq: Token.t, pat: pat}

    | LabAsPat of
        { id: Token.t
        , ty: {colon: Token.t, ty: Ty.t} option
        , aspat: {ass: Token.t, pat: pat} option
        }


    and pat =
      Wild of Token.t

    | Const of Token.t

    | Unit of {left: Token.t, right: Token.t}

    (** [op] longvid *)
    | Ident of {opp: Token.t option, id: MaybeLongToken.t}

    (** [ pat, ..., pat ] *)
    | List of
        {left: Token.t, elems: pat Seq.t, delims: Token.t Seq.t, right: Token.t}

    (** ( pat, ..., pat ) *)
    | Tuple of
        { left: Token.t
        , elems: pat Seq.t
        , delims: Token.t Seq.t (** Gotta remember the commas too! *)
        , right: Token.t
        }

    (** { lab = pat, ..., lab = pat } *)
    | Record of
        { left: Token.t
        , elems: patrow Seq.t
        , delims: Token.t Seq.t
        , right: Token.t
        }

    (** ( pat ) *)
    | Parens of {left: Token.t, pat: pat, right: Token.t}

    (** [op] longvid atpat *)
    | Con of {opp: Token.t option, id: MaybeLongToken.t, atpat: pat}

    (** pat vid pat *)
    | Infix of {left: pat, id: Token.t, right: pat}

    (** pat : ty *)
    | Typed of {pat: pat, colon: Token.t, ty: Ty.t}

    (** [op] vid [:ty] as pat *)
    | Layered of
        { opp: Token.t option
        , id: Token.t
        , ty: {colon: Token.t, ty: Ty.t} option
        , ass: Token.t (** the `as` of course *)
        , pat: pat
        }

    (** SuccessorML "or patterns":
      * pat | pat | ... | pat *)
    | Or of {elems: pat Seq.t, delims: Token.t Seq.t (* `|` between pats *)}

    type t = pat
  end


  (** ======================================================================
    * Expressions and declarations.
    *)
  structure Exp =
  struct

    (** tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
    type typbind =
      { elems:
          {tyvars: Token.t SyntaxSeq.t, tycon: Token.t, eq: Token.t, ty: Ty.t} Seq.t
      (** the `and` delimiters between bindings *)
      , delims: Token.t Seq.t
      }


    (** tyvarseq tycon = conbind [and tyvarseq tycon = conbind ...]
      * where conbind ::= [op] vid [of ty] [| [op] vid [of ty] ...]
      *)
    type datbind =
      { elems:
          { tyvars: Token.t SyntaxSeq.t
          , tycon: Token.t
          , eq: Token.t
          , elems:
              { opp: Token.t option
              , id: Token.t
              , arg: {off: Token.t, ty: Ty.t} option
              } Seq.t
          (** the `|` delimiters between bindings *)
          , delims: Token.t Seq.t

          (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
          , optbar: Token.t option
          } Seq.t

      (** the `and` delimiters between bindings *)
      , delims: Token.t Seq.t
      }


    (** Functions can be defined either in prefix style
      *
      *   fun [op]name arg1 arg2 arg3 ... [: ty] = ...
      *
      * or in infix style
      *
      *   fun arg1 name arg2 [: ty] = ...
      *   fun (arg1 name arg2) arg3 ... [: ty] = ...
      *
      * In the infix style, it's a bit annoying, because if there are
      * additional curried arguments then there needs to be parentheses
      * around the infix part.
      *
      * Note that the arguments always must be atomic patterns
      *)
    datatype fname_args =
      PrefixedFun of {opp: Token.t option, id: Token.t, args: Pat.t Seq.t}

    | InfixedFun of {larg: Pat.t, id: Token.t, rarg: Pat.t}

    | CurriedInfixedFun of
        { lparen: Token.t
        , larg: Pat.t
        , id: Token.t
        , rarg: Pat.t
        , rparen: Token.t
        , args: Pat.t Seq.t
        }


    type 'exp fvalbind =
      { elems:
          { elems:
              { fname_args: fname_args
              , ty: {colon: Token.t, ty: Ty.t} option
              , eq: Token.t
              , exp: 'exp
              } Seq.t

          (** the `|` delimiters *)
          , delims: Token.t Seq.t

          (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
          , optbar: Token.t option
          } Seq.t

      (** the `and` delimiters *)
      , delims: Token.t Seq.t
      }


    datatype 'exp row_exp =
      RecordRow of {lab: Token.t, eq: Token.t, exp: 'exp}
    | RecordPun of {id: Token.t}


    datatype exp =
      Const of Token.t

    (** [op] longvid *)
    | Ident of {opp: Token.t option, id: MaybeLongToken.t}

    (** { lab = pat, ..., lab = pat } *)
    | Record of
        { left: Token.t
        , elems: exp row_exp Seq.t
        , delims: Token.t Seq.t (** Gotta remember the commas too! *)
        , right: Token.t
        }

    (** # label *)
    | Select of {hash: Token.t, label: Token.t}

    (** () *)
    | Unit of {left: Token.t, right: Token.t}

    (** (exp, ..., exp) *)
    | Tuple of
        { left: Token.t (** open paren *)
        , elems: exp Seq.t (** elements *)
        , delims: Token.t Seq.t (** commas between elements *)
        , right: Token.t (** close paren *)
        }

    (** [exp, ..., exp] *)
    | List of
        {left: Token.t, elems: exp Seq.t, delims: Token.t Seq.t, right: Token.t}

    (** (exp; ...; exp) *)
    | Sequence of
        {left: Token.t, elems: exp Seq.t, delims: Token.t Seq.t, right: Token.t}

    (** let dec in exp [; exp ...] end *)
    | LetInEnd of
        { lett: Token.t
        , dec: dec
        , inn: Token.t
        , exps: exp Seq.t
        , delims: Token.t Seq.t
        , endd: Token.t
        }

    (** ( exp ) *)
    | Parens of {left: Token.t, exp: exp, right: Token.t}

    (** exp exp
      * (Note: needs to be restricted by AtExp < AppExp < InfExp < Exp)
      *)
    | App of
        { left: exp (** the function expression *)
        , right: exp (** the argument expression *)
        }

    (** exp vid exp
      * (Note: needs to be restricted by AtExp < AppExp < InfExp < Exp)
      *)
    | Infix of {left: exp, id: Token.t, right: exp}

    (** exp : ty *)
    | Typed of {exp: exp, colon: Token.t, ty: Ty.t}

    (** exp andalso exp *)
    | Andalso of {left: exp, andalsoo: Token.t, right: exp}

    (** exp orelse exp *)
    | Orelse of {left: exp, orelsee: Token.t, right: exp}

    (** exp handle pat => exp [| pat => exp ...] *)
    | Handle of
        { exp: exp
        , handlee: Token.t
        , elems: {pat: Pat.t, arrow: Token.t, exp: exp} Seq.t
        , delims: Token.t Seq.t (** the bars between match rules *)

        (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
        , optbar: Token.t option
        }

    (** raise exp *)
    | Raise of {raisee: Token.t, exp: exp}

    (** if exp then exp else exp *)
    | IfThenElse of
        { iff: Token.t
        , exp1: exp
        , thenn: Token.t
        , exp2: exp
        , elsee: Token.t
        , exp3: exp
        }

    (** while exp do exp *)
    | While of {whilee: Token.t, exp1: exp, doo: Token.t, exp2: exp}

    (** case exp of pat => exp [| pat => exp ...] *)
    | Case of
        { casee: Token.t
        , exp: exp
        , off: Token.t
        , elems: {pat: Pat.t, arrow: Token.t, exp: exp} Seq.t
        , delims: Token.t Seq.t (** the bars between match rules *)

        (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
        , optbar: Token.t option
        }

    (** fn pat => exp [| pat => exp ...] *)
    | Fn of
        { fnn: Token.t
        , elems: {pat: Pat.t, arrow: Token.t, exp: exp} Seq.t
        , delims: Token.t Seq.t (** the bars between match rules *)

        (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
        , optbar: Token.t option
        }

    (** things like _prim, _import, etc.
      * contains arbitrary tokens until ended by a semicolon
      *)
    | MLtonSpecific of
        { underscore: Token.t (** must be exactly adjacent to the directive *)
        , directive: Token.t (** prim, import, etc. *)
        , contents: Token.t Seq.t
        , semicolon: Token.t
        }


    and dec =
      DecEmpty

    (** val tyvarseq [rec] pat = exp [and [rec] pat = exp ...] *)
    | DecVal of
        { vall: Token.t
        , tyvars: Token.t SyntaxSeq.t
        , elems: {recc: Token.t option, pat: Pat.t, eq: Token.t, exp: exp} Seq.t
        (** the `and` delimiters between bindings *)
        , delims: Token.t Seq.t
        }

    (** fun tyvarseq [op]vid atpat ... atpat [: ty] = exp [| ...] *)
    | DecFun of
        {funn: Token.t, tyvars: Token.t SyntaxSeq.t, fvalbind: exp fvalbind}

    (** type tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
    | DecType of {typee: Token.t, typbind: typbind}

    (** datatype datbind [withtype typbind] *)
    | DecDatatype of
        { datatypee: Token.t
        , datbind: datbind
        , withtypee: {withtypee: Token.t, typbind: typbind} option
        }

    (** datatype tycon = datatype longtycon *)
    | DecReplicateDatatype of
        { left_datatypee: Token.t
        , left_id: Token.t
        , eq: Token.t
        , right_datatypee: Token.t
        , right_id: MaybeLongToken.t
        }

    (** abstype datbind [withtype typbind] with dec end *)
    | DecAbstype of
        { abstypee: Token.t
        , datbind: datbind
        , withtypee: {withtypee: Token.t, typbind: typbind} option
        , withh: Token.t
        , dec: dec
        , endd: Token.t
        }

    (** exception exbind *)
    | DecException of
        { exceptionn: Token.t
        , elems: exbind Seq.t
        (** the `and` delimiters between bindings *)
        , delims: Token.t Seq.t
        }

    (** local dec in dec end *)
    | DecLocal of
        { locall: Token.t
        , left_dec: dec
        , inn: Token.t
        , right_dec: dec
        , endd: Token.t
        }

    (** open longstrid [longstrid ...] *)
    | DecOpen of {openn: Token.t, elems: MaybeLongToken.t Seq.t}

    (** dec [[;] dec ...]
      *
      * delims are same length as elems (every dec can end with a semicolon)
      *)
    | DecMultiple of {elems: dec Seq.t, delims: Token.t option Seq.t}

    (** infix [d] vid [vid ...] *)
    | DecInfix of
        {infixx: Token.t, precedence: Token.t option, elems: Token.t Seq.t}

    (** infixr [d] vid [vid ...] *)
    | DecInfixr of
        {infixrr: Token.t, precedence: Token.t option, elems: Token.t Seq.t}

    (** nonfix vid [vid ...] *)
    | DecNonfix of {nonfixx: Token.t, elems: Token.t Seq.t}


    and exbind =
      ExnNew of
        {opp: Token.t option, id: Token.t, arg: {off: Token.t, ty: Ty.t} option}

    | ExnReplicate of
        { opp: Token.t option
        , left_id: Token.t
        , eq: Token.t
        , right_id: MaybeLongToken.t
        }

  end


  (** =======================================================================
    * Module Signatures
    *)
  structure Sig =
  struct

    (** tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
    (* This is the same as Exp.typbind *)
    type typbind =
      { elems:
          {tyvars: Token.t SyntaxSeq.t, tycon: Token.t, eq: Token.t, ty: Ty.t} Seq.t
      (** the `and` delimiters between bindings *)
      , delims: Token.t Seq.t
      }


    datatype spec =
      EmptySpec

    (** val vid : ty [and vid : ty and ...] *)
    | Val of
        { vall: Token.t
        , elems: {vid: Token.t, colon: Token.t, ty: Ty.t} Seq.t
        (** 'and' delimiters between mutually recursive values *)
        , delims: Token.t Seq.t
        }

    (** type tyvarseq tycon [and tyvarseq tycon ...] *)
    | Type of
        { typee: Token.t
        , elems: {tyvars: Token.t SyntaxSeq.t, tycon: Token.t} Seq.t
        (** 'and' delimiters between mutually recursive types *)
        , delims: Token.t Seq.t
        }

    | TypeAbbreviation of {typee: Token.t, typbind: typbind}

    (** eqtype tyvarseq tycon [and tyvarseq tycon ...] *)
    | Eqtype of
        { eqtypee: Token.t
        , elems: {tyvars: Token.t SyntaxSeq.t, tycon: Token.t} Seq.t
        (** 'and' delimiters between mutually recursive types *)
        , delims: Token.t Seq.t
        }

    (** datatype tyvarseq tycon = condesc [and tyvarseq tycon ...] *)
    | Datatype of
        { datatypee: Token.t
        , elems:
            { tyvars: Token.t SyntaxSeq.t
            , tycon: Token.t
            , eq: Token.t
            , elems: {vid: Token.t, arg: {off: Token.t, ty: Ty.t} option} Seq.t
            (** '|' delimiters between clauses *)
            , delims: Token.t Seq.t
            (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
            , optbar: Token.t option
            } Seq.t
        (** 'and' delimiters between mutually recursive datatypes *)
        , delims: Token.t Seq.t
        (** SuccessorML: withtype in signatures *)
        , withtypee: {withtypee: Token.t, typbind: typbind} option
        }

    (** datatype tycon = datatype longtycon *)
    | ReplicateDatatype of
        { left_datatypee: Token.t
        , left_id: Token.t
        , eq: Token.t
        , right_datatypee: Token.t
        , right_id: MaybeLongToken.t
        }

    (** exception vid [of ty] [and vid [of ty] ...] *)
    | Exception of
        { exceptionn: Token.t
        , elems: {vid: Token.t, arg: {off: Token.t, ty: Ty.t} option} Seq.t
        (** 'and' delimiters between exceptions *)
        , delims: Token.t Seq.t
        }

    (** structure strid : sigexp [and strid : sigep ...] *)
    | Structure of
        { structuree: Token.t
        , elems: {id: Token.t, colon: Token.t, sigexp: sigexp} Seq.t
        , delims: Token.t Seq.t
        }

    (** include sigexp *)
    | Include of {includee: Token.t, sigexp: sigexp}

    (** include sigid ... sigid *)
    | IncludeIds of {includee: Token.t, sigids: Token.t Seq.t}

    (** spec sharing type longtycon1 = ... = longtyconn *)
    | SharingType of
        { spec: spec
        , sharingg: Token.t
        , typee: Token.t
        , elems: MaybeLongToken.t Seq.t
        (** the '=' delimiters between longtycons *)
        , delims: Token.t Seq.t
        }

    (** spec sharing longstrid = ... = longstrid *)
    | Sharing of
        { spec: spec
        , sharingg: Token.t
        , elems: MaybeLongToken.t Seq.t
        (** the '=' delimiters between longstrids *)
        , delims: Token.t Seq.t
        }

    (** spec [[;] spec ...] *)
    | Multiple of {elems: spec Seq.t, delims: Token.t option Seq.t}


    and sigexp =
      Ident of Token.t

    (** sig spec end *)
    | Spec of {sigg: Token.t, spec: spec, endd: Token.t}

    (** sigexp where type tyvarseq tycon = ty [where type ...]
      *
      * NOTE: permitted to do 'and type' instead of 'where type' if it is
      * not the first in the sequence, for example
      * sig ... end where type ... and type ...
      *)
    | WhereType of
        { sigexp: sigexp
        , elems:
            { wheree: Token.t
            , typee: Token.t
            , tyvars: Token.t SyntaxSeq.t
            , tycon: MaybeLongToken.t
            , eq: Token.t
            , ty: Ty.t
            } Seq.t
        }


    and sigdec =

    (** signature sigid = sigexp [and ...] *)
      Signature of
        { signaturee: Token.t
        , elems: {ident: Token.t, eq: Token.t, sigexp: sigexp} Seq.t

        (** 'and' between elems *)
        , delims: Token.t Seq.t
        }

  end


  (** =======================================================================
    * Module Structures
    *)
  structure Str =
  struct

    datatype strexp =
      Ident of MaybeLongToken.t

    | Struct of {structt: Token.t, strdec: strdec, endd: Token.t}

    | Constraint of
        { strexp: strexp
        , colon: Token.t (** either : or :> *)
        , sigexp: Sig.sigexp
        }

    | FunAppExp of
        {funid: Token.t, lparen: Token.t, strexp: strexp, rparen: Token.t}

    | FunAppDec of
        {funid: Token.t, lparen: Token.t, strdec: strdec, rparen: Token.t}

    | LetInEnd of
        { lett: Token.t
        , strdec: strdec
        , inn: Token.t
        , strexp: strexp
        , endd: Token.t
        }


    and strdec =
      DecEmpty

    | DecCore of Exp.dec

    | DecStructure of
        { structuree: Token.t
        , elems:
            { strid: Token.t
            , constraint:
                {colon: Token.t (** either : or :> *), sigexp: Sig.sigexp} option
            , eq: Token.t
            , strexp: strexp
            } Seq.t

        (** 'and' between elems *)
        , delims: Token.t Seq.t
        }

    | DecMultiple of {elems: strdec Seq.t, delims: Token.t option Seq.t}

    | DecLocalInEnd of
        { locall: Token.t
        , strdec1: strdec
        , inn: Token.t
        , strdec2: strdec
        , endd: Token.t
        }

    (** _overload prec name : ty as longvid [and longvid ...] *)
    | MLtonOverload of
        { underscore: Token.t
        , overload: Token.t
        , prec: Token.t
        , name: Token.t
        , colon: Token.t
        , ty: Ty.t
        , ass: Token.t
        , elems: MaybeLongToken.t Seq.t
        , delims: Token.t Seq.t
        }

  end


  (** =======================================================================
    * Module Functors
    *)
  structure Fun =
  struct

    datatype funarg =
      ArgIdent of {strid: Token.t, colon: Token.t, sigexp: Sig.sigexp}

    | ArgSpec of Sig.spec


    datatype fundec =
      DecFunctor of
        { functorr: Token.t
        , elems:
            { funid: Token.t
            , lparen: Token.t
            , funarg: funarg
            , rparen: Token.t
            , constraint:
                {colon: Token.t (** either : or :> *), sigexp: Sig.sigexp} option
            , eq: Token.t
            , strexp: Str.strexp
            } Seq.t
        (** 'and' between elems *)
        , delims: Token.t Seq.t
        }

  end


  (** =======================================================================
    * Top-level. Programs are sequences of top-level declarations.
    * Something a little cumbersome: strdec permits standard declarations too,
    * of values, types, etc. IMO this doesn't align with anyone's intuitive
    * understanding of the language, but (I suppose) it is somewhat convenient
    * for avoid unnecessary ambiguity in the grammar.
    *)
  datatype topdec =
    SigDec of Sig.sigdec
  | StrDec of Str.strdec
  | FunDec of Fun.fundec
  | TopExp of {exp: Exp.exp, semicolon: Token.t}

  datatype ast =
  (** optional semicolon after every topdec *)
    Ast of {topdec: topdec, semicolon: Token.t option} Seq.t

  type t = ast

end
