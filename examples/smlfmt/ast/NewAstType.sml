(** Based on smlfmt by Sam Westrick, which is released under the MIT license.
  *
  * See the file LICENSE for details.
  *)

(** In smlfmt, the AST sits on top of a token sequence. We take a different
    approach, where the tokens belong to a node in the AST, i.e., there is
    no separate list of tokens. *)
(* TODO Explain why we take a different approach *)
structure NewAstType =
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
        { left: NewToken.t (** open paren *)
        , elems: 'a Seq.t (** elements *)
        , delims: NewToken.t Seq.t (** commas between elements *)
        , right: NewToken.t (** close paren *)
        }
  end


  (** ======================================================================
    * Types.
    *)
  structure Ty =
  struct
    datatype ty =
      Var of NewToken.t

    (** { lab : ty, ..., lab : ty } *)
    | Record of
        { left: NewToken.t
        , elems: {lab: NewToken.t, colon: NewToken.t, ty: ty} Seq.t
        , delims: NewToken.t Seq.t
        , right: NewToken.t
        }

    (** ty * ... * ty *)
    | Tuple of {elems: ty Seq.t, delims: NewToken.t Seq.t}

    (** tyseq longtycon *)
    | Con of {args: ty SyntaxSeq.t, id: NewToken.t}

    (** ty -> ty *)
    | Arrow of {from: ty, arrow: NewToken.t, to: ty}

    (** ( ty ) *)
    | Parens of {left: NewToken.t, ty: ty, right: NewToken.t}

    type t = ty
  end


  (** ======================================================================
    * Patterns.
    *)
  structure Pat =
  struct

    datatype patrow =
      DotDotDot of NewToken.t (** can only appear at end of record pattern *)

    | LabEqPat of {lab: NewToken.t, eq: NewToken.t, pat: pat}

    | LabAsPat of
        { id: NewToken.t
        , ty: {colon: NewToken.t, ty: Ty.t} option
        , aspat: {ass: NewToken.t, pat: pat} option
        }


    and pat =
      Wild of NewToken.t

    | Const of NewToken.t

    | Unit of {left: NewToken.t, right: NewToken.t}

    (** [op] longvid *)
    | Ident of {op_: NewToken.t option, id: NewToken.t}

    (** [ pat, ..., pat ] *)
    | List of
        {left: NewToken.t, elems: pat Seq.t, delims: NewToken.t Seq.t, right: NewToken.t}

    (** ( pat, ..., pat ) *)
    | Tuple of
        { left: NewToken.t
        , elems: pat Seq.t
        , delims: NewToken.t Seq.t (** Gotta remember the commas too! *)
        , right: NewToken.t
        }

    (** { lab = pat, ..., lab = pat } *)
    | Record of
        { left: NewToken.t
        , elems: patrow Seq.t
        , delims: NewToken.t Seq.t
        , right: NewToken.t
        }

    (** ( pat ) *)
    | Parens of {left: NewToken.t, pat: pat, right: NewToken.t}

    (** [op] longvid atpat *)
    | Con of {op_: NewToken.t option, id: NewToken.t, atpat: pat}

    (** pat vid pat *)
    | Infix of {left: pat, id: NewToken.t, right: pat}

    (** pat : ty *)
    | Typed of {pat: pat, colon: NewToken.t, ty: Ty.t}

    (** [op] vid [:ty] as pat *)
    | Layered of
        { op_: NewToken.t option
        , id: NewToken.t
        , ty: {colon: NewToken.t, ty: Ty.t} option
        , as_: NewToken.t (** the `as` of course *)
        , pat: pat
        }

    (** SuccessorML "or patterns":
      * pat | pat | ... | pat *)
    | Or of {elems: pat Seq.t, delims: NewToken.t Seq.t (* `|` between pats *)}

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
          {tyvars: NewToken.t SyntaxSeq.t, tycon: NewToken.t, eq: NewToken.t, ty: Ty.t} Seq.t
      (** the `and` delimiters between bindings *)
      , delims: NewToken.t Seq.t
      }


    (** tyvarseq tycon = conbind [and tyvarseq tycon = conbind ...]
      * where conbind ::= [op] vid [of ty] [| [op] vid [of ty] ...]
      *)
    type datbind =
      { elems:
          { tyvars: NewToken.t SyntaxSeq.t
          , tycon: NewToken.t
          , eq: NewToken.t
          , elems:
              { op_: NewToken.t option
              , id: NewToken.t
              , arg: {off: NewToken.t, ty: Ty.t} option
              } Seq.t
          (** the `|` delimiters between bindings *)
          , delims: NewToken.t Seq.t

          (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
          , optbar: NewToken.t option
          } Seq.t

      (** the `and` delimiters between bindings *)
      , delims: NewToken.t Seq.t
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
      PrefixedFun of {op_: NewToken.t option, id: NewToken.t, args: Pat.t Seq.t}

    | InfixedFun of {larg: Pat.t, id: NewToken.t, rarg: Pat.t}

    | CurriedInfixedFun of
        { lparen: NewToken.t
        , larg: Pat.t
        , id: NewToken.t
        , rarg: Pat.t
        , rparen: NewToken.t
        , args: Pat.t Seq.t
        }


    type 'exp fvalbind =
      { elems:
          { elems:
              { fname_args: fname_args
              , ty: {colon: NewToken.t, ty: Ty.t} option
              , eq: NewToken.t
              , exp: 'exp
              } Seq.t

          (** the `|` delimiters *)
          , delims: NewToken.t Seq.t

          (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
          , optbar: NewToken.t option
          } Seq.t

      (** the `and` delimiters *)
      , delims: NewToken.t Seq.t
      }


    datatype 'exp row_exp =
      RecordRow of {lab: NewToken.t, eq: NewToken.t, exp: 'exp}
    | RecordPun of {id: NewToken.t}


    datatype exp =
      Const of NewToken.t

    (** [op] longvid *)
    | Ident of {op_: NewToken.t option, id: NewToken.t}

    (** { lab = pat, ..., lab = pat } *)
    | Record of
        { left: NewToken.t
        , elems: exp row_exp Seq.t
        , delims: NewToken.t Seq.t (** Gotta remember the commas too! *)
        , right: NewToken.t
        }

    (** # label *)
    | Select of {hash: NewToken.t, label: NewToken.t}

    (** () *)
    | Unit of {left: NewToken.t, right: NewToken.t}

    (** (exp, ..., exp) *)
    | Tuple of
        { left: NewToken.t (** open paren *)
        , elems: exp Seq.t (** elements *)
        , delims: NewToken.t Seq.t (** commas between elements *)
        , right: NewToken.t (** close paren *)
        }

    (** [exp, ..., exp] *)
    | List of
        {left: NewToken.t, elems: exp Seq.t, delims: NewToken.t Seq.t, right: NewToken.t}

    (** (exp; ...; exp) *)
    | Sequence of
        {left: NewToken.t, elems: exp Seq.t, delims: NewToken.t Seq.t, right: NewToken.t}

    (** let dec in exp [; exp ...] end *)
    | LetInEnd of
        { let_: NewToken.t
        , dec: dec
        , in_: NewToken.t
        , exps: exp Seq.t
        , delims: NewToken.t Seq.t
        , end_: NewToken.t
        }

    (** ( exp ) *)
    | Parens of {left: NewToken.t, exp: exp, right: NewToken.t}

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
    | Infix of {left: exp, id: NewToken.t, right: exp}

    (** exp : ty *)
    | Typed of {exp: exp, colon: NewToken.t, ty: Ty.t}

    (** exp andalso exp *)
    | Andalso of {left: exp, andalso_: NewToken.t, right: exp}

    (** exp orelse exp *)
    | Orelse of {left: exp, orelse_: NewToken.t, right: exp}

    (** exp handle pat => exp [| pat => exp ...] *)
    | Handle of
        { exp: exp
        , handle_: NewToken.t
        , elems: {pat: Pat.t, arrow: NewToken.t, exp: exp} Seq.t
        , delims: NewToken.t Seq.t (** the bars between match rules *)

        (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
        , optbar: NewToken.t option
        }

    (** raise exp *)
    | Raise of {raise_: NewToken.t, exp: exp}

    (** if exp then exp else exp *)
    | IfThenElse of
        { if_: NewToken.t
        , exp1: exp
        , then_: NewToken.t
        , exp2: exp
        , else_: NewToken.t
        , exp3: exp
        }

    (** while exp do exp *)
    | While of {while_: NewToken.t, exp1: exp, do_: NewToken.t, exp2: exp}

    (** case exp of pat => exp [| pat => exp ...] *)
    | Case of
        { case_: NewToken.t
        , exp: exp
        , of_: NewToken.t
        , elems: {pat: Pat.t, arrow: NewToken.t, exp: exp} Seq.t
        , delims: NewToken.t Seq.t (** the bars between match rules *)

        (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
        , optbar: NewToken.t option
        }

    (** fn pat => exp [| pat => exp ...] *)
    | Fn of
        { fn_: NewToken.t
        , elems: {pat: Pat.t, arrow: NewToken.t, exp: exp} Seq.t
        , delims: NewToken.t Seq.t (** the bars between match rules *)

        (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
        , optbar: NewToken.t option
        }

    (** things like _prim, _import, etc.
      * contains arbitrary tokens until ended by a semicolon
      *)
    | MLtonSpecific of
        { underscore: NewToken.t (** must be exactly adjacent to the directive *)
        , directive: NewToken.t (** prim, import, etc. *)
        , contents: NewToken.t Seq.t
        , semicolon: NewToken.t
        }


    and dec =
      DecEmpty

    (** val tyvarseq [rec] pat = exp [and [rec] pat = exp ...] *)
    | DecVal of
        { val_: NewToken.t
        , tyvars: NewToken.t SyntaxSeq.t
        , elems: {rec_: NewToken.t option, pat: Pat.t, eq: NewToken.t, exp: exp} Seq.t
        (** the `and` delimiters between bindings *)
        , delims: NewToken.t Seq.t
        }

    (** fun tyvarseq [op]vid atpat ... atpat [: ty] = exp [| ...] *)
    | DecFun of
        {fun_: NewToken.t, tyvars: NewToken.t SyntaxSeq.t, fvalbind: exp fvalbind}

    (** type tyvarseq tycon = ty [and tyvarseq tycon = ty ...] *)
    | DecType of {type_: NewToken.t, typbind: typbind}

    (** datatype datbind [withtype typbind] *)
    | DecDatatype of
        { datatype_: NewToken.t
        , datbind: datbind
        , withtype_: {withtype_: NewToken.t, typbind: typbind} option
        }

    (** datatype tycon = datatype longtycon *)
    | DecReplicateDatatype of
        { left_datatypee: NewToken.t
        , left_id: NewToken.t
        , eq: NewToken.t
        , right_datatypee: NewToken.t
        , right_id: NewToken.t
        }

    (** abstype datbind [withtype typbind] with dec end *)
    | DecAbstype of
        { abstype_: NewToken.t
        , datbind: datbind
        , withtype_: {withtype_: NewToken.t, typbind: typbind} option
        , withh: NewToken.t
        , dec: dec
        , end_: NewToken.t
        }

    (** exception exbind *)
    | DecException of
        { exception_: NewToken.t
        , elems: exbind Seq.t
        (** the `and` delimiters between bindings *)
        , delims: NewToken.t Seq.t
        }

    (** local dec in dec end *)
    | DecLocal of
        { local_: NewToken.t
        , left_dec: dec
        , in_: NewToken.t
        , right_dec: dec
        , end_: NewToken.t
        }

    (** open longstrid [longstrid ...] *)
    | DecOpen of {open_: NewToken.t, elems: NewToken.t Seq.t}

    (** dec [[;] dec ...]
      *
      * delims are same length as elems (every dec can end with a semicolon)
      *)
    | DecMultiple of {elems: dec Seq.t, delims: NewToken.t option Seq.t}

    (** infix [d] vid [vid ...] *)
    | DecInfix of
        {infix_: NewToken.t, precedence: NewToken.t option, elems: NewToken.t Seq.t}

    (** infixr [d] vid [vid ...] *)
    | DecInfixr of
        {infixr_: NewToken.t, precedence: NewToken.t option, elems: NewToken.t Seq.t}

    (** nonfix vid [vid ...] *)
    | DecNonfix of {nonfix_: NewToken.t, elems: NewToken.t Seq.t}

    (** HOLScript *)
    | DecHOLCoInductive of {head: NewToken.t, body: qbody, end_: NewToken.t}
    | DecHOLInductive of {head: NewToken.t, body: qbody, end_: NewToken.t}
    | DecHOLDatatype of {head: NewToken.t, body: qbody, end_: NewToken.t}
    | DecHOLOverload of {head: NewToken.t, term: exp}
    | DecHOLDefinition of
        { head: NewToken.t
        , body: NewToken.t list
        , termination: {tok: NewToken.t, proof: exp} option
        , end_: NewToken.t}
    | DecHOLSimpleTheorem of {head: NewToken.t, thm: exp}
    | DecHOLSimpleTriviality of {head: NewToken.t, thm: exp}
    | DecHOLTheorem of
        { head: NewToken.t
        , body: NewToken.t list
        , proof: {tok: NewToken.t, tactics: exp}
        , qed: NewToken.t}
    | DecHOLTriviality of
        { head: NewToken.t
        , body: NewToken.t list
        , proof: {tok: NewToken.t, tactics: exp}
        , qed: NewToken.t}


    and exbind =
      ExnNew of
        {op_: NewToken.t option, id: NewToken.t, arg: {of_: NewToken.t, ty: Ty.t} option}

    | ExnReplicate of
        { op_: NewToken.t option
        , left_id: NewToken.t
        , eq: NewToken.t
        , right_id: NewToken.t
        }

    and qbody = QuoteBody of {start: int, decls: qdecl list, stop: int}

    and qdecl =
      QuoteAntiq of {caret_: NewToken.t, arg: exp, stop: int}

    | QuoteDefinitionLabel of NewToken.t

    | QuoteComment of Source.range

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
          {tyvars: NewToken.t SyntaxSeq.t, tycon: NewToken.t, eq: NewToken.t, ty: Ty.t} Seq.t
      (** the `and` delimiters between bindings *)
      , delims: NewToken.t Seq.t
      }


    datatype spec =
      EmptySpec

    (** val vid : ty [and vid : ty and ...] *)
    | Val of
        { val_: NewToken.t
        , elems: {vid: NewToken.t, colon: NewToken.t, ty: Ty.t} Seq.t
        (** 'and' delimiters between mutually recursive values *)
        , delims: NewToken.t Seq.t
        }

    (** type tyvarseq tycon [and tyvarseq tycon ...] *)
    | Type of
        { type_: NewToken.t
        , elems: {tyvars: NewToken.t SyntaxSeq.t, tycon: NewToken.t} Seq.t
        (** 'and' delimiters between mutually recursive types *)
        , delims: NewToken.t Seq.t
        }

    | TypeAbbreviation of {type_: NewToken.t, typbind: typbind}

    (** eqtype tyvarseq tycon [and tyvarseq tycon ...] *)
    | Eqtype of
        { eqtype_: NewToken.t
        , elems: {tyvars: NewToken.t SyntaxSeq.t, tycon: NewToken.t} Seq.t
        (** 'and' delimiters between mutually recursive types *)
        , delims: NewToken.t Seq.t
        }

    (** datatype tyvarseq tycon = condesc [and tyvarseq tycon ...] *)
    | Datatype of
        { datatype_: NewToken.t
        , elems:
            { tyvars: NewToken.t SyntaxSeq.t
            , tycon: NewToken.t
            , eq: NewToken.t
            , elems: {vid: NewToken.t, arg: {of_: NewToken.t, ty: Ty.t} option} Seq.t
            (** '|' delimiters between clauses *)
            , delims: NewToken.t Seq.t
            (** SuccessorML: optional leading bar (not permitted in Standard ML). *)
            , optbar: NewToken.t option
            } Seq.t
        (** 'and' delimiters between mutually recursive datatypes *)
        , delims: NewToken.t Seq.t
        (** SuccessorML: withtype in signatures *)
        , withtype_: {withtype_: NewToken.t, typbind: typbind} option
        }

    (** datatype tycon = datatype longtycon *)
    | ReplicateDatatype of
        { left_datatypee: NewToken.t
        , left_id: NewToken.t
        , eq: NewToken.t
        , right_datatypee: NewToken.t
        , right_id: NewToken.t
        }

    (** exception vid [of ty] [and vid [of ty] ...] *)
    | Exception of
        { exception_: NewToken.t
        , elems: {vid: NewToken.t, arg: {of_: NewToken.t, ty: Ty.t} option} Seq.t
        (** 'and' delimiters between exceptions *)
        , delims: NewToken.t Seq.t
        }

    (** structure strid : sigexp [and strid : sigep ...] *)
    | Structure of
        { structuree: NewToken.t
        , elems: {id: NewToken.t, colon: NewToken.t, sigexp: sigexp} Seq.t
        , delims: NewToken.t Seq.t
        }

    (** include sigexp *)
    | Include of {include_: NewToken.t, sigexp: sigexp}

    (** include sigid ... sigid *)
    | IncludeIds of {include_: NewToken.t, sigids: NewToken.t Seq.t}

    (** spec sharing type longtycon1 = ... = longtyconn *)
    | SharingType of
        { spec: spec
        , sharing_: NewToken.t
        , type_: NewToken.t
        , elems: NewToken.t Seq.t
        (** the '=' delimiters between longtycons *)
        , delims: NewToken.t Seq.t
        }

    (** spec sharing longstrid = ... = longstrid *)
    | Sharing of
        { spec: spec
        , sharing_: NewToken.t
        , elems: NewToken.t Seq.t
        (** the '=' delimiters between longstrids *)
        , delims: NewToken.t Seq.t
        }

    (** spec [[;] spec ...] *)
    | Multiple of {elems: spec Seq.t, delims: NewToken.t option Seq.t}


    and sigexp =
      Ident of NewToken.t

    (** sig spec end *)
    | Spec of {sig_: NewToken.t, spec: spec, end_: NewToken.t}

    (** sigexp where type tyvarseq tycon = ty [where type ...]
      *
      * NOTE: permitted to do 'and type' instead of 'where type' if it is
      * not the first in the sequence, for example
      * sig ... end where type ... and type ...
      *)
    | WhereType of
        { sigexp: sigexp
        , elems:
            { where_: NewToken.t
            , type_: NewToken.t
            , tyvars: NewToken.t SyntaxSeq.t
            , tycon: NewToken.t
            , eq: NewToken.t
            , ty: Ty.t
            } Seq.t
        }


    and sigdec =

    (** signature sigid = sigexp [and ...] *)
      Signature of
        { signature_: NewToken.t
        , elems: {ident: NewToken.t, eq: NewToken.t, sigexp: sigexp} Seq.t

        (** 'and' between elems *)
        , delims: NewToken.t Seq.t
        }

  end


  (** =======================================================================
    * Module Structures
    *)
  structure Str =
  struct

    datatype strexp =
      Ident of NewToken.t

    | Struct of {struct_: NewToken.t, strdec: strdec, end_: NewToken.t}

    | Constraint of
        { strexp: strexp
        , colon: NewToken.t (** either : or :> *)
        , sigexp: Sig.sigexp
        }

    | FunAppExp of
        {funid: NewToken.t, lparen: NewToken.t, strexp: strexp, rparen: NewToken.t}

    | FunAppDec of
        {funid: NewToken.t, lparen: NewToken.t, strdec: strdec, rparen: NewToken.t}

    | LetInEnd of
        { let_: NewToken.t
        , strdec: strdec
        , in_: NewToken.t
        , strexp: strexp
        , end_: NewToken.t
        }


    and strdec =
      DecEmpty

    | DecCore of Exp.dec

    | DecStructure of
        { structuree: NewToken.t
        , elems:
            { strid: NewToken.t
            , constraint:
                {colon: NewToken.t (** either : or :> *), sigexp: Sig.sigexp} option
            , eq: NewToken.t
            , strexp: strexp
            } Seq.t

        (** 'and' between elems *)
        , delims: NewToken.t Seq.t
        }

    | DecMultiple of {elems: strdec Seq.t, delims: NewToken.t option Seq.t}

    | DecLocalInEnd of
        { local_: NewToken.t
        , strdec1: strdec
        , in_: NewToken.t
        , strdec2: strdec
        , end_: NewToken.t
        }

    (** _overload prec name : ty as longvid [and longvid ...] *)
    | MLtonOverload of
        { underscore: NewToken.t
        , overload: NewToken.t
        , prec: NewToken.t
        , name: NewToken.t
        , colon: NewToken.t
        , ty: Ty.t
        , ass: NewToken.t
        , elems: NewToken.t Seq.t
        , delims: NewToken.t Seq.t
        }

  end


  (** =======================================================================
    * Module Functors
    *)
  structure Fun =
  struct

    datatype funarg =
      ArgIdent of {strid: NewToken.t, colon: NewToken.t, sigexp: Sig.sigexp}

    | ArgSpec of Sig.spec


    datatype fundec =
      DecFunctor of
        { functor_: NewToken.t
        , elems:
            { funid: NewToken.t
            , lparen: NewToken.t
            , funarg: funarg
            , rparen: NewToken.t
            , constraint:
                {colon: NewToken.t (** either : or :> *), sigexp: Sig.sigexp} option
            , eq: NewToken.t
            , strexp: Str.strexp
            } Seq.t
        (** 'and' between elems *)
        , delims: NewToken.t Seq.t
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
  | TopExp of {exp: Exp.exp, semicolon: NewToken.t}

  datatype ast =
  (** optional semicolon after every topdec *)
    Ast of {topdec: topdec, semicolon: NewToken.t option} Seq.t

  type t = ast

end;
