(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)


(** See AstType.sml for the type definition. *)
structure Ast =
struct

  open AstType

  fun join (Ast td1, Ast td2) =
    Ast (Seq.append (td1, td2))

  val empty = Ast (Seq.empty ())

  structure SyntaxSeq = struct open AstType.SyntaxSeq end

  structure Ty = struct open AstType.Ty end

  structure Pat =
  struct
    open AstType.Pat

    fun okayForConPat pat =
      case pat of
        Ident _ => true
      | _ => false

    fun unpackForConPat pat =
      case pat of
        Ident {opp, id} => {opp = opp, id = id}
      | _ => raise Fail "Bug: Ast.Pat.unpackForConPat: invalid argument"

    fun isValueIdentifier pat =
      case pat of
        Ident {id, ...} =>
          Token.isValueIdentifierNoEqual (MaybeLongToken.getToken id)
      | _ => false

    fun okayForAsPat pat =
      isValueIdentifier pat
      orelse
      case pat of
        Typed {pat, ...} => isValueIdentifier pat
      | _ => false

    (** Not that the unpacked id has to be a "short" identifer. We could
      * check this here for sanity...
      *)
    fun unpackForAsPat pat =
      case pat of
        Ident {opp, id} =>
          {opp = opp, id = MaybeLongToken.getToken id, ty = NONE}
      | Typed {pat = Ident {opp, id}, colon, ty} =>
          { opp = opp
          , id = MaybeLongToken.getToken id
          , ty = SOME {colon = colon, ty = ty}
          }
      | _ => raise Fail "Bug: Ast.Pat.unpackForAsPat: invalid argument"

    fun isAtPat pat =
      case pat of
        Wild _ => true
      | Const _ => true
      | Unit _ => true
      | Ident _ => true
      | List _ => true
      | Tuple _ => true
      | Record _ => true
      | Parens _ => true
      | _ => false

    fun isAppPat pat =
      isAtPat pat
      orelse
      (case pat of
         Con _ => true
       | _ => false)

    fun isInfPat pat =
      isAppPat pat
      orelse
      (case pat of
         Infix _ => true
       | _ => false)

    fun leftMostToken pat =
      case pat of
        Wild t => t
      | Unit {left, ...} => left
      | Const t => t
      | Ident {opp, id} =>
          (case opp of
             SOME t => t
           | NONE => MaybeLongToken.getToken id)
      | List {left, ...} => left
      | Tuple {left, ...} => left
      | Record {left, ...} => left
      | Parens {left, ...} => left
      | Con {opp, id, ...} =>
          (case opp of
             SOME t => t
           | NONE => MaybeLongToken.getToken id)
      | Infix {left, ...} => leftMostToken left
      | Typed {pat, ...} => leftMostToken pat
      | Layered {opp, id, ...} =>
          (case opp of
             SOME t => t
           | NONE => id)
      | Or {elems, ...} => leftMostToken (Seq.nth elems 0)
  end

  structure Exp =
  struct
    open AstType.Exp

    fun isAtExp exp =
      case exp of
        Const _ => true
      | Ident _ => true
      | Record _ => true
      | Select _ => true
      | Unit _ => true
      | Tuple _ => true
      | List _ => true
      | Sequence _ => true
      | LetInEnd _ => true
      | Parens _ => true
      | _ => false

    fun isAppExp exp =
      isAtExp exp
      orelse
      (case exp of
         App _ => true
       | _ => false)

    fun isInfExp exp =
      isAppExp exp
      orelse
      (case exp of
         Infix _ => true
       | _ => false)

    fun isMultipleDecs dec =
      case dec of
        DecMultiple {elems, ...} => Seq.length elems > 1
      | _ => false

    (** All the names have to match. *)
    fun checkValidFValBind (fvalbind: exp fvalbind)
      (error: {what: string, pos: Source.t, explain: string option} -> unit) =
      let
        fun getName {fname_args, ...} =
          case fname_args of
            PrefixedFun {id, ...} => id
          | InfixedFun {id, ...} => id
          | CurriedInfixedFun {id, ...} => id

        fun checkFunc {elems, ...} =
          let
            val fname = getName (Seq.nth elems 0)
            fun checkName clause =
              if Token.same (getName clause, fname) then
                ()
              else
                error
                  { pos = Token.getSource (getName clause)
                  , what = "Function name does not match."
                  , explain = NONE
                  }
          in
            Seq.applyIdx (Seq.drop elems 1) (fn (_, elem) => checkName elem)
          end
      in
        Seq.applyIdx (#elems fvalbind) (fn (_, func) => checkFunc func)
      end


  end


  structure Str =
  struct
    open AstType.Str

    fun isMultipleDecs dec =
      case dec of
        DecMultiple {elems, ...} => Seq.length elems > 1
      | _ => false
  end

end
