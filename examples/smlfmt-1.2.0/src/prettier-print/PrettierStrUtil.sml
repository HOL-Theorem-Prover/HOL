(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierStrUtil:
sig
  val leftMostStrExp: Ast.Str.strexp -> Ast.Str.strexp
  val strExpWantsSameTabAsDec: Ast.Str.strexp -> bool
  val strExpInsideFunAppWantsSpaceBefore: Ast.Str.strexp -> bool
  val strDecInsideFunAppWantsSpaceBefore: Ast.Str.strdec -> bool
  val strDecIsEmpty: Ast.Str.strdec -> bool
  val showConstraintInStrDec:
    {colon: Token.t, sigexp: Ast.Sig.sigexp} PrettierUtil.shower
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  open PrettierSigUtil
  open PrettierSig
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ====================================================================== *)

  fun leftMostStrExp strexp =
    let
      open Ast.Str
    in
      case strexp of
        Constraint {strexp, ...} => leftMostStrExp strexp
      | _ => strexp
    end


  fun strExpWantsSameTabAsDec e =
    let
      open Ast.Str
    in
      case leftMostStrExp e of
        Struct _ => true
      | LetInEnd _ => true
      | _ => false
    end


  fun strExpInsideFunAppWantsSpaceBefore e =
    let
      open Ast.Str
    in
      case leftMostStrExp e of
        Struct _ => true
      | LetInEnd _ => true
      | _ => false
    end


  fun strDecInsideFunAppWantsSpaceBefore e =
    let
      open Ast.Str
    in
      case e of
        DecEmpty => false
      | DecCore _ => false
      | _ => true
    end


  fun strDecIsEmpty e =
    case e of
      Ast.Str.DecEmpty => true
    | _ => false


  fun showConstraintInStrDec tab {colon, sigexp} =
    (if
       Token.getClass colon = Token.Reserved Token.ColonArrow
       orelse Token.hasCommentsBefore colon
     then empty
     else nospace) ++ token colon ++ showSigExpInDec tab sigexp

end
