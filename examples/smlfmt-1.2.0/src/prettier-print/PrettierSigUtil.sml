(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierSigUtil:
sig
  val leftMostSigExp: Ast.Sig.sigexp -> Ast.Sig.sigexp
  val specIsEmpty: Ast.Sig.spec -> bool
  val sigExpWantsSameTabAsDec: Ast.Sig.sigexp -> bool
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ====================================================================== *)

  fun leftMostSigExp e =
    let
      open Ast.Sig
    in
      case e of
        WhereType {sigexp, ...} => leftMostSigExp sigexp
      | _ => e
    end


  fun specIsEmpty spec =
    let
      open Ast.Sig
    in
      case spec of
        EmptySpec => true
      | _ => false
    end


  fun sigExpWantsSameTabAsDec e =
    let
      open Ast.Sig
    in
      case leftMostSigExp e of
        Ident _ => false
      | Spec {spec, ...} => not (specIsEmpty spec)
      | _ => true
    end

end
