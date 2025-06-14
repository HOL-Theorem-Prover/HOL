(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettyFun:
sig
  val showFunDec: Ast.Fun.fundec -> TokenDoc.t
end =
struct

  open TokenDoc
  open PrettyUtil

  infix 2 ++ $$ //
  infix 1 \\

  fun showTy ty = PrettyTy.showTy ty
  fun showPat pat = PrettyPat.showPat pat
  fun showExp exp = PrettyExpAndDec.showExp exp
  fun showDec dec = PrettyExpAndDec.showDec dec
  fun showSpec spec = PrettySig.showSpec spec
  fun showSigExp sigexp = PrettySig.showSigExp sigexp
  fun showSigDec sigdec = PrettySig.showSigDec sigdec
  fun showStrExp strexp = PrettyStr.showStrExp strexp
  fun showStrDec strdec = PrettyStr.showStrDec strdec

  fun showFunArg fa =
    case fa of
      Ast.Fun.ArgSpec spec => showSpec spec
    | Ast.Fun.ArgIdent {strid, colon, sigexp} =>
        group
          (token strid ++ space ++ token colon ++ space ++ showSigExp sigexp)

  fun showFunDec (Ast.Fun.DecFunctor {functorr, elems, delims}) =
    let
      fun showFunctor
        (starter, {funid, lparen, funarg, rparen, constraint, eq, strexp}) =
        separateWithSpaces [SOME (token starter), SOME (token funid)]
        \\
        separateWithSpaces
          [ SOME (token lparen ++ showFunArg funarg ++ token rparen)
          , Option.map (fn {colon, sigexp} => token colon) constraint
          ]
        \\
        separateWithSpaces
          [ Option.map (fn {colon, sigexp} => showSigExp sigexp) constraint
          , SOME (token eq)
          ] \\ showStrExp strexp
    in
      rigidVertically (showFunctor (functorr, Seq.nth elems 0))
        (Seq.map showFunctor (Seq.zip (delims, Seq.drop elems 1)))
    end

end
