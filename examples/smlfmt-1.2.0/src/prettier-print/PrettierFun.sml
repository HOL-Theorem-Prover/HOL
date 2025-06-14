(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierFun:
sig
  val showFunDec: Ast.Fun.fundec PrettierUtil.shower
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  open PrettierSigUtil
  open PrettierSig
  open PrettierStrUtil
  open PrettierStr
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ======================================================================= *)

  fun funArgWantsSpaceBefore fa =
    case fa of
      Ast.Fun.ArgSpec _ => true
    | Ast.Fun.ArgIdent _ => false

  fun showFunArg tab fa =
    case fa of
      Ast.Fun.ArgSpec spec => withNewChild showSpec tab spec
    | Ast.Fun.ArgIdent {strid, colon, sigexp} =>
        newTab tab (fn tab =>
          (* NOTE: nospace before the colon should be safe here, because
           * structure identifiers cannot be symbolic *)
          at tab
            (token strid
             ++ (if Token.hasCommentsAfter strid then empty else nospace)
             ++ token colon ++ showSigExpInDec tab sigexp))

  fun showFunDec tab (Ast.Fun.DecFunctor {functorr, elems, delims}) =
    let
      fun showFunctor _
        (starter, {funid, lparen, funarg, rparen, constraint, eq, strexp}) =
        at tab
          (token starter ++ token funid
           ++ (if funArgWantsSpaceBefore funarg then space else nospace)
           ++
           newTab tab (fn inner =>
             at inner
               (token lparen ++ nospace ++ showFunArg inner funarg ++ nospace
                ++ token rparen))
           ++ showOption (showConstraintInStrDec tab) constraint ++ token eq
           ++
           (if strExpWantsSameTabAsDec strexp then
              at tab (showStrExp tab strexp)
            else
              withNewChild showStrExp tab strexp))
    in
      Seq.iterate op++ (showFunctor true (functorr, Seq.nth elems 0))
        (Seq.map (showFunctor false) (Seq.zip (delims, Seq.drop elems 1)))
    end

end
