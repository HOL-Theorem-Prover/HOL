(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierTy:
sig
  val showTy: Ast.Ty.t PrettierUtil.shower
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  infix 2 ++
  fun x ++ y = concat (x, y)

  fun showTy tab ty : doc =
    let
      open Ast.Ty
    in
      case ty of
        Var tok => token tok

      | Con {args = Ast.SyntaxSeq.Empty, id} =>
          token (MaybeLongToken.getToken id)

      | Con {args, id} =>
          showSyntaxSeq (withNewChild showTy) tab args
          ++ token (MaybeLongToken.getToken id)

      | Parens {left, ty, right} =>
          token left ++ nospace ++ withNewChild showTy tab ty ++ nospace
          ++ token right

      | Tuple {elems, delims} =>
          newTab tab (fn tab =>
            let
              fun f (delim, x) =
                at tab (token delim ++ withNewChild showTy tab x)
            in
              Seq.iterate op++
                (at tab (withNewChild showTy tab (Seq.nth elems 0)))
                (Seq.zipWith f (delims, Seq.drop elems 1))
            end)

      | Record {left, elems, delims, right} =>
          let
            fun showElem tab {lab, colon, ty} =
              token lab
              ++
              (if
                 Token.isSymbolicIdentifier lab
                 orelse Token.hasCommentsAfter lab
               then empty
               else nospace) ++ token colon ++ showTy tab ty
          in
            showSequence (fn _ => false) (withNewChild showElem) tab
              {openn = left, elems = elems, delims = delims, close = right}
          end

      | Arrow {from, arrow, to} =>
          let
            fun loop (arr, right) =
              at tab
                (token arr
                 ++
                 (case right of
                    Arrow {from, arrow, to} =>
                      withNewChild showTy tab from ++ loop (arrow, to)
                  | _ => withNewChild showTy tab right))
          in
            withNewChild showTy tab from ++ loop (arrow, to)
          end
    end

end
