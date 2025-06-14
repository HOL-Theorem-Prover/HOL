(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettyTy:
sig
  val showTy: Ast.Ty.t -> TokenDoc.t
end =
struct

  open TokenDoc
  open PrettyUtil

  infix 2 ++ $$ // +/+ +$+
  fun x ++ y = beside (x, y)
  fun x $$ y = aboveOrSpace (x, y)
  fun x // y = aboveOrBeside (x, y)

  fun x +/+ y = besideAndAbove (x, y)
  fun x +$+ y = besideAndAboveOrSpace (x, y)

  fun showTy ty =
    let
      open Ast.Ty
    in
      case ty of
        Var tok => token tok
      | Con {args = Ast.SyntaxSeq.Empty, id} =>
          token (MaybeLongToken.getToken id)
      | Con {args, id} =>
          (separateWithSpaces
             [ maybeShowSyntaxSeq args showTy
             , SOME (token (MaybeLongToken.getToken id))
             ])
      | Parens {left, ty, right} => token left ++ showTy ty ++ token right
      | Tuple {elems, delims} =>
          let
            val begin = showTy (Seq.nth elems 0)
            fun f (delim, x) =
              space ++ token delim ++ space ++ showTy x
          in
            Seq.iterate op++ begin (Seq.map f (Seq.zip
              (delims, Seq.drop elems 1)))
          end
      | Record {left, elems, delims, right} =>
          let
            fun showElem {lab, colon, ty} =
              token lab ++ space ++ token colon ++ space ++ showTy ty
          in
            sequence left delims right (Seq.map showElem elems)
          end
      | Arrow {from = left, arrow, to = right} =>
          let
            fun show_arrow l arrow r =
              case (r, right) of
                (Arrow {from = l', arrow = arrow', to = r'}, _) =>
                  showTy l
                  $$ ((spaces 2 ++ token arrow) +$+ show_arrow l' arrow' r')
              | (_, Arrow _) =>
                  showTy l $$ (spaces 2 ++ token arrow ++ space ++ showTy r)
              | _ => showTy l ++ space ++ token arrow ++ space ++ showTy r
          in
            group (show_arrow left arrow right)
          end
    end

end
