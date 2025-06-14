(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettyPat:
sig
  val showPat: Ast.Pat.t -> TokenDoc.t
end =
struct

  open TokenDoc
  open PrettyUtil

  infix 2 ++ $$ //
  fun x ++ y = beside (x, y)
  fun x $$ y = aboveOrSpace (x, y)
  fun x // y = aboveOrBeside (x, y)

  fun showTy ty = PrettyTy.showTy ty

  fun showPat pat =
    let
      open Ast.Pat
    in
      case pat of
        Wild tok => token tok
      | Const tok => token tok
      | Unit {left, right} => token left ++ token right
      | Ident {opp, id} =>
          separateWithSpaces
            [Option.map token opp, SOME (token (MaybeLongToken.getToken id))]
      | Parens {left, pat, right} => token left ++ showPat pat ++ token right
      | Tuple {left, elems, delims, right} =>
          sequence left delims right (Seq.map showPat elems)
      | List {left, elems, delims, right} =>
          sequence left delims right (Seq.map showPat elems)
      | Record {left, elems, delims, right} =>
          let
            fun showPatRow patrow =
              case patrow of
                DotDotDot ddd => token ddd
              | LabEqPat {lab, eq, pat} =>
                  token lab ++ space ++ token eq ++ space ++ showPat pat
              | LabAsPat {id, ty, aspat} =>
                  separateWithSpaces
                    [ SOME (token id)
                    , Option.map
                        (fn {colon, ty} => token colon ++ space ++ showTy ty) ty
                    , Option.map
                        (fn {ass, pat} => token ass ++ space ++ showPat pat)
                        aspat
                    ]
          in
            sequence left delims right (Seq.map showPatRow elems)
          end
      | Con {opp, id, atpat} =>
          separateWithSpaces
            [ Option.map token opp
            , SOME (token (MaybeLongToken.getToken id))
            , SOME (showPat atpat)
            ]
      | Typed {pat, colon, ty} =>
          showPat pat ++ space ++ token colon ++ space ++ showTy ty
      | Layered {opp, id, ty, ass, pat} =>
          separateWithSpaces
            [ Option.map token opp
            , SOME (token id)
            , Option.map (fn {colon, ty} => token colon ++ space ++ showTy ty)
                ty
            , SOME (token ass)
            , SOME (showPat pat)
            ]
      | Infix {left, id, right} =>
          showPat left ++ space ++ token id ++ space ++ showPat right

      | Or _ => recordPunFail ()
    end

end
