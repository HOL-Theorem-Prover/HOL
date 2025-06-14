(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierPat:
sig
  val showPat: Ast.Pat.t PrettierUtil.shower
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  open PrettierTy
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ====================================================================== *)

  fun patBeforeColonNeedsSpace pat =
    let
      open Ast.Pat
    in
      case pat of
        Wild _ => false
      | Const _ => false
      | Unit _ => false
      | Ident {id, ...} =>
          Token.isSymbolicIdentifier (MaybeLongToken.getToken id)
      | Parens _ => false
      | Tuple _ => false
      | List _ => false
      | Record _ => false
      | _ => true
    end

  (* ====================================================================== *)

  fun showPat tab pat =
    let
      open Ast.Pat
    in
      case pat of
        Wild tok => token tok

      | Const tok => token tok

      | Unit {left, right} => token left ++ nospace ++ token right

      | Ident {opp, id} => showMaybeOpToken opp (MaybeLongToken.getToken id)

      | Parens {left, pat, right} =>
          token left ++ (if patStartsWithStar pat then empty else nospace)
          ++ withNewChild showPat tab pat ++ nospace ++ token right

      | Tuple {left, elems, delims, right} =>
          showSequence patStartsWithStar (withNewChild showPat) tab
            {openn = left, elems = elems, delims = delims, close = right}

      | List {left, elems, delims, right} =>
          showSequence patStartsWithStar (withNewChild showPat) tab
            {openn = left, elems = elems, delims = delims, close = right}

      | Record {left, elems, delims, right} =>
          let
            fun showPatRow tab patrow =
              case patrow of
                DotDotDot ddd => token ddd
              | LabEqPat {lab, eq, pat} =>
                  newTab tab (fn inner =>
                    at inner
                      (token lab ++ token eq ++ withNewChild showPat inner pat))
              | LabAsPat {id, ty, aspat} =>
                  token id
                  ++
                  showOption
                    (fn {colon, ty} =>
                       (if
                          Token.isSymbolicIdentifier id
                          orelse Token.hasCommentsBefore colon
                        then empty
                        else nospace) ++ token colon
                       ++ withNewChild showTy tab ty) ty
                  ++
                  showOption
                    (fn {ass, pat} => token ass ++ withNewChild showPat tab pat)
                    aspat
          in
            showSequence (fn _ => false) (withNewChild showPatRow) tab
              {openn = left, elems = elems, delims = delims, close = right}
          end

      | Con {opp, id, atpat} =>
          showMaybeOpToken opp (MaybeLongToken.getToken id)
          ++ withNewChild showPat tab atpat

      | Typed {pat, colon, ty} =>
          showPat tab pat
          ++
          (if patBeforeColonNeedsSpace pat orelse Token.hasCommentsBefore colon then
             empty
           else
             nospace) ++ token colon ++ withNewChild showTy tab ty

      | Layered {opp, id, ty, ass, pat} =>
          showMaybeOpToken opp id
          ++
          showOption
            (fn {colon, ty} =>
               (if
                  Token.isSymbolicIdentifier id
                  orelse Token.hasCommentsBefore colon
                then empty
                else nospace) ++ token colon ++ withNewChild showTy tab ty) ty
          ++ token ass ++ withNewChild showPat tab pat

      | Infix {left, id, right} =>
          showPat tab left ++ token id ++ withNewChild showPat tab right

      | Or {elems, delims} =>
          newTab tab (fn tab =>
            let
              fun f (d, p) =
                at tab (token d) ++ withNewChild showPat tab p

              val front = at tab (showPat tab (Seq.nth elems 0))
            in
              Seq.iterate op++ front (Seq.zipWith f (delims, Seq.drop elems 1))
            end)
    end
end
