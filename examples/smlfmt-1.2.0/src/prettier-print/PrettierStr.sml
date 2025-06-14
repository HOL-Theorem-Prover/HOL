(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierStr:
sig
  val showStrExp: Ast.Str.strexp PrettierUtil.shower
  val showStrDec: Ast.Str.strdec PrettierUtil.shower
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  open PrettierTy
  open PrettierExpAndDec
  open PrettierSigUtil
  open PrettierSig
  open PrettierStrUtil
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ====================================================================== *)

  fun showStrExp tab e =
    let
      open Ast.Str
    in
      case e of
        Ident id => token (MaybeLongToken.getToken id)

      | Struct {structt, strdec, endd} =>
          if strDecIsEmpty strdec then
            token structt ++ at tab (token endd)
          else
            newTabWithStyle tab (indented, fn inner =>
              token structt ++ at inner (showStrDec inner strdec)
              ++
              cond inner {inactive = token endd, active = at tab (token endd)})

      | Constraint {strexp, colon, sigexp} =>
          showStrExp tab strexp ++ token colon
          ++ withNewChild showSigExp tab sigexp

      | FunAppExp {funid, lparen, strexp, rparen} =>
          (* The check for inserting a space after the `funid` is nice to
           * allow for both `F(G(X))` and `Fun (struct val x = 5 end)`.
           * (Personally, I like removing the space in the former case
           * and leaving the space in the second case, but this is certainly
           * open to debate.)
           *)
          newTab tab (fn inner =>
            token funid
            ++
            (if strExpInsideFunAppWantsSpaceBefore strexp then space
             else nospace)
            ++
            at inner
              (token lparen ++ nospace ++ withNewChild showStrExp inner strexp
               ++ nospace ++ token rparen))

      | FunAppDec {funid, lparen, strdec, rparen} => (* See note above, about the maybe-space after `funid` *)
          newTab tab (fn inner =>
            token funid
            ++
            (if strDecInsideFunAppWantsSpaceBefore strdec then space
             else nospace)
            ++
            at inner
              (token lparen ++ nospace ++ withNewChild showStrDec inner strdec
               ++ nospace ++ token rparen))

      | LetInEnd {lett, strdec, inn, strexp, endd} =>
          showThingSimilarToLetInEnd tab
            { lett = lett
            , isEmpty1 = strDecIsEmpty strdec
            , doc1 = withNewChildWithStyle indented showStrDec tab strdec
            , inn = inn
            , doc2 = withNewChildWithStyle indented showStrExp tab strexp
            , endd = endd
            }
    end


  and showStrDec tab d =
    let
      open Ast.Str
    in
      case d of
        DecEmpty => empty

      | DecCore d => showDec tab d

      | DecStructure {structuree, elems, delims} =>
          newTab tab (fn tab =>
            let
              fun showConstraint constraint =
                case constraint of
                  NONE => empty
                | SOME {colon, sigexp} =>
                    showConstraintInStrDec tab {colon = colon, sigexp = sigexp}

              fun showOne (starter, {strid, constraint, eq, strexp}) =
                token starter ++ token strid ++ showConstraint constraint
                ++ token eq
                ++
                (if strExpWantsSameTabAsDec strexp then
                   at tab (showStrExp tab strexp)
                 else
                   withNewChild showStrExp tab strexp)
            in
              at tab
                (Seq.iterate op++ (showOne (structuree, Seq.nth elems 0))
                   (Seq.map (fn x => at tab (showOne x)) (Seq.zip
                      (delims, (Seq.drop elems 1)))))
            end)


      | DecMultiple {elems, delims} =>
          let
            fun mk first (elem, delim) =
              at tab
                (showStrDec tab elem
                 ++ showOption (fn d => nospace ++ token d) delim)

            val things = Seq.zip (elems, delims)
          in
            Seq.iterate op++ (mk true (Seq.nth things 0)) (Seq.map (mk false)
              (Seq.drop things 1))
          end

      | DecLocalInEnd {locall, strdec1, inn, strdec2, endd} =>
          showThingSimilarToLetInEnd tab
            { lett = locall
            , isEmpty1 = strDecIsEmpty strdec1
            , doc1 = withNewChildWithStyle indented showStrDec tab strdec1
            , inn = inn
            , doc2 = withNewChildWithStyle indented showStrDec tab strdec2
            , endd = endd
            }

      (** This is MLton-specific. Useful for testing by parsing the entire
        * MLton implementation of the standard basis.
        *)
      | MLtonOverload
          {underscore, overload, prec, name, colon, ty, ass, elems, delims} =>
          newTab tab (fn inner =>
            let
              val front =
                at inner
                  (token underscore ++ nospace ++ token overload ++ token prec
                   ++ token name ++ token colon) ++ withNewChild showTy inner ty
                ++
                at inner
                  (token ass
                   ++ token (MaybeLongToken.getToken (Seq.nth elems 0)))

              fun showOne (d, e) =
                at inner (token d ++ token (MaybeLongToken.getToken e))
            in
              Seq.iterate op++ front (Seq.zipWith showOne
                (delims, Seq.drop elems 1))
            end) (* | _ => text "<strdec>" *)
    end

end
