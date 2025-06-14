(** Copyright (c) 2022-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierSig:
sig
  val showSpec: Ast.Sig.spec PrettierUtil.shower
  val showSigExp: Ast.Sig.sigexp PrettierUtil.shower
  val showSigExpInDec: Ast.Sig.sigexp PrettierUtil.shower
  val showSigDec: Ast.Sig.sigdec PrettierUtil.shower
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  open PrettierTy
  open PrettierSigUtil
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ======================================================================= *)

  (* This function is duplicated in PrettierExpAndDec. *)
  fun showTypbind tab (front, {elems, delims}) =
    let
      fun showOne _ (starter, {tyvars, tycon, ty, eq}) =
        at tab
          (token starter ++ showTokenSyntaxSeq tab tyvars ++ token tycon
           ++ token eq ++ withNewChild showTy tab ty)
    in
      Seq.iterate op++ (showOne true (front, Seq.nth elems 0))
        (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
    end


  (* NOTE: very similar to PrettierExpAndDec.showDatbind. The
   * only difference: there is no possible 'op' in the condesc, ugh.
   *)
  fun showDatspec tab (datatypee, elems, delims) =
    newTabWithStyle tab (Tab.Style.allowComments, fn tab =>
      let
        fun showCon (starter, {vid, arg}) =
          at tab
            (starter ++ token vid
             ++
             showOption
               (fn {off, ty} =>
                  token off
                  ++ withNewChildWithStyle (indentedAtLeastBy 4) showTy tab ty)
               arg)

        fun showOne (starter, {tyvars, tycon, eq, elems, delims, optbar}) =
          let
            val initial = at tab
              (token starter ++ showTokenSyntaxSeq tab tyvars ++ token tycon
               ++ token eq)

            val skipper = cond tab {inactive = empty, active = space ++ space}
            fun dd delim = token delim ++ space

            val firstConFront =
              case optbar of
                NONE => skipper
              | SOME bar => dd bar
          in
            initial
            ++
            Seq.iterate op++ (showCon (firstConFront, Seq.nth elems 0))
              (Seq.zipWith showCon (Seq.map dd delims, Seq.drop elems 1))
          end
      in
        Seq.iterate op++ (showOne (datatypee, Seq.nth elems 0))
          (Seq.zipWith showOne (delims, Seq.drop elems 1))
      end)

  (* ======================================================================= *)


  fun showSpec tab spec =
    let
      open Ast.Sig
    in
      case spec of
        EmptySpec => empty

      | Val {vall, elems, delims} =>
          let
            fun showOne _ (starter, {vid, colon, ty}) =
              at tab
                (token starter ++ token vid
                 ++
                 (if
                    Token.isSymbolicIdentifier vid
                    orelse Token.hasCommentsAfter vid
                  then empty
                  else nospace) ++ token colon ++ withNewChild showTy tab ty)
          in
            Seq.iterate op++ (showOne true (vall, Seq.nth elems 0))
              (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
          end

      | Type {typee, elems, delims} =>
          let
            fun showOne first (starter, {tyvars, tycon}) =
              at tab
                (token starter ++ showTokenSyntaxSeq tab tyvars ++ token tycon)
          in
            Seq.iterate op++ (showOne true (typee, Seq.nth elems 0))
              (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
          end

      | TypeAbbreviation {typee, typbind} => showTypbind tab (typee, typbind)

      | Eqtype {eqtypee, elems, delims} =>
          let
            fun showOne _ (starter, {tyvars, tycon}) =
              at tab
                (token starter ++ showTokenSyntaxSeq tab tyvars ++ token tycon)
          in
            Seq.iterate op++ (showOne true (eqtypee, Seq.nth elems 0))
              (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
          end

      | Multiple {elems, delims} =>
          let
            fun showOne _ (elem: spec, delim: Token.t option) =
              at tab
                (showSpec tab elem
                 ++ showOption (fn d => nospace ++ token d) delim)

            val things = Seq.zip (elems, delims)
          in
            Seq.iterate op++ (showOne true (Seq.nth things 0))
              (Seq.map (showOne false) (Seq.drop things 1))
          end

      | Exception {exceptionn, elems, delims} =>
          let
            fun showOne _ (starter, {vid, arg}) =
              at tab
                (token starter ++ token vid
                 ++
                 showOption
                   (fn {off, ty} => token off ++ withNewChild showTy tab ty) arg)
          in
            Seq.iterate op++ (showOne true (exceptionn, Seq.nth elems 0))
              (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
          end

      | Structure {structuree, elems, delims} =>
          let
            fun showOne _ (starter, {id, colon, sigexp}) =
              at tab
                (token starter ++ token id
                 (* NOTE: nospace should be safe here, because structure
                 * identifiers cannot be symbolic *)
                 ++ (if Token.hasCommentsAfter id then empty else nospace)
                 ++ token colon) ++ showSigExpInDec tab sigexp
          in
            Seq.iterate op++ (showOne true (structuree, Seq.nth elems 0))
              (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
          end

      | Include {includee, sigexp} =>
          token includee ++ withNewChild showSigExp tab sigexp

      | IncludeIds {includee, sigids} =>
          Seq.iterate op++ (token includee)
            (Seq.map (withNewChild (fn _ => token) tab) sigids)

      | Sharing {spec, sharingg, elems, delims} =>
          newTab tab (fn inner =>
            let
              fun showOne (delim, elem) =
                at inner
                  (token delim (** this is an '=' *)
                   ++ token (MaybeLongToken.getToken elem))

              val first = at inner (token (MaybeLongToken.getToken
                (Seq.nth elems 0)))

              val stuff = Seq.iterate op++ first (Seq.zipWith showOne
                (delims, Seq.drop elems 1))
            in
              showSpec tab spec ++ at tab (token sharingg ++ stuff)
            end)

      | SharingType {spec, sharingg, typee, elems, delims} =>
          newTab tab (fn inner =>
            let
              fun showOne (delim, elem) =
                at inner
                  (token delim (** this is an '=' *)
                   ++ token (MaybeLongToken.getToken elem))

              val first = at inner (token (MaybeLongToken.getToken
                (Seq.nth elems 0)))

              val stuff = Seq.iterate op++ first (Seq.zipWith showOne
                (delims, Seq.drop elems 1))
            in
              showSpec tab spec
              ++ at tab (token sharingg ++ token typee ++ stuff)
            end)

      | ReplicateDatatype
          {left_datatypee, left_id, eq, right_datatypee, right_id} =>
          token left_datatypee ++ token left_id ++ token eq
          ++
          newTab tab (fn inner =>
            at inner
              (token right_datatypee ++ token (MaybeLongToken.getToken right_id)))

      | Datatype {datatypee, elems, delims, withtypee} =>
          showDatspec tab (datatypee, elems, delims)
          ++
          showOption
            (fn {withtypee, typbind} =>
               at tab (showTypbind tab (withtypee, typbind))) withtypee
    end


  and showSigExp tab sigexp =
    let
      open Ast.Sig
    in
      case sigexp of
        Ident id => token id

      | Spec {sigg, spec, endd} =>
          newTabWithStyle tab (indented, fn inner =>
            at tab (token sigg) ++ at inner (showSpec inner spec)
            ++ cond inner {inactive = token endd, active = at tab (token endd)})

      | WhereType {sigexp, elems} =>
          let
            fun showElem {wheree, typee, tyvars, tycon, eq, ty} =
              at tab
                (token wheree (** this could be 'and' *) ++ token typee
                 ++ showTokenSyntaxSeq tab tyvars
                 ++ token (MaybeLongToken.getToken tycon) ++ token eq
                 ++ withNewChild showTy tab ty)
          in
            Seq.iterate op++ (showSigExp tab sigexp) (Seq.map showElem elems)
          end
    end


  and showSigExpInDec tab sigexp =
    if not (sigExpWantsSameTabAsDec sigexp) then
      withNewChild showSigExp tab sigexp
    else
      let
        open Ast.Sig
        val style = Tab.Style.combine (Tab.Style.rigid, Tab.Style.indented)
      in
        case sigexp of
          Spec {sigg, spec, endd} =>
            newTabWithStyle tab (style, fn inner =>
              at tab (token sigg) ++ at inner (showSpec inner spec)
              ++
              cond inner {inactive = token endd, active = at tab (token endd)})

        | _ => at tab (showSigExp tab sigexp)
      end


  and showSigDec tab (Ast.Sig.Signature {signaturee, elems, delims}) =
    let
      fun showOne _ (starter, {ident, eq, sigexp}) =
        at tab (token starter ++ token ident ++ token eq)
        ++ showSigExpInDec tab sigexp
    in
      Seq.iterate op++ (showOne true (signaturee, Seq.nth elems 0))
        (Seq.zipWith (showOne false) (delims, Seq.drop elems 1))
    end

end
