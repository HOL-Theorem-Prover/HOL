(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettySig:
sig
  val showSpec: Ast.Sig.spec -> TokenDoc.t
  val showSigExp: Ast.Sig.sigexp -> TokenDoc.t
  val showSigDec: Ast.Sig.sigdec -> TokenDoc.t
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

  fun showSpec spec =
    case spec of
      Ast.Sig.EmptySpec => empty

    | Ast.Sig.Val {vall, elems, delims} =>
        let
          fun showOne (starter, {vid, colon, ty}) =
            token starter ++ space ++ token vid ++ space ++ token colon ++ space
            ++ showTy ty
        in
          rigidVertically (showOne (vall, Seq.nth elems 0)) (Seq.zipWith showOne
            (delims, Seq.drop elems 1))
        end

    | Ast.Sig.Type {typee, elems, delims} =>
        let
          fun showOne (starter, {tyvars, tycon}) =
            separateWithSpaces
              [ SOME (token starter)
              , maybeShowSyntaxSeq tyvars token
              , SOME (token tycon)
              ]
        in
          rigidVertically (showOne (typee, Seq.nth elems 0))
            (Seq.zipWith showOne (delims, Seq.drop elems 1))
        end

    | Ast.Sig.TypeAbbreviation {typee, typbind = {elems, delims}} =>
        let
          fun showOne (starter, {tyvars, tycon, eq, ty}) =
            separateWithSpaces
              [ SOME (token starter)
              , maybeShowSyntaxSeq tyvars token
              , SOME (token tycon)
              , SOME (token eq)
              , SOME (showTy ty)
              ]
        in
          rigidVertically (showOne (typee, Seq.nth elems 0))
            (Seq.zipWith showOne (delims, Seq.drop elems 1))
        end

    | Ast.Sig.Eqtype {eqtypee, elems, delims} =>
        let
          fun showOne (starter, {tyvars, tycon}) =
            separateWithSpaces
              [ SOME (token starter)
              , maybeShowSyntaxSeq tyvars token
              , SOME (token tycon)
              ]
        in
          rigidVertically (showOne (eqtypee, Seq.nth elems 0))
            (Seq.zipWith showOne (delims, Seq.drop elems 1))
        end

    | Ast.Sig.Datatype {datatypee, elems, delims, withtypee} =>
        (** This is *really* similar to a datbind (see showDatbind above), but
          * only one difference: there is no possible 'op' in the condesc, ugh.
          *)
        let
          val _ = if Option.isSome withtypee then sigWithtypeFail () else ()

          fun showCon (starter, {vid, arg}) =
            starter ++ space
            ++
            group (separateWithSpaces
              [ SOME (token vid)
              , Option.map (fn {off, ty} => token off $$ indent (showTy ty)) arg
              ])

          fun show_datdesc (starter, {tyvars, tycon, eq, elems, delims, optbar}) =
            let
              val _ = if Option.isSome optbar then optBarFail () else ()

              val initial = group (separateWithSpaces
                [ SOME (token starter)
                , maybeShowSyntaxSeq tyvars token
                , SOME (token tycon)
                , SOME (token eq)
                ])
            in
              group
                (initial
                 $$
                 group
                   (Seq.iterate op$$ (showCon (space, Seq.nth elems 0))
                      (Seq.zipWith showCon
                         (Seq.map token delims, Seq.drop elems 1))))
            end
        in
          rigidVertically (show_datdesc (datatypee, Seq.nth elems 0))
            (Seq.zipWith show_datdesc (delims, Seq.drop elems 1))
        end

    | Ast.Sig.ReplicateDatatype
        {left_datatypee, left_id, eq, right_datatypee, right_id} =>
        group
          (separateWithSpaces
             [ SOME (token left_datatypee)
             , SOME (token left_id)
             , SOME (token eq)
             ]
           $$
           indent
             (token right_datatypee ++ space
              ++ token (MaybeLongToken.getToken right_id)))

    | Ast.Sig.Exception {exceptionn, elems, delims} =>
        let
          fun showOne (starter, {vid, arg}) =
            group (separateWithSpaces
              [ SOME (token starter)
              , SOME (token vid)
              , Option.map (fn {off, ty} => token off ++ space ++ showTy ty) arg
              ])
        in
          rigidVertically (showOne (exceptionn, Seq.nth elems 0))
            (Seq.zipWith showOne (delims, Seq.drop elems 1))
        end

    | Ast.Sig.Structure {structuree, elems, delims} =>
        let
          fun showOne (starter, {id, colon, sigexp}) =
            group
              (separateWithSpaces
                 [SOME (token starter), SOME (token id), SOME (token colon)]
               $$ indent (showSigExp sigexp))
        in
          rigidVertically (showOne (structuree, Seq.nth elems 0))
            (Seq.zipWith showOne (delims, Seq.drop elems 1))
        end

    | Ast.Sig.Include {includee, sigexp} =>
        group (token includee $$ indent (showSigExp sigexp))

    | Ast.Sig.IncludeIds {includee, sigids} =>
        Seq.iterate (fn (a, b) => a ++ space ++ token b) (token includee) sigids

    | Ast.Sig.Multiple {elems, delims} =>
        let
          fun showOne (elem: Ast.Sig.spec, delim: Token.t option) =
            showSpec elem
            ++
            (case delim of
               NONE => empty
             | SOME sc => token sc)
        in
          rigid (Seq.iterate op$$ empty (Seq.zipWith showOne (elems, delims)))
        end

    | Ast.Sig.Sharing {spec, sharingg, elems, delims} =>
        let
          fun showOne (delim, elem) =
            token delim (** this is an '=' *) ++ space
            ++ token (MaybeLongToken.getToken elem)

          val stuff =
            Seq.iterate (fn (a, b) => a ++ space ++ b)
              (token (MaybeLongToken.getToken (Seq.nth elems 0)))
              (Seq.zipWith showOne (delims, Seq.drop elems 1))
        in
          group (showSpec spec $$ rigid (token sharingg ++ space ++ stuff))
        end

    | Ast.Sig.SharingType {spec, sharingg, typee, elems, delims} =>
        let
          fun showOne (delim, elem) =
            token delim (** this is an '=' *) ++ space
            ++ token (MaybeLongToken.getToken elem)

          val stuff =
            Seq.iterate (fn (a, b) => a ++ space ++ b)
              (token (MaybeLongToken.getToken (Seq.nth elems 0)))
              (Seq.zipWith showOne (delims, Seq.drop elems 1))
        in
          group
            (showSpec spec
             $$ rigid (token sharingg ++ space ++ token typee ++ space ++ stuff))
        end


  and showSigExp sigexp =
    case sigexp of
      Ast.Sig.Ident id => token id

    | Ast.Sig.Spec {sigg, spec, endd} =>
        group (token sigg $$ indent (showSpec spec) $$ token endd)

    | Ast.Sig.WhereType {sigexp, elems} =>
        let
          val se = showSigExp sigexp

          fun showElem {wheree, typee, tyvars, tycon, eq, ty} =
            indent (separateWithSpaces
              [ SOME (token wheree) (** this could be 'and' *)
              , SOME (token typee)
              , maybeShowSyntaxSeq tyvars token
              , SOME (token (MaybeLongToken.getToken tycon))
              , SOME (token eq)
              , SOME (showTy ty)
              ])
        in
          Seq.iterate op$$ se (Seq.map showElem elems)
        end


  fun showSigDec (Ast.Sig.Signature {signaturee, elems, delims}) =
    let
      fun showOne (starter, {ident, eq, sigexp}) =
        group
          ((token starter ++ space ++ token ident ++ space ++ token eq)
           $$ indent (showSigExp sigexp))
    in
      rigidVertically (showOne (signaturee, Seq.nth elems 0))
        (Seq.zipWith showOne (delims, Seq.drop elems 1))
    end

end
