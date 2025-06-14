(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettyStr:
sig
  val showStrExp: Ast.Str.strexp -> TokenDoc.t
  val showStrDec: Ast.Str.strdec -> TokenDoc.t
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

  fun showStrExp e =
    case e of
      Ast.Str.Ident id => token (MaybeLongToken.getToken id)

    | Ast.Str.Struct {structt, strdec, endd} =>
        (case strdec of
           Ast.Str.DecEmpty => token structt ++ space ++ token endd
         | _ =>
             rigid (token structt $$ indent (showStrDec strdec) $$ token endd))

    | Ast.Str.Constraint {strexp, colon, sigexp} =>
        showStrExp strexp ++ space ++ token colon \\ showSigExp sigexp

    | Ast.Str.FunAppExp {funid, lparen, strexp, rparen} =>
        token funid \\ token lparen ++ showStrExp strexp ++ token rparen

    | Ast.Str.FunAppDec {funid, lparen, strdec, rparen} =>
        token funid \\ token lparen ++ showStrDec strdec ++ token rparen

    | Ast.Str.LetInEnd {lett, strdec, inn, strexp, endd} =>
        let
          val topPart = token lett $$ indent (showStrDec strdec) $$ token inn

          val topPart =
            if Ast.Str.isMultipleDecs strdec then topPart else group topPart
        in
          group (topPart $$ indent (group (showStrExp strexp)) $$ token endd)
        end


  and showStrDec d =
    case d of
      Ast.Str.DecEmpty => empty

    | Ast.Str.DecCore d => showDec d

    | Ast.Str.DecStructure {structuree, elems, delims} =>
        let
          fun showOne (starter, {strid, constraint, eq, strexp}) =
            separateWithSpaces
              [ SOME (token starter)
              , SOME (token strid)
              , Option.map (fn {colon, sigexp} => token colon) constraint
              ]
            \\
            separateWithSpaces
              [ Option.map (fn {colon, sigexp} => showSigExp sigexp) constraint
              , SOME (token eq)
              ] \\ showStrExp strexp
        in
          rigidVertically (showOne (structuree, Seq.nth elems 0))
            (Seq.map showOne (Seq.zip (delims, (Seq.drop elems 1))))
        end

    | Ast.Str.DecMultiple {elems, delims} =>
        let
          fun f i =
            showStrDec (Seq.nth elems i)
            ++
            (case Seq.nth delims i of
               NONE => empty
             | SOME sc => token sc)
        in
          rigid (Util.loop (0, Seq.length elems) empty (fn (prev, i) =>
            prev $$ f i))
        end

    | Ast.Str.DecLocalInEnd {locall, strdec1, inn, strdec2, endd} =>
        rigid
          (token locall $$ indent (showStrDec strdec1) $$ token inn
           $$ indent (showStrDec strdec2) $$ token endd)

    (** This is MLton-specific. Useful for testing by parsing the entire
      * MLton implementation of the standard basis.
      *)
    | Ast.Str.MLtonOverload
        {underscore, overload, prec, name, colon, ty, ass, elems, delims} =>
        let
          val front =
            token underscore ++ token overload ++ space ++ token prec ++ space
            ++ token name ++ space ++ token colon ++ space ++ showTy ty ++ space
            ++ token ass

          fun showOne (d, e) =
            token d ++ space ++ token (MaybeLongToken.getToken e)
        in
          group
            (front
             $$
             indent
               (rigidVertically
                  (token (MaybeLongToken.getToken (Seq.nth elems 0)))
                  (Seq.zipWith showOne (delims, Seq.drop elems 1))))
        end

end
