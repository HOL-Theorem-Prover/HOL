(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettyPrintAst:
sig
  val pretty:
    {ribbonFrac: real, maxWidth: int, tabWidth: int, indent: int, debug: bool}
    -> Ast.t
    -> TerminalColorString.t
end =
struct

  structure Doc = TokenDoc
  open Doc
  open PrettyUtil

  infix 2 ++ $$ //
  fun x ++ y = beside (x, y)
  fun x $$ y = aboveOrSpace (x, y)
  fun x // y = aboveOrBeside (x, y)

  fun showTy ty = PrettyTy.showTy ty
  fun showPat pat = PrettyPat.showPat pat
  fun showExp exp = PrettyExpAndDec.showExp exp
  fun showDec dec = PrettyExpAndDec.showDec dec
  fun showSpec spec = PrettySig.showSpec spec
  fun showSigExp sigexp = PrettySig.showSigExp sigexp
  fun showSigDec sigdec = PrettySig.showSigDec sigdec
  fun showStrExp strexp = PrettyStr.showStrExp strexp
  fun showStrDec strdec = PrettyStr.showStrDec strdec
  fun showFunDec fundec = PrettyFun.showFunDec fundec


  fun showAst (Ast.Ast tds) =
    if Seq.length tds = 0 then
      empty
    else
      let
        fun showOne {topdec, semicolon} =
          let
            val td =
              case topdec of
                Ast.StrDec d => showStrDec d
              | Ast.SigDec d => showSigDec d
              | Ast.FunDec d => showFunDec d
              | Ast.TopExp _ =>
                  raise Fail
                    "unsupported: top-level expressions. Note: you are \
                    \using `-engine pretty`, which is headed towards \
                    \deprecation. Please use `-engine prettier` instead, \
                    \which supports top-level expressions."
            val sc =
              case semicolon of
                NONE => empty
              | SOME sc => token sc
          in
            td ++ sc
          end

        val all = Seq.map showOne tds
      in
        Seq.iterate op$$ (Seq.nth all 0) (Seq.drop all 1)
      end


  fun pretty {ribbonFrac, maxWidth, tabWidth, indent, debug} ast =
    let
      val doc = showAst ast
      val doc = TokenDoc.insertComments doc
      val doc = TokenDoc.insertBlankLines doc
    in
      StringDoc.pretty
        {ribbonFrac = ribbonFrac, maxWidth = maxWidth, indentWidth = indent}
        (toStringDoc {tabWidth = tabWidth} doc)
    end

end
