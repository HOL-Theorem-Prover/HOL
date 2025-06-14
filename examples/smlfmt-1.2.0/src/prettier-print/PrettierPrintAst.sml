(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)
structure PrettierPrintAst:
sig
  val pretty:
    {ribbonFrac: real, maxWidth: int, tabWidth: int, indent: int, debug: bool}
    -> Ast.t
    -> TerminalColorString.t
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  open PrettierSig
  open PrettierStr
  open PrettierFun
  infix 2 ++
  fun x ++ y = concat (x, y)

  (* ====================================================================== *)

  fun showAst (Ast.Ast tds) =
    if Seq.length tds = 0 then
      empty
    else
      let
        fun showOneAt tab {topdec, semicolon} =
          let
            val td =
              case topdec of
                Ast.StrDec d => showStrDec tab d
              | Ast.SigDec d => showSigDec tab d
              | Ast.FunDec d => showFunDec tab d
              | Ast.TopExp {exp, semicolon} =>
                  PrettierExpAndDec.showExp tab exp ++ nospace
                  ++ token semicolon
            val sc =
              case semicolon of
                NONE => empty
              | SOME sc => nospace ++ token sc
          in
            td ++ sc
          end

        val all = Seq.map (showOneAt root) tds
      in
        Seq.iterate op++ (Seq.nth all 0) (Seq.map (at root) (Seq.drop all 1))
      end


  fun pretty {ribbonFrac, maxWidth, tabWidth, indent, debug} ast =
    let
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")
      val (doc, tm) = Util.getTime (fn _ => showAst ast)
      val _ = dbgprintln ("to-doc: " ^ Time.fmt 3 tm ^ "s")
    (* val doc = TokenDoc.insertComments doc
    val doc = TokenDoc.insertBlankLines doc *)
    in
      TabbedTokenDoc.pretty
        { ribbonFrac = ribbonFrac
        , maxWidth = maxWidth
        , indentWidth = indent
        , tabWidth = tabWidth
        , debug = debug
        } doc
    end

end
