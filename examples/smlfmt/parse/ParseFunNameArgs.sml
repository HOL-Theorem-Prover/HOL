(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParseFunNameArgs:
sig
  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = Token.t Seq.t

  val fname_args: ParserContext.t
                  -> tokens
                  -> InfixDict.t
                  -> (int, Ast.Exp.fname_args) parser
end =
struct
  local open ParseSimple ParseTy ParsePat ExpPatRestriction in end

  structure PC = ParserCombinators
  structure PS = ParseSimple
  structure PT = ParseTy
  structure PP = ParsePat

  structure Restriction = ExpPatRestriction

  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = Token.t Seq.t


  fun fname_args ctx toks infdict i =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun check f i =
        i < numToks andalso f (tok i)
      fun isReserved rc i =
        check (fn t => Token.Reserved rc = Token.getClass t) i

      fun isInfixedValueIdentifierNoEqual i =
        check Token.isValueIdentifierNoEqual i
        andalso InfixDict.isInfix infdict (tok i)

      fun restOfCurriedArgs i =
        let
          fun continue i =
            not (isReserved Token.Colon i orelse isReserved Token.Equal i)
        in
          PC.zeroOrMoreWhile continue
            (PP.pat ctx toks infdict Restriction.At) i
        end


      fun curriedInfix lparen larg id rarg rparen i =
        let
          (* val _ = print ("curriedInfix\n") *)
          val (i, args) = restOfCurriedArgs i
        in
          ( i
          , Ast.Exp.CurriedInfixedFun
              { lparen = lparen
              , larg = larg
              , id = id
              , rarg = rarg
              , rparen = rparen
              , args = args
              }
          )
        end


      fun prefixedFun opp id i =
        let
          (* val _ = print ("prefixedFun\n") *)
          val (i, args) = restOfCurriedArgs i
        in
          (i, Ast.Exp.PrefixedFun {opp = opp, id = id, args = args})
        end


      fun infixedFun larg id i =
        let
          (* val _ = print ("infixedFun\n") *)
          val (i, rarg) = PP.pat ctx toks infdict Restriction.At i
        in
          (i, Ast.Exp.InfixedFun {larg = larg, id = id, rarg = rarg})
        end


      val (i, firstPat) = PP.pat ctx toks infdict Restriction.At i

      fun err () =
        ParserUtils.error
          { pos = Token.getSource (Ast.Pat.leftMostToken firstPat)
          , what = "Invalid function definition."
          , explain = SOME "Could not find name of function."
          }
    in
      if isInfixedValueIdentifierNoEqual i then
        infixedFun firstPat (tok i) (i + 1)
      else
        case firstPat of
          Ast.Pat.Parens
            {left = lp, right = rp, pat = Ast.Pat.Infix {left, id, right}} =>
            curriedInfix lp left id right rp i

        | Ast.Pat.Ident {opp, id} =>
            if not (MaybeLongToken.isLong id) then
              prefixedFun opp (MaybeLongToken.getToken id) i
            else
              err ()

        | _ => err ()
    end

end
