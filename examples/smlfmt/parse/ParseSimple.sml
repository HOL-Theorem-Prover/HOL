(** Copyright (c) 2020-2021 Sam Westrick
  * See the file LICENSE for details.
  *
  * This structure implements a lot of the "simple" parser functions, to
  * avoid cluttering the main Parser implementation.
  *)

structure ParseSimple:
sig
  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type 'a peeker = 'a ParserCombinators.peeker

  type tokens = Token.t Seq.t

  val reserved: tokens -> Token.reserved -> (int, Token.t) parser
  val maybeReserved: tokens -> Token.reserved -> (int, Token.t option) parser
  val tyvar: tokens -> (int, Token.t) parser
  val tyvars: tokens -> (int, Token.t Ast.SyntaxSeq.t) parser
  val sigid: tokens -> (int, Token.t) parser
  val strid: tokens -> (int, Token.t) parser
  val funid: tokens -> (int, Token.t) parser
  val vid: tokens -> (int, Token.t) parser
  val longvid: tokens -> (int, MaybeLongToken.t) parser
  val recordLabel: tokens -> (int, Token.t) parser
  val tycon: tokens -> (int, Token.t) parser
  val maybeLongTycon: tokens -> (int, MaybeLongToken.t) parser
  val maybeLongStrid: tokens -> (int, MaybeLongToken.t) parser
end =
struct

  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type 'a peeker = 'a ParserCombinators.peeker
  type tokens = Token.t Seq.t


  fun check toks f i =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
    in
      i < numToks andalso f (tok i)
    end


  fun isReserved toks rc i =
    check toks (fn t => Token.Reserved rc = Token.getClass t) i


  fun reserved toks rc i =
    if isReserved toks rc i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        { pos = i
        , what =
            "Unexpected token. Expected to see " ^ "'"
            ^ Token.reservedToString rc ^ "'"
        , explain = NONE
        }


  fun maybeReserved toks rc i =
    if isReserved toks rc i then (i + 1, SOME (Seq.nth toks i)) else (i, NONE)


  fun tyvar toks i =
    if check toks Token.isTyVar i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        {pos = i, what = "Expected tyvar.", explain = NONE}


  fun strid toks i =
    if check toks Token.isStrIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        { pos = i
        , what = "Expected structure identifier."
        , explain = SOME
            "Must be alphanumeric, and cannot start with a\
            \ prime (')"
        }


  fun sigid toks i =
    if check toks Token.isStrIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        { pos = i
        , what = "Expected signature identifier."
        , explain = SOME
            "Must be alphanumeric, and cannot start with a\
            \ prime (')"
        }


  fun funid toks i =
    if check toks Token.isStrIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        { pos = i
        , what = "Expected functor identifier."
        , explain = SOME
            "Must be alphanumeric, and cannot start with a\
            \ prime (')"
        }


  fun vid toks i =
    if check toks Token.isValueIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        { pos = i
        , what = "Unexpected token. Expected value identifier."
        , explain = NONE
        }


  fun longvid toks i =
    if check toks Token.isMaybeLongIdentifier i then
      (i + 1, MaybeLongToken.make (Seq.nth toks i))
    else
      ParserUtils.tokError toks
        { pos = i
        , what = "Expected (possibly long) value identifier."
        , explain = NONE
        }

  fun recordLabel toks i =
    if check toks Token.isRecordLabel i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        {pos = i, what = "Expected record label.", explain = NONE}


  fun tycon toks i =
    if check toks Token.isTyCon i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.tokError toks
        { pos = i
        , what = "Unexpected token. Invalid type constructor."
        , explain = NONE
        }


  fun maybeLongTycon toks i =
    if check toks Token.isMaybeLongTyCon i then
      (i + 1, MaybeLongToken.make (Seq.nth toks i))
    else
      ParserUtils.tokError toks
        { pos = i
        , what =
            "Unexpected token. Invalid (possibly qualified)\
            \ type constructor."
        , explain = NONE
        }


  fun maybeLongStrid toks i =
    if check toks Token.isMaybeLongStrIdentifier i then
      (i + 1, MaybeLongToken.make (Seq.nth toks i))
    else
      ParserUtils.tokError toks
        { pos = i
        , what =
            "Unexpected token. Invalid (possibly qualified)\
            \ structure identifier."
        , explain = NONE
        }


  fun tyvars toks i =
    if
      check toks Token.isTyVar i
    then
      (i + 1, Ast.SyntaxSeq.One (Seq.nth toks i))
    else if
      not
        (isReserved toks Token.OpenParen i
         andalso check toks Token.isTyVar (i + 1))
    then
      (i, Ast.SyntaxSeq.Empty)
    else
      let
        val (i, openParen) = (i + 1, Seq.nth toks i)
        val (i, {elems, delims}) =
          ParserCombinators.oneOrMoreDelimitedByReserved toks
            {parseElem = tyvar toks, delim = Token.Comma} i
        val (i, closeParen) = reserved toks Token.CloseParen i
      in
        ( i
        , Ast.SyntaxSeq.Many
            { left = openParen
            , right = closeParen
            , elems = elems
            , delims = delims
            }
        )
      end

end
