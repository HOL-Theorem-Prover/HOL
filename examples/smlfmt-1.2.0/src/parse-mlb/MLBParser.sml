(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure MLBParser:
sig
  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = MLBToken.t Seq.t

  val basdec: tokens -> (int, MLBAst.basdec) parser
  val basexp: tokens -> (int, MLBAst.basexp) parser

  val parse: Source.t -> MLBAst.t
end =
struct

  type ('a, 'b) parser = ('a, 'b) ParserCombinators.parser
  type tokens = MLBToken.t Seq.t

  fun check_ toks f i =
    i < Seq.length toks andalso f (Seq.nth toks i)

  fun isReserved_ toks rc i =
    check_ toks
      (fn t =>
         case MLBToken.getClass t of
           MLBToken.Reserved rc' => rc = rc'
         | _ => false) i

  fun isSMLReserved_ toks rc i =
    check_ toks
      (fn t =>
         case MLBToken.getClass t of
           MLBToken.SML (Token.Reserved rc') => rc = rc'
         | _ => false) i


  fun nyi_ toks fname i =
    if i >= Seq.length toks then
      raise Error.Error
        (Error.lineError
           { header = "ERROR: NOT YET IMPLEMENTED"
           , pos = MLBToken.getSource (Seq.nth toks (Seq.length toks - 1))
           , what = "Unexpected EOF after token."
           , explain = SOME ("(TODO: see parser " ^ fname ^ ")")
           })
    else if i >= 0 then
      raise Error.Error
        (Error.lineError
           { header = "ERROR: NOT YET IMPLEMENTED"
           , pos = MLBToken.getSource (Seq.nth toks i)
           , what = "Unexpected token."
           , explain = SOME ("(TODO: see parser " ^ fname ^ ")")
           })
    else
      raise Fail ("Bug in parser " ^ fname ^ ": position out of bounds??")


  fun parse_SMLReserved toks rc i =
    if isSMLReserved_ toks rc i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.error
        { pos = MLBToken.getSource (Seq.nth toks i)
        , what =
            "Unexpected token. Expected to see " ^ "'"
            ^ Token.reservedToString rc ^ "'"
        , explain = NONE
        }


  fun checkSML toks f i =
    i < Seq.length toks
    andalso
    case MLBToken.getClass (Seq.nth toks i) of
      MLBToken.SML c =>
        f (Token.fromPre
          (Token.Pretoken.make (MLBToken.getSource (Seq.nth toks i)) c))
    | _ => false


  fun parse_strid toks i =
    if checkSML toks Token.isStrIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.error
        { pos = MLBToken.getSource (Seq.nth toks i)
        , what = "Expected structure identifier."
        , explain = SOME
            "Must be alphanumeric, and cannot start with a\
            \ prime (')"
        }


  fun parse_sigid toks i =
    if checkSML toks Token.isStrIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.error
        { pos = MLBToken.getSource (Seq.nth toks i)
        , what = "Expected signature identifier."
        , explain = SOME
            "Must be alphanumeric, and cannot start with a\
            \ prime (')"
        }


  fun parse_funid toks i =
    if checkSML toks Token.isStrIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.error
        { pos = MLBToken.getSource (Seq.nth toks i)
        , what = "Expected functor identifier."
        , explain = SOME
            "Must be alphanumeric, and cannot start with a\
            \ prime (')"
        }


  fun parse_basid toks i =
    if checkSML toks Token.isStrIdentifier i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.error
        { pos = MLBToken.getSource (Seq.nth toks i)
        , what = "Expected basis identifier."
        , explain = SOME
            "Must be alphanumeric, and cannot start with a\
            \ prime (')"
        }


  fun parse_stringConstant toks i =
    if checkSML toks Token.isStringConstant i then
      (i + 1, Seq.nth toks i)
    else
      ParserUtils.error
        { pos = MLBToken.getSource (Seq.nth toks i)
        , what = "Expected string literal."
        , explain = NONE
        }


  fun parse_oneOrMoreDelimitedBySMLReserved (toks: tokens) {parseElem, delim} i =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun isReserved rc =
        checkSML toks (fn t => Token.Reserved rc = Token.getClass t)

      fun loop elems delims i =
        let
          val (i, elem) = parseElem i
          val elems = elem :: elems
        in
          if isReserved delim i then loop elems (tok i :: delims) (i + 1)
          else (i, elems, delims)
        end

      val (i, elems, delims) = loop [] [] i
    in
      (i, {elems = Seq.fromRevList elems, delims = Seq.fromRevList delims})
    end


  fun basexp toks start =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun check f i =
        check_ toks f i
      fun isReserved rc i =
        isReserved_ toks rc i
      fun isSMLReserved rc i =
        isSMLReserved_ toks rc i


      (** bas basdec end
        *    ^
        *)
      fun parse_bas bas i =
        let
          val (i, basdec) = basdec toks i
          val (i, endd) = parse_SMLReserved toks Token.End i
        in
          (i, MLBAst.BasEnd {bas = bas, basdec = basdec, endd = endd})
        end


      (** let basdec in basexp end
        *    ^
        *)
      fun parse_let lett i =
        let
          val (i, basdec) = basdec toks i
          val (i, inn) = parse_SMLReserved toks Token.In i
          val (i, basexp) = parse_basexp i
          val (i, endd) = parse_SMLReserved toks Token.End i
        in
          ( i
          , MLBAst.LetInEnd
              { lett = lett
              , basdec = basdec
              , inn = inn
              , basexp = basexp
              , endd = endd
              }
          )
        end


      and parse_basexp i =
        if checkSML toks Token.isStrIdentifier i then
          (i + 1, MLBAst.Ident (tok i))
        else if isReserved MLBToken.Bas i then
          parse_bas (tok i) (i + 1)
        else if isSMLReserved Token.Let i then
          parse_let (tok i) (i + 1)
        else
          ParserUtils.error
            { pos = MLBToken.getSource (tok i)
            , what = "Unexpected token."
            , explain = SOME "Expected beginning of basis expression."
            }

    in
      parse_basexp start
    end


  and basdec toks start =
    let
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun check f i =
        check_ toks f i
      fun isReserved rc i =
        isReserved_ toks rc i
      fun isSMLReserved rc i =
        isSMLReserved_ toks rc i


      (** not yet implemented *)
      fun nyi fname i =
        nyi_ toks fname i


      fun makeSMLPath pathtok pathstr =
        MLBAst.DecPathSML
          {token = pathtok, path = FilePath.fromUnixPath pathstr}

      fun makeMLBPath pathtok pathstr =
        MLBAst.DecPathMLB
          {token = pathtok, path = FilePath.fromUnixPath pathstr}


      (**  "path.{sml,mlb,...}"
        * ^
        *
        * TODO: this is a bit of a mess. Some repeated but slightly different
        * behavior from the lexer, which already distinguishes between SML
        * and MLB paths for unquoted path strings. Perhaps the lexer should be
        * simplified, and the quoted/unquoted path handling logic should be
        * unified?
        *)
      fun parse_decPathFromString i =
        let
          val thisTok = tok i
          val thisSrc = MLBToken.getSource thisTok
          val n = Source.length thisSrc
          val _ =
            if
              n >= 2 andalso Source.nth thisSrc 0 = #"\""
              andalso Source.nth thisSrc (n - 1) = #"\""
            then ()
            else raise Fail "MLBParser bug! see parse_decPathFromString: fail 1"

          val pathstr = Source.toString (Source.slice thisSrc (1, n - 2))

          fun mlbCase () =
            (i + 1, makeMLBPath thisTok pathstr)
          fun smlCase () =
            (i + 1, makeSMLPath thisTok pathstr)
        in
          case OS.Path.ext pathstr of
            SOME "mlb" => mlbCase ()
          | SOME "sml" => smlCase ()
          | SOME "sig" => smlCase ()
          | SOME "fun" => smlCase ()
          | _ =>
              ParserUtils.error
                { pos = MLBToken.getSource thisTok
                , what = "Missing or invalid file extension in path."
                , explain = SOME "Valid extensions are: .mlb .sml .sig .fun"
                }
        end


      (** basis basid = basexp [and ...]
        *      ^
        *)
      fun parse_decBasis basis i =
        let
          fun parseElem i =
            let
              val (i, basid) = parse_basid toks i
              val (i, eq) = parse_SMLReserved toks Token.Equal i
              val (i, basexp) = basexp toks i
            in
              (i, {basid = basid, eq = eq, basexp = basexp})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedBySMLReserved toks
              {parseElem = parseElem, delim = Token.And} i
        in
          (i, MLBAst.DecBasis {basis = basis, elems = elems, delims = delims})
        end


      (** open basid ... basid
        *     ^
        *)
      fun parse_decOpen openn i =
        let
          val (i, elems) =
            ParserCombinators.oneOrMoreWhile
              (checkSML toks Token.isStrIdentifier) (parse_basid toks) i
        in
          (i, MLBAst.DecOpen {openn = openn, elems = elems})
        end


      (** structure strid [= strid] [and ...]
        *          ^
        *)
      fun parse_decStructure structuree i =
        let
          fun parseElem i =
            let
              val (i, strid) = parse_strid toks i
              val (i, eqstrid) =
                if not (isSMLReserved Token.Equal i) then
                  (i, NONE)
                else
                  let
                    val (i, eq) = (i + 1, tok i)
                    val (i, strid) = parse_strid toks i
                  in
                    (i, SOME {eq = eq, strid = strid})
                  end
            in
              (i, {strid = strid, eqstrid = eqstrid})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedBySMLReserved toks
              {parseElem = parseElem, delim = Token.And} i
        in
          ( i
          , MLBAst.DecStructure
              {structuree = structuree, elems = elems, delims = delims}
          )
        end


      (** signature sigid [= sigid] [and ...]
        *          ^
        *)
      fun parse_decSignature signaturee i =
        let
          fun parseElem i =
            let
              val (i, sigid) = parse_sigid toks i
              val (i, eqsigid) =
                if not (isSMLReserved Token.Equal i) then
                  (i, NONE)
                else
                  let
                    val (i, eq) = (i + 1, tok i)
                    val (i, sigid) = parse_sigid toks i
                  in
                    (i, SOME {eq = eq, sigid = sigid})
                  end
            in
              (i, {sigid = sigid, eqsigid = eqsigid})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedBySMLReserved toks
              {parseElem = parseElem, delim = Token.And} i
        in
          ( i
          , MLBAst.DecSignature
              {signaturee = signaturee, elems = elems, delims = delims}
          )
        end


      (** functor funid [= funid] [and ...]
        *        ^
        *)
      fun parse_decFunctor functorr i =
        let
          fun parseElem i =
            let
              val (i, funid) = parse_funid toks i
              val (i, eqfunid) =
                if not (isSMLReserved Token.Equal i) then
                  (i, NONE)
                else
                  let
                    val (i, eq) = (i + 1, tok i)
                    val (i, funid) = parse_funid toks i
                  in
                    (i, SOME {eq = eq, funid = funid})
                  end
            in
              (i, {funid = funid, eqfunid = eqfunid})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedBySMLReserved toks
              {parseElem = parseElem, delim = Token.And} i
        in
          ( i
          , MLBAst.DecFunctor
              {functorr = functorr, elems = elems, delims = delims}
          )
        end


      (** ann "annotation" [...] in basdec end
        *    ^
        *)
      fun parse_decAnn ann i =
        let
          val (i, annotations) =
            ParserCombinators.oneOrMoreWhile
              (checkSML toks Token.isStringConstant) (parse_stringConstant toks)
              i

          val (i, inn) = parse_SMLReserved toks Token.In i
          val (i, basdec) = parse_dec i
          val (i, endd) = parse_SMLReserved toks Token.End i
        in
          ( i
          , MLBAst.DecAnn
              { ann = ann
              , annotations = annotations
              , inn = inn
              , basdec = basdec
              , endd = endd
              }
          )
        end


      (** local basdec in basdec end
        *      ^
        *)
      and parse_decLocal locall i =
        let
          val (i, basdec1) = parse_dec i
          val (i, inn) = parse_SMLReserved toks Token.In i
          val (i, basdec2) = parse_dec i
          val (i, endd) = parse_SMLReserved toks Token.End i
        in
          ( i
          , MLBAst.DecLocalInEnd
              { locall = locall
              , basdec1 = basdec1
              , inn = inn
              , basdec2 = basdec2
              , endd = endd
              }
          )
        end


      and parse_exactlyOneDec i =
        if check MLBToken.isSMLPath i then
          ( i + 1
          , makeSMLPath (tok i) (Source.toString (MLBToken.getSource (tok i)))
          )
        else if check MLBToken.isMLBPath i then
          ( i + 1
          , makeMLBPath (tok i) (Source.toString (MLBToken.getSource (tok i)))
          )
        else if check MLBToken.isStringConstant i then
          parse_decPathFromString i
        else if isReserved MLBToken.UnderscorePrim i then
          (i + 1, MLBAst.DecUnderscorePrim (tok i))
        else if isReserved MLBToken.Basis i then
          parse_decBasis (tok i) (i + 1)
        else if isReserved MLBToken.Ann i then
          parse_decAnn (tok i) (i + 1)
        else if isSMLReserved Token.Open i then
          parse_decOpen (tok i) (i + 1)
        else if isSMLReserved Token.Local i then
          parse_decLocal (tok i) (i + 1)
        else if isSMLReserved Token.Structure i then
          parse_decStructure (tok i) (i + 1)
        else if isSMLReserved Token.Signature i then
          parse_decSignature (tok i) (i + 1)
        else if isSMLReserved Token.Functor i then
          parse_decFunctor (tok i) (i + 1)
        else
          ParserUtils.error
            { pos = MLBToken.getSource (tok i)
            , what = "Unexpected token."
            , explain = SOME "Expected beginning of basis declaration."
            }


      and parse_dec i =
        let
          fun parse_maybeSemicolon i =
            if isSMLReserved Token.Semicolon i then (i + 1, SOME (tok i))
            else (i, NONE)

          fun continue i = check MLBToken.isBasDecStartToken i

          (** While we see a basdec start-token, parse pairs of
            *   (dec, semicolon option)
            *)
          val (i, basdecs) =
            ParserCombinators.zeroOrMoreWhile continue
              (ParserCombinators.two (parse_exactlyOneDec, parse_maybeSemicolon))
              i

          fun makeDecMultiple () =
            MLBAst.DecMultiple
              {elems = Seq.map #1 basdecs, delims = Seq.map #2 basdecs}

          val result =
            case Seq.length basdecs of
              0 => MLBAst.DecEmpty
            | 1 =>
                let val (dec, semicolon) = Seq.nth basdecs 0
                in if isSome semicolon then makeDecMultiple () else dec
                end
            | _ => makeDecMultiple ()
        in
          (i, result)
        end

    in
      parse_dec start
    end


  fun parse src =
    let
      val toksWithComments = MLBLexer.tokens src
      val toks =
        Seq.filter (not o MLBToken.isCommentOrWhitespace) toksWithComments

      val (i, basdec) = basdec toks 0

      val _ =
        if i >= Seq.length toks then
          ()
        else
          ParserUtils.error
            { pos = MLBToken.getSource (Seq.nth toks i)
            , what = "Unexpected token."
            , explain = SOME "Invalid start of basis declaration!"
            }
    in
      MLBAst.Ast basdec
    end

end
