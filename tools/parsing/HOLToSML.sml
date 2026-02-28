structure HOLToSML :> HOLToSML = struct
open HOLAst

exception Unreachable

fun pluck p [] = NONE
  | pluck p (h::t) =
    if p h then SOME(h,t)
    else case pluck p t of NONE => NONE | SOME (e,t) => SOME(e,h::t)

fun mkHandleHolErr (p, e) = let
  val pat = App (mkIdent (p, "Feedback.HOL_ERR"), Wild p)
  val h = mkIdent (p, "boolTheory.TRUTH")
  val arm = {bar = NONE, pat = pat, arrow = NONE, exp = h}
  in Handle {exp = e, handle_ = p, elems = [arm], stop = expStop e} end

fun mkKval {key, bind = NONE} = #2 key
  | mkKval {key, bind = SOME {vals, ...}} =
    concat [#2 key, " = ", String.concatWith " " (map #2 vals)]

fun mkNameAttrs _ (p, name) NONE = mkString (p, name)
  | mkNameAttrs f (p, name) (SOME {attrs = {args, ...}, ...}: 'a attrs) =
    mkString (p, concat [name, "[", String.concatWith ", " (map f args), "]"])

fun expandRecord f pat {left, elems = {args, delims, stop = stop1}, right, stop} = let
  fun reord [] NONE acc = rev acc
    | reord [] (SOME p) acc = rev (DotDotDot p :: acc)
    | reord (DotDotDot p :: ls) _ acc = reord ls (SOME p) acc
    | reord (LabEq {lab, eq, exp} :: ls) dot acc =
      reord ls dot (LabEq {lab = lab, eq = eq, exp = f exp} :: acc)
    | reord ((lab as LabAs {id, ty, aspat}) :: ls) dot acc = let
      val aspat = Option.map (fn {as_, exp} => {as_ = as_, exp = f exp}) aspat
      fun typed exp NONE = exp
        | typed exp (SOME {colon, ty}) = Typed {exp = exp, colon = colon, ty = ty}
      val lab = if pat then LabAs {id = id, ty = ty, aspat = aspat} else let
        val pat' = case aspat of
          NONE => LabEq {lab = id, eq = #1 id, exp = typed (mkIdent id) ty}
        | SOME {as_, exp} => LabEq {lab = id, eq = as_, exp = typed exp ty}
        in LabExpansion {orig = lab, result = pat'} end
      in reord ls dot (lab :: acc) end
    | reord (LabExpansion _ :: _) _ _ = raise Fail "double row expansion"
  val elems = {args = reord args NONE [], delims = delims, stop = stop1}
  in {left = left, elems = elems, right = right, stop = stop} end

fun mkLocPragma line col s =
  concat [" (*#loc ", Int.toString (line + 1), " ", Int.toString (col + 1), "*)", s]

fun mkLocString (p, noloc, _) {file = "", ...} = mkIdent (p, noloc)
  | mkLocString (p, _, loc) {file, line, ...} =
    App (mkIdent (p, loc), App (mkIdent (p, "DB_dtype.mkloc"),
      mkTuple (p, [mkString (p, file), mkInt (p, line+1), mkIdent (p, "true")])))

fun mkLocString' (p, loc) {file = "", ...} = App (mkIdent (p, loc), mkIdent (p, "DB_dtype.Unknown"))
  | mkLocString' (p, loc) {file, line, ...} =
    App (mkIdent (p, loc), App (mkIdent (p, "DB_dtype.mkloc"),
      mkTuple (p, [mkString (p, file), mkInt (p, line+1), mkIdent (p, "true")])))

fun doProofKvals p [] tac = tac
  | doProofKvals p (kv::kvs) tac = let
  val e = mkIdent (p, "BasicProvers.with_simpset_updates")
  fun mktm1 {key = (p, key), bind} = let
    val args = case bind of NONE => [] | SOME {vals, ...} => map mkString vals
    val key = case key of
      "exclude_simps" => "simpLib.remove_simps"
    | "exclude_frags" => "simpLib.remove_ssfrags"
    | _ => key
    in App (mkIdent (p, key), mkList (p, args)) end
  fun mktm (kv, e) = Infix {left = e, id = (p, "o"), right = mktm1 kv}
  in App (App (e, foldl mktm (mktm1 kv) kvs), tac) end

fun doProofAttrs p (SOME {attrs = {args = kvs, ...}, ...}) tac = doProofKvals p kvs tac
  | doProofAttrs _ _ tac = tac

fun wrapTac (p, tac) = let
  val dummy = mkIdent (p, "HOL__GOAL__foo")
  in Fn {fn_ = p,
       elems = [{bar = NONE, pat = dummy, arrow = NONE, exp = App (tac, dummy)}],
       stop = expStop tac} end

val canBindStr = true (* TODO: make false on mosml *)

fun valPat pos pat e = let
  val s = {rec_ = NONE, pat = pat, eq = SOME {eq = pos, exp = e}}
  in DecVal {val_ = pos, tyvars = Empty, elems = {args = [s], delims = [], stop = expStop e}} end

fun valWild pos = valPat pos (Wild pos)

fun magicBind (p, name) acc =
  if canBindStr then let
    val code = mkString (p, concat ["val ", name, " = DB.fetch \"-\" \"", name,
      "\" handle Feedback.HOL_ERR _ => boolTheory.TRUTH;"])
    in valWild p (App (mkIdent (p, "CompilerSpecific.quietbind"), code)) :: acc end
  else acc

fun mapArms g f1 f2 elems = let
  fun list [] _ f = f []
    | list (x :: xs) g f =
      g x (fn x => list xs g (fn xs => f (x :: xs)))

  fun delims {args, delims, stop} g f =
    list args g (fn args => f {args = args, delims = delims, stop = stop})

  fun onPat (List {left, elems, right, stop}) f =
      delims elems onPat
        (fn elems => f (List {left = left, elems = elems, right = right, stop = stop}))
    | onPat (Tuple {left, elems, right, stop}) f =
      delims elems onPat
        (fn elems => f (Tuple {left = left, elems = elems, right = right, stop = stop}))
    | onPat (Record r) f = let
      val {left, elems, right, stop} = expandRecord (fn x => x) true r
      in delims elems onRow (fn elems =>
        f (Record {left = left, elems = elems, right = right, stop = stop}))
      end
    | onPat (Parens {left, exp, right, stop}) f =
      onPat exp (fn exp => f (Parens {left = left, exp = exp, right = right, stop = stop}))
    | onPat (Typed {exp, colon, ty}) f =
      onPat exp (fn exp => f (Typed {exp = exp, colon = colon, ty = ty}))
    | onPat (Layered {op_, id, ty, as_, pat}) f =
      onPat pat (fn pat => f (Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = pat}))
    | onPat (App (e1, e2)) f = onPat e1 (fn e1 => onPat e2 (fn e2 => f (App (e1, e2))))
    | onPat (Or {args, ...}) f = orList args f
    | onPat e f = f (g e)

  and onRow (LabEq {lab, eq, exp}) f =
      onPat exp (fn exp => f (LabEq {lab = lab, eq = eq, exp = exp}))
    | onRow (LabAs {id, ty, aspat = SOME {as_, exp}}) f =
      onPat exp (fn exp => f (LabAs {id = id, ty = ty, aspat = SOME {as_ = as_, exp = exp}}))
    | onRow e f = f e

  and orList [] _ = (fn x => x)
    | orList (e :: es) f = onPat e f o orList es f

  fun arms [] = (fn x => x)
    | arms (x :: ls) = onPat (f1 x) (fn pat => fn l => f2 (x, pat) :: l) o arms ls
  in arms elems [] end

fun mkFail (p, err) = Raise {raise_ = p, exp = App (mkIdent (p, "Fail"), mkString (p, err))}
fun mkSemi acc = DecSemi (case acc of [] => 0 | d::_ => decStop d) :: acc

fun withLocalAttrs _ false attrs = attrs
  | withLocalAttrs p true attrs = let
    val local_ = {key = (p, "local"), bind = NONE}
    in case attrs of
      NONE => SOME {
      left = p, attrs = {args = [local_], delims = [], stop = p},
      right = NONE, stop = p}
    | SOME {left, attrs = {args, delims, stop = stop1}, right, stop} => SOME {
      left = left, attrs = {args = args @ [local_], delims = delims, stop = stop1},
      right = right, stop = stop}
    end

exception HasOrPat
fun mapDelim f {args, delims, stop} = {args = map f args, delims = delims, stop = stop}

fun expandDec {parseError, quietOpen, fileline} = let

fun expandExp true (e as Wild _) = e
  | expandExp false (Wild p) = mkFail (p, "_")
  | expandExp _ (e as IntegerConstant _) = e
  | expandExp _ (e as WordConstant _) = e
  | expandExp _ (StringConstant (p, s)) = mkString (p, decodeStr parseError s 1 (size s - 1))
  | expandExp _ (CharConstant (p, s)) = let
    val s = decodeStr parseError s 2 (size s - 1)
    in CharConstant (p, encodeStr (Substring.full s) "#\"" "\"") end
  | expandExp _ (e as RealConstant _) = e
  | expandExp _ (e as Unit _) = e
  | expandExp _ (e as Ident _) = e
  | expandExp pat (List {left, elems, right, stop}) =
    List {left = left, elems = mapDelim (expandExp pat) elems, right = right, stop = stop}
  | expandExp pat (Tuple {left, elems, right, stop}) =
    Tuple {left = left, elems = mapDelim (expandExp pat) elems, right = right, stop = stop}
  | expandExp pat (Record r) = Record (expandRecord (expandExp pat) pat r)
  | expandExp pat (Parens {left, exp, right, stop}) =
    Parens {left = left, exp = expandExp pat exp, right = right, stop = stop}
  | expandExp pat (Infix {left, id, right}) =
    Infix {left = expandExp pat left, id = id, right = expandExp pat right}
  | expandExp pat (Typed {exp, colon, ty}) = Typed {exp = expandExp pat exp, colon = colon, ty = ty}
  | expandExp pat' (Layered {op_, id, ty, as_, pat}) =
    Layered {op_ = op_, id = id, ty = ty, as_ = as_, pat = expandExp pat' pat}
  | expandExp _ (Or _) = raise HasOrPat
  | expandExp _ (e as Select _) = e
  | expandExp pat (Sequence {left, elems, right, stop}) =
    Sequence {left = left, elems = mapDelim (expandExp pat) elems, right = right, stop = stop}
  | expandExp _ (LetInEnd {let_, dec, in_, exps, end_, stop}) =
    LetInEnd {let_ = let_, dec = map (expandDec false) dec, in_ = in_,
      exps = mapDelim (expandExp false) exps, end_ = end_, stop = stop}
  | expandExp pat (App (e1, e2)) = App (expandExp pat e1, expandExp pat e2)
  | expandExp _ (AndAlso {left, andalso_, right}) =
    AndAlso {left = expandExp false left, andalso_ = andalso_, right = expandExp false right}
  | expandExp _ (OrElse {left, orelse_, right}) =
    OrElse {left = expandExp false left, orelse_ = orelse_, right = expandExp false right}
  | expandExp _ (Handle {exp, handle_, elems, stop}) = let
    val exp = expandExp false exp
    in Handle {exp = exp, handle_ = handle_, elems = expandArms handle_ elems, stop = stop} end
  | expandExp _ (Raise {raise_, exp}) = Raise {raise_ = raise_, exp = expandExp false exp}
  | expandExp _ (e as IfThenElse {if_, exp1, then_, exp2, else_}) = let
    val exp1 = expandExp false exp1
    val exp2 = expandExp false exp2
    val exp3 = case else_ of
      NONE => SOME {else_ = if_, exp3 = Unit {left = if_, right = if_}}
    | SOME {else_, exp3} => SOME {else_ = else_, exp3 = expandExp false exp3}
    val e' = IfThenElse {if_ = if_, exp1 = exp1, then_ = then_, exp2 = exp2, else_ = exp3}
    in case else_ of NONE => ExpExpansion {orig = e, result = e'} | _ => e' end
  | expandExp _ (While {while_, exp1, do_, exp2}) =
    While {while_ = while_, exp1 = expandExp false exp1, do_ = do_, exp2 = expandExp false exp2}
  | expandExp _ (Case {case_, exp, of_, elems, stop}) = let
    val exp = expandExp false exp
    val p = Option.getOpt (of_, case_)
    in Case {case_ = case_, exp = exp, of_ = of_, elems = expandArms p elems, stop = stop} end
  | expandExp _ (Fn {fn_, elems, stop}) = Fn {fn_ = fn_, elems = expandArms fn_ elems, stop = stop}

  | expandExp _ (e as HOLFullQuote {head, type_q, quote, stop, ...}) = let
    val id = (#1 head, case type_q of NONE => "Parse.Term" | SOME _ => "Parse.Type")
    val e' = App (mkIdent id, expandQuote (#1 head) stop quote)
    in ExpExpansion {orig = e, result = e'} end
  | expandExp _ (e as HOLQuote {head, quote, stop, ...}) =
    ExpExpansion {orig = e, result = expandQuote (#1 head) stop quote}
  | expandExp _ (e as HOLLinePragma {hash_, ...}) = let
    val e' = IntegerConstant (hash_, Int.toString (#line (fileline hash_) + 1))
    in ExpExpansion {orig = e, result = e'} end
  | expandExp _ (e as HOLFilePragma {hash_, ...}) =
    ExpExpansion {orig = e, result = mkString (hash_, #file (fileline hash_))}
  | expandExp _ (e as HOLLinePragmaWith {hash_, ...}) =
    ExpExpansion {orig = e, result = Unit {left = hash_, right = hash_}}
  | expandExp _ (e as HOLFilePragmaWith {hash_, ...}) =
    ExpExpansion {orig = e, result = Unit {left = hash_, right = hash_}}
  | expandExp _ (e as ExpEmpty p) = ExpExpansion {orig = e, result = Unit {left = p, right = p}}
  | expandExp _ (e as ExpBad {start = p, ...}) =
    ExpExpansion {orig = e, result = mkFail (p, "malformed")}
  | expandExp pat (ExpExpansion {orig, result}) =
    ExpExpansion {orig = orig, result = expandExp pat result}

and expandArms p [] =
    [{bar = NONE, pat = Wild p, arrow = NONE, exp = Raise {raise_ = p, exp = mkIdent (p, "Bind")}}]
  | expandArms _ elems =
    map (fn {bar, pat, arrow, exp} =>
      {bar = bar, pat = expandExp true pat, arrow = arrow, exp = expandExp false exp}) elems
    handle HasOrPat => mapArms (expandExp true) #pat
      (fn ({bar, arrow, exp, ...}, pat) => {bar = bar, pat = pat, arrow = arrow, exp = exp}) elems

and expandFunBranches p [] =
    [{bar = NONE, pat = Wild p, eq = NONE, exp = Raise {raise_ = p, exp = mkIdent (p, "Bind")}}]
  | expandFunBranches _ elems = let
    val elems = map (fn {bar, pat, eq, exp} =>
      {bar = bar, pat = pat, eq = eq, exp = expandExp false exp}) elems
    in
      map (fn {bar, pat, eq, exp} =>
        {bar = bar, pat = expandExp true pat, eq = eq, exp = exp}) elems
      handle HasOrPat => mapArms (expandExp true) #pat
        (fn ({bar, eq, exp, ...}, pat) => {bar = bar, pat = pat, eq = eq, exp = exp}) elems
    end

and expandQuoteCore start toks = let
  fun go [] acc = rev acc
    | go (QuoteLiteral (pos, value) :: rest) acc = let
      val {line, col, file = _} = fileline pos
      val s = mkLocPragma line col value
      in go rest (App (mkIdent (start, "QUOTE"), mkString (start, s)) :: acc) end
    | go (QuoteAntiq {exp, ...} :: rest) acc =
      go rest (App (mkIdent (start, "ANTIQUOTE"), expandExp false exp) :: acc)
    | go (DefinitionLabel _ :: _) _ = raise Unreachable
  in go toks [] end

and expandQuote start stop toks = let
  val elems = {args = expandQuoteCore start toks, delims = [], stop = stop}
  in List {left = start, elems = elems, right = NONE, stop = stop} end

and expandDec _ (dec as DecSemi _) = DecExpansion {orig = dec, result = []}
  | expandDec _ (DecVal {val_, tyvars, elems}) = let
    fun f {rec_, pat, eq} = let
      val pat = expandExp true pat handle HasOrPat => let
        val (start, stop) = expSpan pat
        val _ = parseError (start, stop) "or patterns not supported here"
        in ExpBad {start = start, stop = stop} end
      val eq = Option.map (fn {eq, exp} => {eq = eq, exp = expandExp false exp}) eq
      in {rec_ = rec_, pat = pat, eq = eq} end
    in DecVal {val_ = val_, tyvars = tyvars, elems = mapDelim f elems} end
  | expandDec _ (DecFun {fun_, tyvars, fvalbind}) = let
    val fvalbind = mapDelim (expandFunBranches fun_) fvalbind
    in DecFun {fun_ = fun_, tyvars = tyvars, fvalbind = fvalbind} end
  | expandDec _ (dec as DecType _) = dec
  | expandDec _ (dec as DecEqtype _) = dec
  | expandDec _ (dec as DecDatatype _) = dec
  | expandDec _ (dec as DecAbstype _) = dec
  | expandDec _ (dec as DecException _) = dec
  | expandDec top (DecLocal {local_, dec1, in_, dec2, end_, stop}) =
    DecLocal {local_ = local_, dec1 = map (expandDec false) dec1, in_ = in_,
      dec2 = map (expandDec top) dec2, end_ = end_, stop = stop}
  | expandDec _ (dec as DecOpen _) = dec
  | expandDec _ (dec as DecInfix _) = dec
  | expandDec _ (dec as DecInfixr _) = dec
  | expandDec _ (dec as DecNonfix _) = dec
  | expandDec _ (DecStructure {structure_, elems}) = let
    fun f {id, constraint, bind} = let
      val bind = Option.map (fn {eq, strexp} => {eq = eq, strexp = expandStrExp strexp}) bind
      in {id = id, constraint = constraint, bind = bind} end
    in DecStructure {structure_ = structure_, elems = mapDelim f elems} end
  | expandDec _ (DecSignature {signature_, elems}) = let
    fun f {eq, sigexp} = {eq = eq, sigexp = expandSigExp sigexp}
    fun g {id, bind} = {id = id, bind = Option.map f bind}
    in DecSignature {signature_ = signature_, elems = mapDelim g elems} end
  | expandDec _ (DecInclude {include_, sigexps}) =
    DecInclude {include_ = include_, sigexps = map expandSigExp sigexps}
  | expandDec _ (dec as Sharing _) = dec
  | expandDec _ (DecFunctor {functor_, elems}) = let
    fun f {id, lparen, funarg, rparen, constraint, bind} = let
      val funarg = expandFunArg funarg
      val bind = Option.map (fn {eq, strexp} => {eq = eq, strexp = expandStrExp strexp}) bind
      in {id = id, lparen = lparen, funarg = funarg,
          rparen = rparen, constraint = constraint, bind = bind} end
    in DecFunctor {functor_ = functor_, elems = mapDelim f elems} end
  | expandDec top (dec as DecExp e) = let
    val p = expStart e
    val dec' = valPat p (if top then mkIdent (p, "it") else Wild p) (expandExp false e)
    in DecExpansion {orig = dec, result = [dec']} end

  | expandDec _ (dec as HOLTheory {theory_, id, attrs, elems, ...}) = let
    val bare = ref false
    val _ = app (fn
        {key = (_, "bare"), bind = NONE} => bare := true
      | {key = (_, "no_sig_docs"), bind = NONE} => ()  (* considered in HOLTheoryEnd *)
      | {key = (p, s), ...} => parseError (p, p + size s) "unknown theory attribute"
      ) (case attrs of NONE => [] | SOME v => #args (#attrs v))
    val grammar = ref (if !bare then [] else [mkString (theory_, "hol")])
    fun finish (NONE, acc) = acc
      | finish (SOME (false, ns), acc) = mkSemi (DecOpen {open_ = theory_, elems = rev ns} :: acc)
      | finish (SOME (true, ns), acc) = let
        val dec = DecOpen {open_ = theory_, elems = rev ns}
        val stop = decStop dec
        in
          mkSemi (DecLocal {
            local_ = theory_, dec1 = [dec],
            in_ = SOME stop, dec2 = [], end_ = SOME stop, stop = stop} :: acc)
        end
    fun push b x (NONE, acc) = (SOME (b, [x]), acc)
      | push b x (p as (SOME (b2, ns), acc)) =
        if b = b2 then (SOME (b2, x :: ns), acc) else (SOME (b, [x]), finish p)
    fun process [] acc = finish acc
      | process (HOLAncestors {elems, ...} :: ls) acc = processList true elems ls acc
      | process (HOLLibs {elems, ...} :: ls) acc = processList false elems ls acc
    and processList _ [] ls acc = process ls acc
      | processList isThy ({id, attrs} :: thys) ls acc = let
        val aliases = ref []
        val qualified = ref false
        val ignoreGrammar = ref false
        val _ = app (fn x => case (x, isThy) of
            ({key = (_, "alias"), bind = SOME {vals = [tgt], ...}}, _) => aliases := tgt :: !aliases
          | ({key = (_, "qualified"), bind = NONE}, _) => qualified := true
          | ({key = (_, "ignore_grammar"), bind = NONE}, true) => ignoreGrammar := true
          | ({key = (p, s), ...}, _) => parseError (p, p + size s) "unknown header attribute"
          ) (case attrs of NONE => [] | SOME v => #args (#attrs v))
        val id' = if isThy then (#1 id, #2 id ^ "Theory") else id
        val acc = push (!qualified) id' acc
        val _ =
          if isThy andalso not (!ignoreGrammar) then grammar := mkString id :: !grammar else ()
        val acc = foldl (fn (tgt, acc) => let
          val stop = idStop tgt
          val s = {id = tgt, constraint = NONE, bind = SOME {eq = stop, strexp = StrIdent id'}}
          val elems = {args = [s], delims = [], stop = stop}
          val d = DecStructure {structure_ = #1 tgt, elems = elems}
          in (NONE, d :: finish acc) end) acc (rev (!aliases))
        in processList isThy thys ls acc end
    val lhs = if !bare then NONE else SOME (false,
      map (fn s => (theory_, s)) ["Parse", "bossLib", "boolLib", "HolKernel", "holTheory"])
    val acc = []
    val acc = if quietOpen then
      case process elems (lhs, []) of
        [] => acc
      | decs => let
        val unit = Unit {left = theory_, right = theory_}
        fun f x acc = mkSemi (valWild theory_ (App (mkIdent (theory_, x), unit)) :: acc)
        val acc = mkSemi (decs @ f "HOL_Interactive.start_open" acc)
        in f "HOL_Interactive.end_open" acc end
    else process elems (lhs, acc)
    val acc = valWild theory_ (App (mkIdent (theory_, "Theory.new_theory"), mkString id)) :: acc
    val acc = if !bare then acc else
      valWild theory_ (App (mkIdent (theory_, "Parse.set_grammar_ancestry"),
        mkList (theory_, rev (!grammar)))) :: acc
    in DecExpansion {orig = dec, result = rev acc} end
  | expandDec _ (dec as HOLTheoryEnd {theory_, noSigDocs, ...}) = let
    val unit = Unit {left = theory_, right = theory_}
    val e = App (mkIdent (theory_, "Theory.export_theory"), unit)
    val e = if not noSigDocs then e else let
      val set_trace = mkIdent (theory_, "Feedback.set_trace")
      val include_docs = mkString (theory_, "TheoryPP.include_docs")
      val zero = mkInt (theory_, 0)
      val exclude_docs = mkApp set_trace [include_docs, zero]
      in Infix {left = exclude_docs, id = (theory_, "before"), right = e} end
    in DecExpansion {orig = dec, result = [valWild theory_ e]} end
  | expandDec _ (dec as HOLDefinition {
      definition_, id as (_, name), attrs, colon = _, quote, termination, end_ = _, stop}) = let
    val indThm = ref NONE
    val _ = app (fn
        {key = (p, s as "induction"), bind} =>
        (case bind of
          SOME {vals = [tgt], ...} => indThm := SOME tgt
        | _ => parseError (p, p + size s) "unexpected arguments to [induction] attribute")
      | _ => ()
      ) (case attrs of NONE => [] | SOME v => #args (#attrs v))
    val indThm = case !indThm of
      SOME s => s
    | NONE => (#1 id,
      if String.isSuffix "_def" name then
        String.extract (name, 0, SOME (size name - 4)) ^ "_ind"
      else if String.isSuffix "_DEF" name then
        String.extract (name, 0, SOME (size name - 4)) ^ "_IND"
      else name ^ "_ind")
    val fileline = fileline (#1 id)
    val e = mkLocString (definition_, "TotalDefn.qDefine", "TotalDefn.located_qDefine") fileline
    val e = App (e, mkNameAttrs mkKval id attrs)
    val e = App (e, expandQuote definition_ stop quote)
    val e = App (e, case termination of
      NONE => mkIdent (definition_, "NONE")
    | SOME {tac, ...} => App (mkIdent (definition_, "SOME"), expandExp false tac))
    val dec' = magicBind indThm [valPat definition_ (mkIdent id) e]
    in DecExpansion {orig = dec, result = rev dec'} end
  | expandDec _ (dec as HOLDatatype {datatype_, quote, stop, ...}) = let
    val e = App (mkIdent (datatype_, "bossLib.Datatype"), expandQuote datatype_ stop quote)
    in DecExpansion {orig = dec, result = [valWild datatype_ e]} end
  | expandDec _ (dec as HOLQuoteDecl {quote_, id, bind, colon = _, quote, end_ = _, stop}) = let
    val (pat, e) = case bind of
      NONE => (Wild (#1 id), mkIdent id)
    | SOME {exp, ...} => (mkIdent id, expandExp false exp)
    val dec' = valPat quote_ pat (App (e, expandQuote quote_ stop quote))
    in DecExpansion {orig = dec, result = [dec']} end
  | expandDec _ (dec as HOLInductiveDecl {co, inductive_, id = (id, stem), quote, ...}) = let
    val (entryPoint, indSuffix) =
      if co then ("CoIndDefLib.xHol_coreln", "_coind") else ("IndDefLib.xHol_reln", "_ind")
    fun mkQ s = App (mkIdent (inductive_, "QUOTE"), mkString (inductive_, s))
    val frag = mkQ ") /\\ ("
    fun mk l = frag :: expandQuoteCore inductive_ (rev l)
    fun split olab l [] (qs, labs) = (rev (mk l :: qs), rev (olab :: labs))
      | split olab l (DefinitionLabel lab :: r) (qs, labs) =
        if case olab of
            NONE => List.all
            (fn QuoteLiteral (_, value) => isOnlyComments (Substring.full value) | _ => false) l
          | _ => false
        then split (SOME lab) [] r (qs, labs)
        else split (SOME lab) [] r (mk l :: qs, olab :: labs)
      | split olab l (d :: r) qs = split olab (d :: l) r qs
    val (quotes, conjs) = split NONE [] quote ([], [])
    val quote = mkList (inductive_, mkQ "(" :: tl (List.concat quotes) @ [mkQ ")"])
    fun mkStem x = (id, stem ^ x)
    val pat = mkTuple (inductive_, map (mkIdent o mkStem) ["_rules", indSuffix, "_cases"])
    val e = App (App (mkIdent (inductive_, entryPoint), mkString (id, stem)), quote)
    val acc = magicBind (mkStem "_strongind") [valPat inductive_ pat e]
    fun mkExtra _ [] acc = acc
      | mkExtra i (SOME {label = SOME (HOLLabel {tilde_, id}), attrs, ...} :: conjs) acc = let
        val name = case tilde_ of NONE => id | SOME p => (p, stem ^ "_" ^ #2 id)
        val proof = mkHandleHolErr (inductive_,
          App (App (mkIdent (inductive_, "Drule.cj"), mkInt (inductive_, i)),
            mkIdent (mkStem "_rules")))
        val args = mkTuple (inductive_, [mkNameAttrs #2 name attrs, proof])
        val fileline = fileline (#1 name)
        val e = mkLocString (inductive_, "boolLib.save_thm", "boolLib.save_thm_at") fileline
        in mkExtra (i+1) conjs (valPat inductive_ (mkIdent name) (App (e, args)) :: acc) end
      | mkExtra i (_ :: conjs) acc = mkExtra (i+1) conjs acc
    in DecExpansion {orig = dec, result = rev (mkExtra 1 conjs acc)} end
  | expandDec _ (dec as HOLType {overload, type_, id, attrs, bind}) = let
    val inferior = ref false
    val local_ = ref false
    val pp = ref false
    val by_nametype = ref false
    fun f true (_, "inferior") = inferior := true
      | f _ (_, "local") = local_ := true
      | f false (_, "pp") = pp := true
      | f true (_, "by_nametype") = by_nametype := true
      | f _ (p, sk) = parseError (p, p + size sk) ("unexpected attribute '"^sk^"'")
    val _ = Option.app (app (f overload) o #args o #attrs) attrs
    val name = "Parse." ^
      (if !local_ then "temp_" else "") ^
      (if overload then
        (if !inferior then "inferior_" else "") ^
        "overload_on" ^
        (if !by_nametype then "_by_nametype" else "")
       else "type_abbrev" ^ (if !pp then "_pp" else ""))
    val id = case id of QuotedId s => StringConstant s | UnquotedId s => mkString s
    val rhs = case bind of
      NONE => mkFail (type_, "Type/Overload missing body")
    | SOME {exp, ...} => expandExp false exp
    val dec' = valWild type_ (App (mkIdent (type_, name), mkTuple (type_, [id, rhs])))
    in DecExpansion {orig = dec, result = [dec']} end
  | expandDec _ (dec as HOLSimpleThm {triv, theorem_, id, attrs, bind}) = let
    val fileline = fileline (#1 id)
    val e = mkLocString (theorem_, "boolLib.save_thm", "boolLib.save_thm_at") fileline
    val nameAttrs = mkNameAttrs mkKval id (withLocalAttrs theorem_ triv attrs)
    val rhs = case bind of
      NONE => mkFail (theorem_, "Theorem missing body")
    | SOME {exp, ...} => expandExp false exp
    val dec' = valPat theorem_ (mkIdent id) (App (e, mkTuple (theorem_, [nameAttrs, rhs])))
    in DecExpansion {orig = dec, result = [dec']} end
  | expandDec _ (dec as HOLTheoremDecl {
      triv, theorem_, id,
      attrs, colon = _, quote, proof_, tac, qed_ = _, stop}) = let
    val fileline = fileline (#1 id)
    val nameAttrs = mkNameAttrs mkKval id (withLocalAttrs theorem_ triv attrs)
    val quote = expandQuote theorem_ stop quote
    val tac = expandExp false tac
    val tac = case proof_ of SOME {proof_, attrs} => doProofAttrs proof_ attrs tac | _ => tac
    val tac = wrapTac (theorem_, tac)
    val e = mkLocString (theorem_, "Q.store_thm", "Q.store_thm_at") fileline
    val e = App (e, mkTuple (theorem_, [nameAttrs, quote, tac]))
    in DecExpansion {orig = dec, result = [valPat theorem_ (mkIdent id) e]} end
  | expandDec _ (dec as HOLResume {resume_, id, attrs, tac, ...}) = let
    val (label, rest) = case (case attrs of NONE => [] | SOME v => #args (#attrs v)) of
      {key, bind = NONE} :: rest => (key, rest)
    | rest => ((#1 id, ""), rest)
    val subname = pluck (fn {key = (_, "smlname"), ...} => true | _ => false) rest
    val (subname, rest) = case subname of
      NONE =>  (* no smlname attr - return original rest *)
      (Wild (#1 label), rest)
    | SOME ({bind = SOME {vals = [tgt], ...}, ...}, rest) =>  (* ok smlname attr *)
      (mkIdent tgt, rest)
    | SOME ({key = (p, s), ...}, rest)  => (
      (* bad smlname attr: report error, use wildcard and return rest of attributes *)
      parseError (p, p + size s) "unexpected arguments to [smlname] attribute";
      (Wild (#1 label), rest))
    val e = mkIdent (resume_, "markerLib.resume")
    val e = App (e, mkRecord (resume_, [
      mkLabEq (resume_, "label_name", mkString label),
      mkLabEq (resume_, "suspension_name", mkString id)]))
    val e = App (e, wrapTac (resume_, doProofKvals resume_ rest (expandExp false tac)))
    in DecExpansion {orig = dec, result = [valPat resume_ subname e]} end
  | expandDec _ (dec as HOLFinalise {finalise_, id, attrs, ...}) = let
    val fileline = fileline (#1 id)
    val e = mkLocString' (finalise_, "boolLib.finalise_suspended_thm") fileline
    val e = App (e, mkNameAttrs mkKval id attrs)
    in DecExpansion {orig = dec, result = [valPat finalise_ (mkIdent id) e]} end

  | expandDec _ (dec as DecBad {start, ...}) =
    DecExpansion {orig = dec, result = [valWild start (mkFail (start, "malformed"))]}
  | expandDec top (DecExpansion {orig, result}) =
    DecExpansion {orig = orig, result = map (expandDec top) result}

and expandFunArg (ArgIdent {strid, ty}) = let
    val ty = Option.map (fn {colon, sigexp} => {colon = colon, sigexp = expandSigExp sigexp}) ty
    in ArgIdent {strid = strid, ty = ty} end
  | expandFunArg (ArgSpec spec) = ArgSpec (map (expandDec false) spec)

and expandSigExp (s as SigIdent _) = s
  | expandSigExp (Spec {sig_, spec, end_, stop}) =
    Spec {sig_ = sig_, spec = map (expandDec false) spec, end_ = end_, stop = stop}
  | expandSigExp (WhereType {sigexp, where_, elems}) =
    WhereType {sigexp = expandSigExp sigexp, where_ = where_, elems = elems}

and expandStrExp (s as StrIdent _) = s
  | expandStrExp (StrStruct {struct_, strdec, end_, stop}) =
    StrStruct {struct_ = struct_, strdec = map (expandDec false) strdec, end_ = end_, stop = stop}
  | expandStrExp (StrConstraint {strexp, kind}) =
    StrConstraint {strexp = expandStrExp strexp, kind = kind}
  | expandStrExp (FunAppExp {funid, lparen, strexp, rparen, stop}) =
    FunAppExp {funid = funid, lparen = lparen,
      strexp = expandStrExp strexp, rparen = rparen, stop = stop}
  | expandStrExp (FunAppDec {funid, lparen, strdec, rparen, stop}) =
    FunAppDec {funid = funid, lparen = lparen,
      strdec = map (expandDec false) strdec, rparen = rparen, stop = stop}
  | expandStrExp (StrLetInEnd {let_, strdec, in_, strexp, end_, stop}) =
    StrLetInEnd {let_ = let_, strdec = map (expandDec false) strdec, in_ = in_,
      strexp = expandStrExp strexp, end_ = end_, stop = stop}

in expandDec true end

end;
