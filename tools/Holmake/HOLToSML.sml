structure HOLToSML = struct
open HOLAst

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
    | reord (LabAs {id, ty, aspat} :: ls) dot acc = let
      val aspat = Option.map (fn {as_, exp} => {as_ = as_, exp = f exp}) aspat
      fun typed exp NONE = exp
        | typed exp (SOME {colon, ty}) = Typed {exp = exp, colon = colon, ty = ty}
      val lab = if pat then LabAs {id = id, ty = ty, aspat = aspat} else
        case aspat of
          NONE => LabEq {lab = id, eq = #1 id, exp = typed (mkIdent id) ty}
        | SOME {as_, exp} => LabEq {lab = id, eq = as_, exp = typed exp ty}
      in reord ls dot (lab :: acc) end
  val elems = {args = reord args NONE [], delims = delims, stop = stop1}
  in {left = left, elems = elems, right = right, stop = stop} end

fun mkLocPragma line col s =
  concat [" (*#loc ", Int.toString (line + 1), " ", Int.toString (col + 1), "*)", s]

fun mkLocString p file line =
  App (mkIdent (p, "DB_dtype.mkloc"),
    mkTuple (p, [mkString (p, file), mkInt (p, line+1), mkIdent (p, "true")]))

val canBindStr = true (* TODO: make false on mosml *)

fun valPat pos pat e = let
  val s = {rec_ = NONE, pat = pat, eq = SOME {eq = pos, exp = e}}
  in DecVal {val_ = pos, tyvars = Empty, elems = {args = [s], delims = [], stop = pos}} end

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

fun expandDec {parseError, quietOpen} = let

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
    LetInEnd {let_ = let_, dec = expandDecs false dec [], in_ = in_,
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
  | expandExp _ (IfThenElse {if_, exp1, then_, exp2, else_}) = let
    val exp1 = expandExp false exp1
    val exp2 = expandExp false exp2
    val else_ = case else_ of
      NONE => SOME {else_ = if_, exp3 = Unit {left = if_, right = if_}}
    | SOME {else_, exp3} => SOME {else_ = else_, exp3 = expandExp false exp3}
    in IfThenElse {if_ = if_, exp1 = exp1, then_ = then_, exp2 = exp2, else_ = else_} end
  | expandExp _ (While {while_, exp1, do_, exp2}) =
    While {while_ = while_, exp1 = expandExp false exp1, do_ = do_, exp2 = expandExp false exp2}
  | expandExp _ (Case {case_, exp, of_, elems, stop}) = let
    val exp = expandExp false exp
    val p = Option.getOpt (of_, case_)
    in Case {case_ = case_, exp = exp, of_ = of_, elems = expandArms p elems, stop = stop} end
  | expandExp _ (Fn {fn_, elems, stop}) = Fn {fn_ = fn_, elems = expandArms fn_ elems, stop = stop}

  | expandExp _ (HOLFullQuote {head, type_q, quote, stop, ...}) = let
    val id = (#1 head, case type_q of NONE => "Parse.Term" | SOME _ => "Parse.Type")
    in App (mkIdent id, expandQuote (#1 head) stop quote) end
  | expandExp _ (HOLQuote {head, quote, stop, ...}) = expandQuote (#1 head) stop quote
  | expandExp _ (HOLLinePragma {hash_, value, ...}) = IntegerConstant (hash_, Int.toString value)
  | expandExp _ (HOLFilePragma {hash_, value, ...}) = mkString (hash_, value)
  | expandExp _ (HOLLinePragmaWith {hash_, ...}) = Unit {left = hash_, right = hash_}
  | expandExp _ (HOLFilePragmaWith {hash_, ...}) = Unit {left = hash_, right = hash_}
  | expandExp _ (EmptyExp p) = Unit {left = p, right = p}
  | expandExp _ (BadExp {start = p, ...}) = mkFail (p, "malformed")

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
    | go (QuoteLiteral {line, col, value} :: rest) acc = let
      val s = mkLocPragma line col (Substring.string value)
      in go rest (App (mkIdent (start, "QUOTE"), mkString (start, s)) :: acc) end
    | go (QuoteAntiq {exp, ...} :: rest) acc =
      go rest (App (mkIdent (start, "ANTIQUOTE"), expandExp false exp) :: acc)
    | go (DefinitionLabel _ :: _) _ = raise Unreachable
  in go toks [] end

and expandQuote start stop toks = let
  val elems = {args = expandQuoteCore start toks, delims = [], stop = stop}
  in List {left = start, elems = elems, right = NONE, stop = stop} end

and expandDecs _ [] acc = rev acc
  | expandDecs top (dec :: rest) acc = expandDecs top rest (expandDec top dec acc)

and expandDec _ (DecSemi _) acc = acc
  | expandDec _ (DecVal {val_, tyvars, elems}) acc = let
    fun f {rec_, pat, eq} = let
      val pat = expandExp true pat handle HasOrPat => let
        val (start, stop) = expSpan pat
        val _ = parseError (start, stop) "or patterns not supported here"
        in BadExp {start = start, stop = stop} end
      val eq = Option.map (fn {eq, exp} => {eq = eq, exp = expandExp false exp}) eq
      in {rec_ = rec_, pat = pat, eq = eq} end
    in DecVal {val_ = val_, tyvars = tyvars, elems = mapDelim f elems} :: acc end
  | expandDec _ (DecFun {fun_, tyvars, fvalbind}) acc = let
    val fvalbind = mapDelim (expandFunBranches fun_) fvalbind
    in DecFun {fun_ = fun_, tyvars = tyvars, fvalbind = fvalbind} :: acc end
  | expandDec _ (dec as DecType _) acc = dec :: acc
  | expandDec _ (dec as DecEqtype _) acc = dec :: acc
  | expandDec _ (dec as DecDatatype _) acc = dec :: acc
  | expandDec _ (dec as DecAbstype _) acc = dec :: acc
  | expandDec _ (dec as DecException _) acc = dec :: acc
  | expandDec top (DecLocal {local_, dec1, in_, dec2, end_, stop}) acc =
    DecLocal {local_ = local_, dec1 = expandDecs false dec1 [], in_ = in_,
      dec2 = expandDecs top dec2 [], end_ = end_, stop = stop} :: acc
  | expandDec _ (dec as DecOpen _) acc = dec :: acc
  | expandDec _ (dec as DecInfix _) acc = dec :: acc
  | expandDec _ (dec as DecInfixr _) acc = dec :: acc
  | expandDec _ (dec as DecNonfix _) acc = dec :: acc
  | expandDec _ (DecStructure {structure_, elems}) acc = let
    fun f {id, constraint, bind} = let
      val bind = Option.map (fn {eq, strexp} => {eq = eq, strexp = expandStrExp strexp}) bind
      in {id = id, constraint = constraint, bind = bind} end
    in DecStructure {structure_ = structure_, elems = mapDelim f elems} :: acc end
  | expandDec _ (DecSignature {signature_, elems}) acc = let
    fun f {eq, sigexp} = {eq = eq, sigexp = expandSigExp sigexp}
    fun g {id, bind} = {id = id, bind = Option.map f bind}
    in DecSignature {signature_ = signature_, elems = mapDelim g elems} :: acc end
  | expandDec _ (DecInclude {include_, sigexps}) acc =
    DecInclude {include_ = include_, sigexps = map expandSigExp sigexps} :: acc
  | expandDec _ (dec as Sharing _) acc = dec :: acc
  | expandDec _ (DecFunctor {functor_, elems}) acc = let
    fun f {id, lparen, funarg, rparen, constraint, bind} = let
      val funarg = expandFunArg funarg
      val bind = Option.map (fn {eq, strexp} => {eq = eq, strexp = expandStrExp strexp}) bind
      in {id = id, lparen = lparen, funarg = funarg,
          rparen = rparen, constraint = constraint, bind = bind} end
    in DecFunctor {functor_ = functor_, elems = mapDelim f elems} :: acc end
  | expandDec top (DecExp e) acc = let
    val p = expStart e
    in valPat p (if top then mkIdent (p, "it") else Wild p) (expandExp false e) :: acc end

  | expandDec _ (HOLTheory {theory_, id, attrs, elems, ...}) acc = let
    val bare = ref false
    val _ = app (fn
        {key = (_, "bare"), bind = NONE} => bare := true
      | {key = (p, s), ...} => parseError (p, p + size s) "unknown theory attribute"
      ) (case attrs of NONE => [] | SOME v => #args (#attrs v))
    val grammar = ref []
    fun finish (NONE, acc) = acc
      | finish (SOME (false, ns), acc) =
        DecSemi theory_ :: DecOpen {open_ = theory_, elems = rev ns} :: acc
      | finish (SOME (true, ns), acc) = DecSemi theory_ :: DecLocal {
        local_ = theory_, dec1 = [DecOpen {open_ = theory_, elems = rev ns}],
        in_ = SOME theory_, dec2 = [], end_ = SOME theory_, stop = theory_} :: acc
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
          val s = {id = tgt, constraint = NONE, bind = SOME {eq = #1 tgt, strexp = StrIdent id'}}
          val elems = {args = [s], delims = [], stop = #1 tgt}
          val d = DecStructure {structure_ = #1 tgt, elems = elems}
          in (NONE, d :: finish acc) end) acc (rev (!aliases))
        in processList isThy thys ls acc end
    val lhs = if !bare then NONE else SOME (false,
      map (fn s => (theory_, s)) ["Parse", "bossLib", "boolLib", "HolKernel"])
    val acc = if quietOpen then
      case process elems (lhs, []) of
        [] => acc
      | decs => let
        val unit = Unit {left = theory_, right = theory_}
        fun f x acc = DecSemi theory_ :: valWild theory_ (App (mkIdent (theory_, x), unit)) :: acc
        val acc = DecSemi theory_ :: decs @ f "HOL_Interactive.start_open" acc
        in f "HOL_Interactive.end_open" acc end
    else process elems (lhs, acc)
    val acc = valWild theory_ (App (mkIdent (theory_, "Theory.new_theory"), mkString id)) :: acc
    val acc = if !bare then acc else
      valWild theory_ (App (mkIdent (theory_, "Parse.set_grammar_ancestry"),
        mkList (theory_, rev (!grammar)))) :: acc
    in acc end
  | expandDec _ (HOLDefinition {
      definition_, id as (_, name), fileline = (file, (_, line, _)),
      attrs, colon = _, quote, termination, end_ = _, stop}) acc = let
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
    val e =
      if file = "" then mkIdent (definition_, "TotalDefn.qDefine")
      else App (mkIdent (definition_, "TotalDefn.located_qDefine"),
        mkLocString definition_ file line)
    val e = App (e, mkNameAttrs mkKval id attrs)
    val e = App (e, expandQuote definition_ stop quote)
    val e = App (e, case termination of
      NONE => mkIdent (definition_, "NONE")
    | SOME {tac, ...} => App (mkIdent (definition_, "SOME"), expandExp false tac))
    in magicBind indThm (valPat definition_ (mkIdent id) e :: acc) end
  | expandDec _ (HOLDatatype {datatype_, quote, stop, ...}) acc = let
    val e = App (mkIdent (datatype_, "bossLib.Datatype"), expandQuote datatype_ stop quote)
    in valWild datatype_ e :: acc end
  | expandDec _ (HOLQuoteDecl {quote_, id, bind, colon = _, quote, end_ = _, stop}) acc = let
    val (pat, e) = case bind of
      NONE => (Wild (#1 id), mkIdent id)
    | SOME {exp, ...} => (mkIdent id, expandExp false exp)
    in valPat quote_ pat (App (e, expandQuote quote_ stop quote)) :: acc end
  | expandDec _ (HOLInductiveDecl {co, inductive_, id = (id, stem), quote, ...}) acc = let
    val (entryPoint, indSuffix) =
      if co then ("CoIndDefLib.xHol_coreln", "_coind") else ("IndDefLib.xHol_reln", "_ind")
    fun mkQ s = App (mkIdent (inductive_, "QUOTE"), mkString (inductive_, s))
    val frag = mkQ ") /\\\\ ("
    fun mk l = frag :: expandQuoteCore inductive_ (rev l)
    fun split olab l [] (qs, labs) = (rev (mk l :: qs), rev (olab :: labs))
      | split olab l (DefinitionLabel lab :: r) (qs, labs) =
        if case olab of
            NONE => List.all
            (fn QuoteLiteral {value,...} => isOnlyComments value | _ => false) l
          | _ => false
        then split (SOME lab) [] r (qs, labs)
        else split (SOME lab) [] r (mk l :: qs, olab :: labs)
      | split olab l (d :: r) qs = split olab (d :: l) r qs
    val (quotes, conjs) = split NONE [] quote ([], [])
    val quote = mkList (inductive_, mkQ "(" :: tl (List.concat quotes) @ [mkQ ")"])
    fun mkStem x = (id, stem ^ x)
    val pat = mkTuple (inductive_, map (mkIdent o mkStem) ["_rules", indSuffix, "_cases"])
    val e = App (App (mkIdent (inductive_, entryPoint), mkString (id, stem)), quote)
    val acc = magicBind (mkStem "_strongind") (valPat inductive_ pat e :: acc)
    fun mkExtra _ [] acc = acc
      | mkExtra i (SOME {label = SOME (HOLLabel {id, tilde_}), attrs, ...} :: conjs) acc = let
        val name = case tilde_ of NONE => id | SOME p => (p, stem ^ "_" ^ #2 id)
        val proof = mkHandleHolErr (inductive_,
          App (App (mkIdent (inductive_, "Drule.cj"), mkInt (inductive_, i)),
            mkIdent (mkStem "_rules")))
        val args = mkTuple (inductive_, [mkNameAttrs #2 id attrs, proof])
        val e = App (mkIdent (inductive_, "boolLib.save_thm"), args)
        in mkExtra (i+1) conjs (valPat inductive_ (mkIdent name) e :: acc) end
      | mkExtra i (_ :: conjs) acc = mkExtra (i+1) conjs acc
    in mkExtra 1 conjs acc end
  | expandDec _ (HOLType {overload, type_, id, attrs, bind}) acc = let
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
    in valWild type_ (App (mkIdent (type_, name), mkTuple (type_, [id, rhs]))) :: acc end
  | expandDec _ (HOLSimpleThm {
      triv, theorem_, id, fileline = (file, (_, line, _)), attrs, bind}) acc = let
    val e =
      if file = "" then mkIdent (theorem_, "boolLib.save_thm")
      else App (mkIdent (theorem_, "boolLib.save_thm_at"), mkLocString theorem_ file line)
    val nameAttrs = mkNameAttrs mkKval id (withLocalAttrs theorem_ triv attrs)
    val rhs = case bind of
      NONE => mkFail (theorem_, "Theorem missing body")
    | SOME {exp, ...} => expandExp false exp
    in valPat theorem_ (mkIdent id) (App (e, mkTuple (theorem_, [nameAttrs, rhs]))) :: acc end
  | expandDec _ (HOLTheoremDecl {
      triv, theorem_, id, fileline = (file, (_, line, _)),
      attrs, colon = _, quote, proof_, tac, qed_ = _, stop}) acc = let
    val nameAttrs = mkNameAttrs mkKval id (withLocalAttrs theorem_ triv attrs)
    val quote = expandQuote theorem_ stop quote
    val tac = expandExp false tac
    val tac = case proof_ of
      SOME {proof_, attrs = SOME {attrs = {args = kv::kvs, ...}, ...}} => let
      val e = mkIdent (proof_, "BasicProvers.with_simpset_updates")
      fun mktm1 {key = (p, key), bind} = let
        val args = case bind of NONE => [] | SOME {vals, ...} => map mkString vals
        val key = case key of
          "exclude_simps" => "simpLib.remove_simps"
        | "exclude_frags" => "simpLib.remove_ssfrags"
        | _ => key
        in App (mkIdent (p, key), mkList (p, args)) end
      fun mktm (kv, e) = Infix {left = e, id = (proof_, "o"), right = mktm1 kv}
      in App (App (e, foldl mktm (mktm1 kv) kvs), tac) end
    | _ => tac
    val dummy = mkIdent (theorem_, "HOL__GOAL__foo")
    val tac = Fn {fn_ = theorem_, elems = [
      {bar = NONE, pat = dummy, arrow = NONE, exp = App (tac, dummy)}], stop = expStop tac}
    val e =
      if file = "" then mkIdent (theorem_, "Q.store_thm")
      else App (mkIdent (theorem_, "Q.store_thm_at"), mkLocString theorem_ file line)
    val e = App (e, mkTuple (theorem_, [nameAttrs, quote, tac]))
    in valPat theorem_ (mkIdent id) e :: acc end

and expandFunArg (ArgIdent {strid, ty}) = let
    val ty = Option.map (fn {colon, sigexp} => {colon = colon, sigexp = expandSigExp sigexp}) ty
    in ArgIdent {strid = strid, ty = ty} end
  | expandFunArg (ArgSpec spec) = ArgSpec (expandDecs false spec [])

and expandSigExp (s as SigIdent _) = s
  | expandSigExp (Spec {sig_, spec, end_, stop}) =
    Spec {sig_ = sig_, spec = expandDecs false spec [], end_ = end_, stop = stop}
  | expandSigExp (WhereType {sigexp, where_, elems}) =
    WhereType {sigexp = expandSigExp sigexp, where_ = where_, elems = elems}

and expandStrExp (s as StrIdent _) = s
  | expandStrExp (StrStruct {struct_, strdec, end_, stop}) =
    StrStruct {struct_ = struct_, strdec = expandDecs false strdec [], end_ = end_, stop = stop}
  | expandStrExp (StrConstraint {strexp, kind}) =
    StrConstraint {strexp = expandStrExp strexp, kind = kind}
  | expandStrExp (FunAppExp {funid, lparen, strexp, rparen, stop}) =
    FunAppExp {funid = funid, lparen = lparen,
      strexp = expandStrExp strexp, rparen = rparen, stop = stop}
  | expandStrExp (FunAppDec {funid, lparen, strdec, rparen, stop}) =
    FunAppDec {funid = funid, lparen = lparen,
      strdec = expandDecs false strdec [], rparen = rparen, stop = stop}
  | expandStrExp (StrLetInEnd {let_, strdec, in_, strexp, end_, stop}) =
    StrLetInEnd {let_ = let_, strdec = expandDecs false strdec [], in_ = in_,
      strexp = expandStrExp strexp, end_ = end_, stop = stop}

in expandDec true end

end;
