structure mungeTools :> mungeTools =
struct

open Lib Feedback HolKernel Parse boolLib

datatype command = Theorem | Term | Type
datatype opt = Turnstile | Case | TT | Def | SpacedDef | AlignedDef
             | TypeOf | TermThm
             | Indent of int * bool
                 (* true: add spaces; false: just alter block indent *)
             | NoSpec
             | NoDefSym
             | Inst of string * string
             | OverrideUpd of (string * int) * string
             | Overload of string * string
             | TraceSet of string * int
             | NoTurnstile | Width of int
             | Mathmode of string | NoMath
             | AllTT | ShowTypes of int
             | Conj of int
             | Rule | StackedRule | IndRules
             | RuleName of string
             | NoDollarParens
             | Merge | NoMerge
             | Unoverload of string
             | Depth of int

val numErrors = ref 0
type posn = int * int

fun inc ir = (ir := !ir + 1)
fun warn ((l,c), s) = (TextIO.output(TextIO.stdErr,
                                     Int.toString l ^ "." ^ Int.toString c ^
                                     ": " ^ s ^ "\n");
                       inc numErrors;
                       TextIO.flushOut TextIO.stdErr)
fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             TextIO.flushOut TextIO.stdErr;
             OS.Process.exit OS.Process.failure)
fun usage() =
    die ("Usage:\n  "^
         CommandLine.name()^
         " [-w<linewidth>] [-m[<math-spacing>]] [--nomergeanalysis] " ^
         "[overridesfile]\nor\n  "^
         CommandLine.name()^" -index filename")

fun isNotChar a b = a <> b

fun stringOpt pos tok =
  let
    open Substring
    fun rmws s = s |> dropl Char.isSpace |> dropr Char.isSpace
    val ss = rmws (full tok)
    val s = string ss
  in case s of
    "|-" => SOME Turnstile
  | "aligneddef" => SOME AlignedDef
  | "alltt" => SOME AllTT
  | "case" => SOME Case
  | "def" => SOME Def
  | "indrules" => SOME IndRules
  | "K" => SOME TermThm
  | "m" => SOME (Mathmode "")
  | "merge" => SOME Merge
  | "nodefsym" => SOME NoDefSym
  | "nodollarparens" => SOME NoDollarParens
  | "nomerge" => SOME NoMerge
  | "nomath" => SOME NoMath
  | "nosp" => SOME NoSpec
  | "nostile" => SOME NoTurnstile
  | "of" => SOME TypeOf
  | "rule" => SOME Rule
  | "showtypes" => SOME (ShowTypes 1)
  | "spaceddef" => SOME SpacedDef
  | "stackedrule" => SOME StackedRule
  | "tt" => SOME TT
  | ">>" => SOME (Indent (2, true))
  | ">>~" => SOME (Indent (2, false))
  | _ => let val (pfx,sfx) = splitl (isNotChar #"/") ss in
    if isPrefix "///" sfx then SOME (OverrideUpd ((string (rmws pfx), size sfx - 3), string (rmws (triml 3 sfx))))
    else if isPrefix "//" sfx then SOME (Overload (string (rmws pfx), string (rmws (triml 2 sfx))))
    else if isPrefix "/" sfx then SOME (Inst (string (rmws pfx), string (rmws (triml 1 sfx))))
    else let
      val (spfx,ssfx) = splitl (isNotChar #"=") ss
      val pfx = rmws spfx
      val sfx = string (rmws (triml 1 ssfx))
      fun numarg cont arg =
        case Int.fromString arg of
          SOME i => cont i
        | NONE => (warn(pos, s ^ " option invalid, equal sign should be followed by a number"); NONE)
    in if isPrefix "=" ssfx then
      case string pfx of
        "rulename" => SOME (RuleName sfx)
      | "width" => numarg (fn i => SOME (Width i)) sfx
      | "depth" => numarg (fn i => SOME (Depth i)) sfx
      | "showtypes" => numarg (fn i => SOME (ShowTypes i)) sfx
      | "conj" => numarg (fn i => SOME (Conj i)) sfx
      | "m" => SOME (Mathmode sfx)
      | ">>" => numarg (fn i => SOME (Indent (i, true))) sfx
      | ">>~" => numarg (fn i => SOME (Indent (i, false))) sfx
      | _ => if isPrefix "tr'" pfx andalso isSuffix "'" pfx then
          numarg (fn i => SOME (TraceSet (string (trimr 1 (triml 3 pfx)), i))) sfx
        else (warn (pos, s ^ " option invalid"); NONE)
    else if isPrefix "-" ss then SOME (Unoverload (string (triml 1 ss)))
    else (warn (pos, s ^ " option invalid"); NONE)
    end
    end
  end


type override_map = (string,(string * int))Binarymap.dict
fun read_overrides fname = let
  val istrm = TextIO.openIn fname
              handle _ => usage()
  fun recurse count acc =
      case TextIO.inputLine istrm of
        NONE => acc
      | SOME line => let
          open Substring
          val ss = full line
          val ss = dropl Char.isSpace (dropr Char.isSpace ss)
          val acc' = let
          in
            if size ss = 0 then acc
            else let
                val (word1, ss) = splitl (not o Char.isSpace) ss
                val word1 = string word1
                val ss = dropl Char.isSpace ss
                val (num, ss) = splitl (not o Char.isSpace) ss
                val word2 = string (dropl Char.isSpace ss)
              in
                case Int.fromString (string num) of
                  NONE => (warn ((count,0),
                                 fname ^ "(overrides file): --" ^
                                 string (dropr Char.isSpace (full line)) ^
                                 "-- couldn't decode size number. Ignoring.");
                           acc)
                | SOME n => let
                  in
                    case Binarymap.peek(acc, word1) of
                      NONE => Binarymap.insert(acc, word1, (word2, n))
                    | SOME _ => (warn ((count,0),
                                       fname ^ " rebinds " ^ word1);
                                 Binarymap.insert(acc, word1, (word2, n)))
                  end
              end
          end
        in
          recurse (count + 1) acc'
        end
in
  recurse 1 (Binarymap.mkDict String.compare) before
  TextIO.closeIn istrm
end

structure OptSet : sig
  type elem type set
  val empty : set
  val add : elem -> set -> set
  val addList : elem list -> set -> set
  val has : elem -> set -> bool
  val listItems : set -> elem list
  val fold : (elem * 'a -> 'a) -> 'a -> set -> 'a
end where type elem = opt = struct
  type elem = opt
  type set = elem list
  val empty = []
  fun add e s = e::s
  fun addList s1 s2 = s1 @ s2
  fun has e s = Lib.mem e s
  fun listItems l = l
  val fold = List.foldl
end

type optionset = OptSet.set

fun optset_width s = get_first (fn Width i => SOME i | _ => NONE) s
fun optset_depth s = get_first (fn Depth i => SOME i | _ => NONE) s
fun spaces 0 = ""
  | spaces 1 = " "
  | spaces 2 = "  "
  | spaces 3 = "   "
  | spaces 4 = "    "
  | spaces n = CharVector.tabulate(n, (fn _ => #" "))
fun optset_indent s =
    case get_first (fn Indent i => SOME i | _ => NONE) s of
      NONE => (0, PP.add_string "")
    | SOME (i,b) =>
        (i, if b then PP.add_string (spaces i) else PP.add_string "")

fun optset_conjnum s = get_first (fn Conj i => SOME i | _ => NONE) s
fun optset_mathmode s = get_first (fn Mathmode s => SOME s | _ => NONE) s
fun optset_showtypes s = get_first (fn ShowTypes i => SOME i | _ => NONE) s
fun optset_rulename s = get_first (fn RuleName s => SOME s | _ => NONE) s
fun optset_nomath s = OptSet.has NoMath s

val optset_unoverloads =
  OptSet.fold (fn
    (Unoverload s,l) => if String.isPrefix ":" s then l else s :: l
  | (_,l) => l) []
val optset_unabbrevs =
  OptSet.fold (fn
    (Unoverload s,l) => if String.isPrefix ":" s then s :: l else l
  | (_,l) => l) []

val optset_overloads =
  OptSet.fold (fn
    (Overload (n,t),l) => if String.isPrefix ":" t then l else (n,Parse.Term [QUOTE t]) :: l
  | (_,l) => l) []
val optset_abbrevs =
  OptSet.fold (fn
    (Overload (n,t),l) => if String.isPrefix ":" t then (n,Parse.Type [QUOTE t]) :: l else l
  | (_,l) => l) []

fun optset_traces opts f =
    OptSet.fold (fn (e, f) => case e of TraceSet p => trace p f | _ => f) f opts

val HOL = !EmitTeX.texPrefix
val user_overrides = ref (Binarymap.mkDict String.compare)

fun diag s = (TextIO.output(TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)
fun overrides s = Binarymap.peek (!user_overrides, s)

fun isChar x y = x = y

fun mkinst loc opts tm = let
  val insts = List.mapPartial (fn Inst(s1,s2) => SOME (s1,s2) | _ => NONE)
                              (OptSet.listItems opts)
  val (tytheta,insts) = let
    fun foldthis ((nm1, nm2), (tyacc, instacc)) =
        if CharVector.sub(nm1,0) = #":" then
          if CharVector.sub(nm2,0) = #":" then
            ((Parse.Type [QUOTE nm2] |-> Parse.Type [QUOTE nm1]) :: tyacc,
             instacc)
          else (warn (loc, "Type substitution mal-formed"); die "")
        else if CharVector.sub(nm2,0) = #":" then
          (warn (loc, "Type substitution mal-formed"); die "")
        else (tyacc, (nm1,nm2)::instacc)
  in
    List.foldl foldthis ([],[]) insts
  end
  val tm = Term.inst tytheta tm
  val vs = FVL [tm] empty_tmset
  fun foldthis (v, acc) = let
    val (n,ty) = dest_var v
  in
    Binarymap.insert(acc,n,ty)
  end
  val vtypemap = HOLset.foldl foldthis (Binarymap.mkDict String.compare) vs
  fun foldthis ((nm1,nm2),acc) = let
    val ty = Binarymap.find(vtypemap, nm2)
  in
    (mk_var(nm2,ty) |-> mk_var(nm1,ty)) :: acc
  end handle Binarymap.NotFound => acc
in
  (insts, tytheta, foldr foldthis [] insts)
end

fun mk_s2smap pairs = let
  fun foldthis ((nm1,nm2), acc) = Binarymap.insert(acc, nm2, nm1)
  val m = Binarymap.mkDict String.compare
in
   List.foldl foldthis m pairs
end

fun rename m t = let
  val (v0, _) = dest_abs t
  val (vnm, vty) = dest_var v0
in
  case Binarymap.peek (m, vnm) of
    NONE => NO_CONV t
  | SOME newname => ALPHA_CONV (mk_var(newname,vty)) t
end

fun depth1_conv c t =
    (TRY_CONV c THENC TRY_CONV (SUB_CONV (depth1_conv c))) t

fun updatef ((k, v), f) x = if x = k then SOME v else f x

fun do_thminsts loc opts th = let
  val (insts, tytheta, theta) = mkinst loc opts (concl th)
  val th = INST_TYPE tytheta th
  val m = mk_s2smap insts
  val th = if null theta then th else INST theta th
in
  CONV_RULE (depth1_conv (rename m)) th
end

fun do_tminsts loc opts tm = let
  val (insts, tytheta, theta) = mkinst loc opts tm
  val tm = Term.inst tytheta tm
  val tm = if null theta then tm else Term.subst theta tm
  val m = mk_s2smap insts
in
  if null insts then tm
  else
    rhs (concl (QCONV (depth1_conv (rename m)) tm))
end

local
  val sm_t = prim_mk_const{Name = "stmarker", Thy = "marker"}
  val exn = mk_HOL_ERR "EmitTeX" "replace_topeq"
                       "Definition clause not an equality"
in
fun replace_topeq tm =
    let val (eqt,l,r) =
            case strip_comb tm of
                (f, [x,y]) => if same_const boolSyntax.equality f then (f, x, y)
                              else raise exn
              | _ => raise exn
    in
      list_mk_comb(mk_icomb(sm_t, eqt), [l,r])
    end
end

local
  open EmitTeX PP
  val _ = set_trace "EmitTeX: print datatype names as types" 1
  exception BadSpec
  fun getThm spec = let
    val (theory,theorem) =
        case String.tokens (isChar #".") spec of
            [thy,th] => (thy,th)
          | _ => raise BadSpec
  in
    DB.fetch theory theorem
  end
  fun block_list begb pfun newl xs = begb (pr_list pfun [newl] xs)
  type arg = {commpos : posn, argpos : posn, command : command,
              options : optionset, argument : string}
  val B = block CONSISTENT 0
  val nothing = B []
in
  fun replacement (argument:arg as {commpos = pos, argument = spec,...}) =
  let
    val {argpos = (argline, argcpos), command, options = opts, ...} = argument
    val alltt = OptSet.has AllTT opts orelse
                (command = Theorem andalso not (OptSet.has TT opts))
    val rulep = OptSet.has Rule opts orelse OptSet.has StackedRule opts
    fun rule_print printer term = let
      val (hs, c) = let
        val (h, c) = dest_imp term
      in
        (strip_conj h, c)
      end handle HOL_ERR _ => ([], term)
      open Portable
      fun addz s = add_stringsz (s, 0)
      val (sep,hypbegin,hypend) =
          if OptSet.has StackedRule opts then
            (addz "\\\\", addz "\\begin{array}{c}", addz "\\end{array}")
          else
            (addz "&", nothing, nothing)
      val rulename =
          case optset_rulename opts of
              NONE => nothing
            | SOME s => B [addz"[\\HOLRuleName{", addz s, addz"}]"]
    in
      B [
        addz "\\infer", rulename, addz "{\\HOLinline{",
        printer c,
        addz "}}{",
        hypbegin,
        B (
          pr_list (fn t => B [addz "\\HOLinline{", printer t, addz "}"])
                  [sep] hs
        ),
        hypend, addz "}"
      ]
    end

    fun modify_grammar unoverloads unabbrevs overloads abbrevs f = let
      val oldtyg = type_grammar()
      val oldtmg = term_grammar()
      val _ = List.app temp_clear_overloads_on unoverloads
      val _ = List.map hide unoverloads
      val _ = List.app temp_disable_tyabbrev_printing unabbrevs
      val _ = List.app temp_type_abbrev_pp abbrevs
      val _ = List.app temp_overload_on overloads
      val newtmg = term_grammar()
      val newtyg = type_grammar()
    in
      (fn x => (temp_set_grammars(newtyg,newtmg);
                f x before temp_set_grammars(oldtyg,oldtmg)))
    end

    fun optprintermod f =
        f |> (case optset_showtypes opts of
                NONE => trace ("types", 0)
              | SOME i => trace ("types", i))
          |> (case optset_depth opts of
                NONE => (fn f => f)
              | SOME i => Lib.with_flag (Globals.max_print_depth, i))
          |> (if OptSet.has NoDollarParens opts then
                trace ("EmitTeX: dollar parens", 0)
              else
                trace ("EmitTeX: dollar parens", 1))
          |> (if OptSet.has NoMerge opts then
                trace ("pp_avoids_symbol_merges", 0)
              else (fn f => f))
          |> (if OptSet.has Merge opts then
                trace ("pp_avoids_symbol_merges", 1)
              else (fn f => f))
          |> (modify_grammar (optset_unoverloads opts) (optset_unabbrevs opts)
                             (optset_overloads opts) (optset_abbrevs opts))
          |> optset_traces opts

    val overrides = let
      fun foldthis (opt, acc) =
          case opt of
              OverrideUpd (newsz,old) => updatef ((old,newsz), acc)
            | _ => acc
    in
      OptSet.fold foldthis overrides opts
    end
    fun stdtermprint t = optprintermod (raw_pp_term_as_tex overrides) t

    fun opttyprintermod f =
      f |> (modify_grammar (optset_unoverloads opts) (optset_unabbrevs opts)
                           (optset_overloads opts) (optset_abbrevs opts))

    fun stdtypeprint t = opttyprintermod (raw_pp_type_as_tex overrides) t

    val start1 =
        if not alltt andalso not rulep then add_string "\\HOLinline{"
        else nothing
    val parse_start = " (*#loc "^ Int.toString argline ^ " " ^
                      Int.toString argcpos ^"*)"
    val QQ = QUOTE
    val result =
      case command of
        Theorem => let
          val thm = getThm spec
          val thm =
              if OptSet.has NoSpec opts then thm
              else
                case optset_conjnum opts of
                  NONE => SPEC_ALL thm
                | SOME i => List.nth(map SPEC_ALL (CONJUNCTS (SPEC_ALL thm)),
                                     i - 1)
                  handle Subscript =>
                         (warn(pos,
                               "Theorem "^spec^
                               " does not have a conjunct #" ^
                               Int.toString i);
                          SPEC_ALL thm)
          val thm = do_thminsts pos opts thm
          val (ind,iact) = optset_indent opts
          fun ind_bl p = block CONSISTENT ind [iact, p]
        in
          if OptSet.has Def opts orelse OptSet.has SpacedDef opts orelse
             OptSet.has AlignedDef opts
          then let
              val newline = if OptSet.has SpacedDef opts then
                              B [add_newline, add_newline]
                            else add_newline
              val m = if OptSet.has NoDefSym opts then (fn t => t)
                      else replace_topeq
              val lines = thm |> CONJUNCTS |> map (m o concl o SPEC_ALL)
              val pr =
                  if OptSet.has AlignedDef opts then
                    let val overrides' =
                            updatef(("(HOLDefEquality)",
                                     ("&\\HOLTokenDefEquality{}&", 1)),
                                    overrides)
                    in
                      optprintermod (raw_pp_term_as_tex overrides')
                    end
                  else
                    stdtermprint
            in
              ind_bl (
                block_list (block INCONSISTENT 0) pr newline lines
              )
            end
          else if OptSet.has IndRules opts then
            ind_bl (
              block_list (block INCONSISTENT 0) (rule_print stdtermprint) add_newline
                (map (concl o SPEC_ALL) (CONJUNCTS thm)))
          else if rulep then ind_bl (rule_print stdtermprint (concl thm))
          else let
              val base = raw_pp_theorem_as_tex overrides
              val printer = optprintermod base
              val printer =
                  if OptSet.has NoTurnstile opts then
                    trace ("EmitTeX: print thm turnstiles", 0) printer
                  else printer
            in
              ind_bl (printer thm)
            end
        end
      | Term => let
          val term = if OptSet.has TermThm opts then
                       spec |> getThm |> concl |> rand |> do_tminsts pos opts
                     else if OptSet.has Case opts then
                       let
                         open Preterm errormonad
                         val a = Absyn [QQ parse_start, QQ spec]
                         val tm_M =
                             absyn_to_preterm a >-                (fn ptm0 =>
                             typecheck_phase1 NONE ptm0 >>
                             overloading_resolution ptm0 >-       (fn (pt,b) =>
                             report_ovl_ambiguity b >>
                             to_term pt))
                         val tm = smash tm_M Pretype.Env.empty
                        in
                          do_tminsts pos opts tm
                        end
                     else
                         Parse.Term [QQ parse_start, QQ spec]
                                    |> do_tminsts pos opts
          val (ind,iact) = optset_indent opts
          val s2 = if OptSet.has Turnstile opts then
                        B [add_stringsz ("\\"^HOL^"TokenTurnstile", 2),
                           add_string " "]
                   else nothing
        in
          if rulep then
            block CONSISTENT ind [iact, s2, rule_print stdtermprint term]
          else block CONSISTENT ind [iact, s2, stdtermprint term]
        end
      | Type => let
          val typ = if OptSet.has TypeOf opts
                         then Parse.Term [QQ parse_start, QQ spec]
                              |> do_tminsts pos opts
                              |> Term.type_of
                    else Parse.Type [QQ parse_start, QQ spec]
          val (ind, iact) = optset_indent opts
        in
          block CONSISTENT ind [iact, stdtypeprint typ]
        end
    val final = if not alltt andalso not rulep then add_string "}"
                else nothing
  in
    B [start1, result, final]
  end handle
      BadSpec => (warn (pos, spec ^ " does not specify a theorem"); nothing)
    | HOL_ERR e => (warn (pos, !Feedback.ERR_to_string e); nothing)
    | e => (warn (pos, "Unknown exception: "^General.exnMessage e); nothing)
end

fun parseOpts pos opts = let
  val toks = String.tokens (isChar #",") opts
  val opts = List.mapPartial (stringOpt pos) toks
in
  OptSet.addList opts OptSet.empty
end

end ;
