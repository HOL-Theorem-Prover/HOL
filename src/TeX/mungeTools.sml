structure mungeTools :> mungeTools =
struct

open Lib Feedback HolKernel Parse boolLib

datatype command = Theorem | Term | Type
datatype opt = Turnstile | Case | TT | Def | SpacedDef | TypeOf | TermThm
             | Indent of int | NoSpec
             | Inst of string * string
             | NoTurnstile | Width of int
             | AllTT | ShowTypes
             | Conj of int
             | Rule | StackedRule

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
fun usage() = die ("Usage:\n  "^CommandLine.name()^" [-w<linewidth>] [overridesfile] or\n"^
                                CommandLine.name()^" -index filename")

fun stringOpt pos s =
  case s of
    "|-" => SOME Turnstile
  | "case" => SOME Case
  | "tt" => SOME TT
  | "alltt" => SOME AllTT
  | "def" => SOME Def
  | "spaceddef" => SOME SpacedDef
  | "of" => SOME TypeOf
  | "K" => SOME TermThm
  | "nosp" => SOME NoSpec
  | "nostile" => SOME NoTurnstile
  | "showtypes" => SOME ShowTypes
  | "rule" => SOME Rule
  | "stackedrule" => SOME StackedRule
  | _ => let
    in
      if String.isPrefix ">>" s then let
          val numpart_s = String.extract(s,2,NONE)
        in
          if numpart_s = "" then SOME (Indent 2)
          else
            case Int.fromString numpart_s of
              NONE => (warn(pos, s ^ " is not a valid option"); NONE)
            | SOME i => if i < 0 then
                          (warn(pos, "Negative indents illegal"); NONE)
                        else SOME (Indent i)
        end
      else if String.isPrefix "width=" s then let
          val numpart_s = String.extract(s,6,NONE)
        in
          case Int.fromString numpart_s of
            NONE => (warn(pos, s ^ " is not a valid option"); NONE)
          | SOME i => SOME (Width i)
        end
      else if String.isPrefix "conj" s then let
          val numpart_s = String.extract(s,4,NONE)
        in
          case Int.fromString numpart_s of
            NONE => (warn(pos, s ^ " is not a valid option"); NONE)
          | SOME i => if i <= 0 then
                        (warn(pos, "Negative/zero conj specs illegal"); NONE)
                      else SOME (Conj i)
        end
      else let
          open Substring
          val ss = full s
          val (pfx,sfx) = position "/" ss
          fun rmws ss = ss |> dropl Char.isSpace |> dropr Char.isSpace |> string
        in
          if size sfx < 2 then (warn (pos, s ^ " is not a valid option"); NONE)
          else SOME (Inst (rmws pfx, rmws (slice(sfx,1,NONE))))
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
end where type elem = opt = struct
  type elem = opt
  type set = elem list
  val empty = []
  fun add e s = e::s
  fun addList s1 s2 = s1 @ s2
  fun has e s = Lib.mem e s
  fun listItems l = l
end

type optionset = OptSet.set

fun optset_width s = get_first (fn Width i => SOME i | _ => NONE) s
fun spaces 0 = ""
  | spaces 1 = " "
  | spaces 2 = "  "
  | spaces 3 = "   "
  | spaces 4 = "    "
  | spaces n = CharVector.tabulate(n, (fn _ => #" "))
fun optset_indent s =
    case get_first (fn Indent i => SOME i | _ => NONE) s of
      NONE => ""
    | SOME i => spaces i

fun optset_conjnum s = get_first (fn Conj i => SOME i | _ => NONE) s

val HOL = !EmitTeX.texPrefix
val user_overrides = ref (Binarymap.mkDict String.compare)


fun overrides s = Binarymap.peek (!user_overrides, s)

fun isChar x y = x = y

fun mkinst loc opts tm = let
  val insts = List.mapPartial (fn Inst(s1,s2) => SOME (s1,s2) | _ => NONE)
                              (OptSet.listItems opts)
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
  (insts, foldr foldthis [] insts)
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

fun do_thminsts loc opts th = let
  val (insts, theta) = mkinst loc opts (concl th)
  val m = mk_s2smap insts
  val th = if null theta then th else INST theta th
in
  CONV_RULE (depth1_conv (rename m)) th
end

fun do_tminsts loc opts tm = let
  val (insts, theta) = mkinst loc opts tm
  val tm = if null theta then tm else Term.subst theta tm
  val m = mk_s2smap insts
in
  if null insts then tm
  else
    rhs (concl (QCONV (depth1_conv (rename m)) tm))
end

local
  open EmitTeX PP
  val _ = set_trace "EmitTeX: print datatype names as types" 1
  exception BadSpec
  fun getThm spec = let
    val [theory,theorem] = String.tokens (isChar #".") spec
  in
    DB.fetch theory theorem
  end handle Bind => raise BadSpec
  fun block_list pps begb pfun newl endb = let
    fun pr [] = ()
      | pr [i] = ( begb pps; pfun pps i; endb pps)
      | pr (i::rst) = ( begb pps; pfun pps i; newl pps; endb pps; pr rst )
  in pr end
  type arg = {commpos : posn, argpos : posn, command : command,
              options : optionset, argument : string}
in
  fun replacement pps (argument:arg as {commpos = pos, argument = spec,...}) =
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
      fun addz s = add_stringsz pps (s, 0)
      val (sep,hypbegin,hypend) =
          if OptSet.has StackedRule opts then
            ((fn () => addz "\\\\"),
             (fn () => addz "\\begin{array}{c}"),
             (fn () => addz "\\end{array}"))
          else
            ((fn () => addz "&"), (fn () => ()), (fn () => ()))
    in
      addz "\\infer{\\HOLinline{";
      printer c;
      addz "}}{";
      hypbegin();
      pr_list (fn t => (addz "\\HOLinline{";
                        printer t;
                        addz "}"))
              sep
              (fn () => ()) hs;
      hypend();
      addz "}"
    end

    fun stdtermprint t = let
      val baseprint = raw_pp_term_as_tex overrides pps
      val printer = if OptSet.has ShowTypes opts then
                      trace ("types", 1) baseprint
                    else trace ("types", 0) baseprint
    in
      printer t
    end

    val () = if not alltt andalso not rulep then add_string pps "\\HOLinline{"
             else ()
    val parse_start = " (*#loc "^ Int.toString argline ^ " " ^
                      Int.toString argcpos ^"*)"
    val QQ = QUOTE
    val () =
      case command of
        Theorem => let
          val thm = do_thminsts pos opts (getThm spec)
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
          val _ = add_string pps (optset_indent opts)
        in
          if OptSet.has Def opts orelse OptSet.has SpacedDef opts then let
              val newline = if OptSet.has SpacedDef opts then
                              (fn pps => (add_newline pps; add_newline pps))
                            else add_newline
              val lines = thm |> CONJUNCTS |> map (concl o SPEC_ALL)
              val printfn = let
                val base = raw_pp_term_as_tex overrides
              in
                if OptSet.has ShowTypes opts then
                  (fn pps => trace ("types", 1) (base pps))
                else (fn pps => trace ("types", 0) (base pps))
              end
            in
              begin_block pps CONSISTENT 0;
              block_list pps
                         (fn pps => begin_block pps INCONSISTENT 0)
                         printfn
                         newline
                         end_block
                         lines;
              end_block pps
            end
          else if rulep then rule_print stdtermprint (concl thm)
          else let
              val base = raw_pp_theorem_as_tex overrides pps
              val printer =
                  if OptSet.has NoTurnstile opts then
                    trace ("EmitTeX: print thm turnstiles", 0) base
                  else base
              val printer =
                  if OptSet.has ShowTypes opts then trace ("types", 1) printer
                  else trace ("types", 0) printer
            in
              printer thm
            end
        end
      | Term => let
          val term = if OptSet.has TermThm opts then
                       spec |> getThm |> concl |> rand |> do_tminsts pos opts
                     else if OptSet.has Case opts
                        then let
                          val ptm0 = Parse.Preterm [QQ parse_start, QQ spec]
                          val () = Preterm.typecheck_phase1 NONE ptm0
                          val ptm = Preterm.overloading_resolution ptm0
                        in
                          Preterm.to_term ptm |> do_tminsts pos opts
                        end
                     else
                         Parse.Term [QQ parse_start, QQ spec]
                                    |> do_tminsts pos opts
          val () = add_string pps (optset_indent opts)
          val () = if OptSet.has Turnstile opts
                      then let in
                        add_stringsz pps ("\\"^HOL^"TokenTurnstile", 2);
                        add_string pps " "
                      end
                   else ()
        in
          if rulep then rule_print stdtermprint term else stdtermprint term
        end
      | Type => let
          val typ = if OptSet.has TypeOf opts
                       then Term.type_of (Parse.Term [QQ parse_start, QQ spec])
                    else Parse.Type [QQ parse_start, QQ spec]
        in
          add_string pps (optset_indent opts);
          raw_pp_type_as_tex overrides pps typ
        end
    val () = if not alltt andalso not rulep then add_string pps "}" else ()
  in () end handle
      BadSpec => warn (pos, spec ^ " does not specify a theorem")
    | HOL_ERR e => warn (pos, !Feedback.ERR_to_string e)
    | e => warn (pos, "Unknown exception: "^General.exnMessage e)
end

fun parseOpts pos opts = let
  val toks = String.tokens (isChar #",") opts
  val opts = List.mapPartial (stringOpt pos) toks
in
  OptSet.addList opts OptSet.empty
end

end ;
