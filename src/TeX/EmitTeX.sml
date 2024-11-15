structure EmitTeX :> EmitTeX =
struct

open HolKernel boolLib;

(* ------------------------------------------------------------------------- *)
(* Configuration                                                             *)
(* ------------------------------------------------------------------------- *)

val texOptions = "11pt, twoside";

val texLinewidth = ref 64;
val texPrefix    = ref "HOL";
val emitTeXDir   = ref "";

val current_theory_name = ref "";
val current_path        = ref Path.currentArc

fun tex_command_escape s =
  String.concat (map
    (fn c =>
       case c of
         #"_" => "XX"
       | #"'" => "YY"
       | #"?" => "QQ"
       | #"!" => "ZZ"
       | #"0" => "Zero"
       | #"1" => "One"
       | #"2" => "Two"
       | #"3" => "Three"
       | #"4" => "Four"
       | #"5" => "Five"
       | #"6" => "Six"
       | #"7" => "Seven"
       | #"8" => "Eight"
       | #"9" => "Nine"
       | _ => String.str c)
    (String.explode s));

fun index_string() =
  "\\index{" ^
    (if !current_theory_name = "" then
       ""
     else
       !current_theory_name ^ " Theory@\\textbf  {" ^
       !current_theory_name ^ " Theory}");

fun prefix_escape s = !texPrefix ^ (tex_command_escape s);

fun prefix_string()     = prefix_escape (!current_theory_name);
fun datatype_prefix()   = prefix_string() ^ "Datatypes";
fun definition_prefix() = prefix_string() ^ "Definitions";
fun theorem_prefix()    = prefix_string() ^ "Theorems";
fun date_prefix()       = prefix_string() ^ "Date";
fun time_prefix()       = prefix_string() ^ "Time";

(* ------------------------------------------------------------------------- *)
(* datatype_theorems : string -> (string * thm) list                         *)
(*   Get a list of datatype theorems in the names theory.                    *)
(*   These have the form |- DATATYPE x                                       *)
(*                                                                           *)
(* non_type_definitions : string -> (string * thm) list                      *)
(*   A version of DB.definitions that filters out definitions created by     *)
(*   Hol_datatype and those containing WFREC.                                *)
(*                                                                           *)
(* non_type_theorems : string -> (string * thm) list                         *)
(*   A version of DB.theorems that filters out theorems created by           *)
(*   Hol_datatype.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun datatype_defns s =
    map (fn x => s ^ x)
      ["_TY_DEF", "_repfns", "_size_def"]

  fun datatype_theorems s =
    "datatype_" ^ s :: map (fn x => s ^ x)
      ["_11", "_Axiom", "_case_cong", "_induction", "_nchotomy"]

  fun enumerate_defns s =
     [s ^ "_BIJ", s ^ "_case", s ^ "_CASE"]

  fun enumerate_thms s =
    ["num2" ^ s ^ "_ONTO", "num2" ^ s ^ "_thm", "num2" ^ s ^ "_11",
     s ^ "2num_ONTO", s ^ "2num_thm", s ^ "2num_11",
     s ^ "_case_def", s ^ "_EQ_" ^ s,
     s ^ "2num_num2" ^ s, "num2" ^ s ^ "_" ^ s ^ "2num"]

  fun record_defns s flds =
    let val (l,r) = Substring.position "brss__" (Substring.full s)
        val big = if Substring.isPrefix "brss__" r then
                    let val n = Substring.string l ^ "brss__sf" ^
                                Substring.string (Substring.slice (r, 6, NONE))
                    in [n, n ^ "_fupd"] end
                  else
                    []
    in
      s :: s ^ "_case_def" :: (big @ List.concat
        (map (fn x => let val y = s ^ "_" ^ x in [y, y ^ "_fupd"] end) flds))
    end

  fun record_thms s =
    ["EXISTS_" ^ s, "FORALL_" ^ s] @
    (map (fn x => s ^ x)
      ["_11", "_accessors", "_accfupds", "_Axiom", "_case_cong",
       "_component_equality", "_fn_updates", "_updates_eq_literal",
       "_fupdcanon", "_fupdcanon_comp", "_fupdfupds", "_fupdfupds_comp",
       "_induction", "_literal_11", "_literal_nchotomy", "_nchotomy"])

  fun type_defn_names thy tyop =
  let val tyinfo = TypeBase.read {Thy = thy, Tyop = tyop} in
    case tyinfo of
      NONE => []
    | SOME x =>
       let val defns =
         case TypeBasePure.fields_of x of
           [] => let val constructors = map (fst o dest_const)
                                            (TypeBasePure.constructors_of x)
                 in
                   case TypeBasePure.one_one_of x of
                     NONE => enumerate_defns tyop @ constructors
                   | SOME _ => tyop ^ "_case_def" :: constructors
                 end
         | flds => record_defns tyop (map fst flds)
       in
         datatype_defns tyop @ defns
       end
  end

  fun type_thm_names thy tyop =
  let val tyinfo = TypeBase.read {Thy = thy, Tyop = tyop} in
    case tyinfo of
      NONE => []
    | SOME x =>
       let val thms =
         case TypeBasePure.fields_of x of
           [] => (case TypeBasePure.one_one_of x of
                   NONE => tyop ^ "_distinct" ::  enumerate_thms tyop
                 | SOME _ => [tyop ^ "_distinct"])
         | flds => record_thms tyop
       in
         datatype_theorems tyop @ thms
       end
  end

  fun datatypes s =
        map snd (filter (fn x => fst x = s)
           (map TypeBasePure.ty_name_of
              (TypeBasePure.listItems (TypeBase.theTypeBase()))))

  fun type_defn_set s =
  let val thm_names = List.concat (map (type_defn_names s) (datatypes s)) in
    Redblackset.addList (Redblackset.empty String.compare, thm_names)
  end

  fun type_thm_set s =
  let val thm_names = List.concat (map (type_thm_names s) (datatypes s)) in
    Redblackset.addList (Redblackset.empty String.compare, thm_names)
  end

  val rec_thm = can (match_term
         ``f = WFREC (a:'a -> 'a -> bool) (b:('a -> 'b) -> 'a -> 'b)``) o
          concl o SPEC_ALL

  val lc = String.map Char.toLower
  fun thm_cmp (a,b) = String.compare (lc (fst a), lc (fst b))
  val thm_sort = Listsort.sort thm_cmp
in
  fun is_datatype_thm thm =
        ((fst o dest_const o fst o dest_comb o concl) thm = "DATATYPE")
             handle HOL_ERR _ => false

  fun datatype_theorems s =
  let val dtype_thms = matchp is_datatype_thm [s]
      fun dtype_name s = String.extract(s, 9, NONE)
  in
    map (fn ((thy,thname), (th,cl,i)) => (dtype_name thname, th)) dtype_thms
  end

  fun non_type_definitions s =
    List.filter (fn (x,y) => not ((String.sub(x, 0) = #" ") orelse
                              Redblackset.member(type_defn_set s, x) orelse
                              rec_thm y))
                (thm_sort (definitions s))

  fun non_type_theorems s =
    List.filter (fn x => not ((String.sub(fst x, 0) = #" ") orelse
                              Redblackset.member(type_thm_set s, fst x)))
                (thm_sort (theorems s))
end;

(* ------------------------------------------------------------------------- *)
(* An emit TeX back end                                                      *)
(* ------------------------------------------------------------------------- *)

fun token_string s = String.concat ["\\", !texPrefix, "Token", s, "{}"];
val KRrecordtypes = ref true
val _ = register_btrace ("EmitTeX: K&R record type defns", KRrecordtypes)

local
  fun greek s = "\\ensuremath{\\" ^ s ^ "}"
  fun subn i  = "\\ensuremath{\\sb{" ^ Int.toString i ^ "}}"

  val dollar_parens = ref true
  val _ = register_btrace ("EmitTeX: dollar parens", dollar_parens)

  fun char_map c =
    case c
    of "\\" => token_string "Backslash"
     | "{"  => token_string "Leftbrace"
     | "}"  => token_string "Rightbrace"
     | "\"" => token_string "DoubleQuote"
     | "&" => "\\&"
     | "%" => "\\%"
     | "#" => "\\#"
     | "$"  => "\\$"
     | "α" => greek "alpha"
     | "β" => greek "beta"
     | "γ" => greek "gamma"
     | "Γ" => greek "Gamma"
     | "δ" => greek "delta"
     | "Δ" => greek "Delta"
     | "ε" => greek "epsilon"
     | "ζ" => greek "zeta"
     | "η" => greek "eta"
     | "θ" => greek "theta"
     | "Θ" => greek "Theta"
     | "ι" => greek "iota"
     | "κ" => greek "kappa"
     | "λ" => greek "lambda"
     | "Λ" => greek "Lambda"
     | "μ" => greek "mu"
     | "ν" => greek "nu"
     | "ξ" => greek "xi"
     | "Ξ" => greek "Xi"
     | "π" => greek "pi"
     | "Π" => greek "Pi"
     | "ρ" => greek "rho"
     | "σ" => greek "sigma"
     | "ς" => greek "varsigma"
     | "Σ" => greek "Sigma"
     | "τ" => greek "tau"
     | "υ" => greek "upsilon"
     | "Υ" => greek "Upsilon"
     | "φ" => greek "varphi" (* U+03C6 *)
     | "ϕ" => greek "phi"    (* U+03D5 *)
     | "Φ" => greek "Phi"    (* U+03A6 *)
     | "χ" => greek "chi"
     | "ψ" => greek "psi"
     | "Ψ" => greek "Psi"
     | "ω" => greek "omega"
     | "Ω" => greek "Omega"
     | "₁" => subn 1
     | "₂" => subn 2
     | "₃" => subn 3
     | "₄" => subn 4
     | "₅" => subn 5
     | "₆" => subn 6
     | "₇" => subn 7
     | "₈" => subn 8
     | "₉" => subn 9
     | "₀" => subn 0
     | c     => c

  fun string_map (s,sz) =
      case Binarymap.peek(TexTokenMap.the_map(), s) of
        SOME {info = result, ...} => result
      | NONE => (UTF8.translate char_map s,
                 case sz of NONE => String.size s | SOME sz => sz)

  fun smap overrides (s,sz) =
      case overrides s of
        NONE => string_map (s,sz)
      | SOME r => r
  fun translate_prime s =
      if s = "'" then "\\prime{}" else
      if s = UnicodeChars.sup_0 then "0" else
      if s = UnicodeChars.sup_1 then "1" else
      if s = UnicodeChars.sup_2 then "2" else
      if s = UnicodeChars.sup_3 then "3" else
      if s = UnicodeChars.sup_4 then "4" else
      if s = UnicodeChars.sup_5 then "5" else
      if s = UnicodeChars.sup_6 then "6" else
      if s = UnicodeChars.sup_7 then "7" else
      if s = UnicodeChars.sup_8 then "8" else
      if s = UnicodeChars.sup_9 then "9" else s
  fun varmunge s =
      if String.sub(s,0) = #"_" andalso
         CharVector.all (fn c => Char.isDigit c) (String.extract(s,1,NONE))
      then
        ("\\HOLTokenUnderscore{}", "")
      else let
          open Substring
          val ss = full s
          val (pfx,primes) = splitl (not o equal #"'") ss
          val prime_str_interior =
            UTF8.translate translate_prime (string primes)
          val prime_str = if prime_str_interior = "" then ""
                          else "\\sp{" ^ prime_str_interior ^ "}"
          val (core,digits) = splitr Char.isDigit pfx
          val dsz = size digits
          val digitstr = if 0 < dsz andalso dsz <= 2 then
                           "\\sb{\\mathrm{" ^ string digits ^ "}}"
                         else string digits
          val core_s = UTF8.translate (fn "_" => "\\HOLTokenUnderscore{}"
                                        | s => s)
                                      (string core)
        in
          (core_s, digitstr ^ prime_str)
        end

  val stringmunge =
    UTF8.translate (fn "\\" => "\\HOLTokenBackslash{}"
                     | "~" => "\\HOLTokenTilde{}"
                     | s => s)

  fun ann_string overrides (s,sz_opt,ann) = let
    open PPBackEnd
    val (dollarpfx,dollarsfx,s,szdelta) =
        if String.sub(s,0) = #"$" andalso size s > 1 then
          if !dollar_parens then ("(", ")", String.extract(s,1,NONE),2)
          else ("", "", String.extract(s,1,NONE),0)
        else ("", "", s,0)
    fun addann2 ty (s1,s2) =
        let val base = "\\" ^ !texPrefix ^ ty ^ "{" ^ s1 ^ "}"
        in
          if size s2 = 0 then base
          else
            "\\ensuremath{" ^ base ^ s2 ^ "}"
        end
    fun addann ty s = addann2 ty (s,"")
    fun smapper s = smap overrides (s, sz_opt)
    val unmapped_sz = case sz_opt of NONE => size s | SOME i => i
    val (string_to_print, sz) =
        case ann of
            BV _ => apfst (addann2 "BoundVar" o varmunge) (smapper s)
          | FV _ => apfst (addann2 "FreeVar" o varmunge) (smapper s)
          | Const _ => apfst (addann "Const") (smapper s)
          | SymConst _ => apfst (addann "SymConst") (smapper s)
          | TyOp _ => apfst (addann "TyOp") (smapper s)
          | Literal StringLit =>
            let
              val c1i = case UTF8.getChar s of
                            SOME ((_, i), _) => i
                          | NONE => failwith "String literal with no content"
              val ann =
                  case c1i of
                    34 => (* " *) "StringLit"
                   | 0xAB => (* double guillemet *) "StringLitDG"
                   | 0x2039 => (* single guillemet *) "StringLitSG"
                   | _ => failwith
                            ("Don't understand string literal delimiter: "^s)
              (* contents of strings are 8-bit chars, but delimiters are
                 potentially Unicode *)
            in
              (addann ann
                      (stringmunge
                         (UTF8.substring(s, 1, UTF8.size s - 2))),
               unmapped_sz)
            end
          | Literal FldName => apfst (addann "FieldName") (smapper s)
          | Literal NumLit => (addann "NumLit" s, unmapped_sz)
          | Literal CharList => (addann "CharLit"
                                        (String.substring(s, 2, size s - 3)),
                                 unmapped_sz)
          | _ => smapper s
  in
    smpp.add_stringsz (dollarpfx ^ string_to_print ^ dollarsfx, sz + szdelta)
  end

  fun add_string overrides (s,sz) = smpp.add_stringsz (smap overrides (s,sz))
  fun add_xstring overrides {s,sz,ann} =
    if isSome ann then ann_string overrides (s,sz,valOf ann)
    else add_string overrides (s,sz)
in
  fun emit_latex overrides =
    {add_break = smpp.add_break,
     add_string = (fn s => add_string overrides (s,NONE)),
     add_xstring = add_xstring overrides,
     add_newline = smpp.add_newline,
     ublock = smpp.block,
     ustyle = fn sty => fn p => p ,
     extras = {
       tm_grammar_upd = (fn g => g),
       ty_grammar_upd = (fn g => g),
       name = "emit_latex"
     }
    }
end;

(* ------------------------------------------------------------------------- *)
(* pp_datatype_theorem : ppstream -> thm -> unit                             *)
(* Pretty-printer for datatype theorems                                      *)
(* ------------------------------------------------------------------------- *)

val print_datatype_names_as_types = ref false
val _ = register_btrace ("EmitTeX: print datatype names as types", print_datatype_names_as_types)

val print_datatypes_compactly = ref false
val _ = register_btrace ("EmitTeX: print datatypes compactly",
                         print_datatypes_compactly)

fun pp_datatype_theorem backend thm =
let open smpp
    val {add_string,add_break,ublock,add_newline,add_xstring,...} = backend
    val S = add_string
    val SX = add_xstring
    val BR = add_break
    val BB = ublock
    val NL = add_newline
    val trace = Feedback.trace
    fun PT0 tm =
        term_pp.pp_term (Parse.term_grammar()) (Parse.type_grammar())
                        backend tm
    val PT = Parse.mlower o (PT0 |> trace ("types", 0))
    val TP0 = type_pp.pp_type (Parse.type_grammar()) backend
    val adest_type = type_grammar.abb_dest_type (Parse.type_grammar())
    fun TP ty =
        if is_vartype ty orelse null (#Args (adest_type ty)) then TP0 ty
        else
          S "(" >> BB PP.INCONSISTENT 1 (TP0 ty) >> S")"

    fun strip_type t =
      if is_vartype t then
        [t]
      else
        case dest_type t of
          ("fun", [a, b]) => a :: strip_type b
        | _ => [t]

    fun pp_clause t =
        let val l = strip_type (type_of t)
            val ll = length l
        in
          BB PP.CONSISTENT 0 (
            lift PT t >>
            (if ll < 2 then nothing
             else
               S " " >>
               BB PP.INCONSISTENT 0 (
                 mapp (fn x => (TP x >> BR(1,0))) (List.take(l, ll - 2)) >>
                 TP (List.nth(l, ll - 2))
               ))
          )
        end

    fun enumerated_type n =
          let val l = butlast (strip_type (type_of n))
              val typ = fst (dest_var n)
          in
            all (fn x => fst (dest_type x) = typ) l
          end

    fun pp_type_name n =
      let val l = strip_type (type_of n)
      in
        TP0 (last (strip_type (hd l)))
      end

    fun pp_constructor_spec (n, l) = let
      val PT0 = if !print_datatype_names_as_types then pp_type_name else lift PT
      val tylen = n |> dest_var |> #1 |> size
    in
      if enumerated_type n then
        BB PP.CONSISTENT 0 (
         PT0 n >> S " " >>
         BB PP.INCONSISTENT (tylen + 1) (
           S "=" >> S " " >>
           pr_list pp_clause (BR(1,0) >> S"|" >> S " ") l
         )
        )
      else
        BB (if !print_datatypes_compactly then PP.INCONSISTENT
            else PP.CONSISTENT) 2 (
          PT0 n >> S " " >> S "=" >> BR(1,2) >>
          pr_list pp_clause (BR(1,0) >> S"|" >> S " ") l
        )
    end

    fun pp_record_spec ty l =
        let val ll = tl l
            fun pp_record x =
              let
                val (x,ty) = dest_var x
                val ann = SOME (PPBackEnd.Literal PPBackEnd.FldName)
              in
                BB PP.INCONSISTENT 2 (
                  SX {s=x,sz=NONE,ann=ann} >> S " " >> S ":" >> BR(1,0) >>
                  TP0 ty
                )
              end
        in
          if !KRrecordtypes then (
            BB PP.CONSISTENT 3 (
              (if !print_datatype_names_as_types then TP0 (snd(dest_var(hd l)))
               else lift PT (hd l)) >>
              S " = " >>
              S "<|" >> BR(1,0) >>
              pr_list pp_record (S ";" >> BR(1,0)) ll >>
              BR(1,~3) >> S "|>"
            )
          ) else (
            BB PP.CONSISTENT 0 (
              (if !print_datatype_names_as_types then TP0 (snd(dest_var(hd l)))
               else lift PT (hd l)) >>
              S " =" >> BR(1,2) >>
              BB PP.CONSISTENT 2 (
                S "<|" >> BR(1,0) >>
                pr_list pp_record (S ";" >> BR(1,0)) ll >>
                BR(1,~2) >>
                S "|>"
              )
            )
          )
        end

    fun pp_binding (n, l) =
          let val (x,ty) = dest_var n in
            if x = "record" then
              pp_record_spec ty l
            else
              pp_constructor_spec (n, l)
          end

    val t = map strip_comb (strip_conj (snd (dest_comb (concl thm))))
in
  BB PP.CONSISTENT 0 (pr_list pp_binding (S " ;" >> NL >> NL) t)
end;

val datatype_thm_to_string =
    PP.pp_to_string (!Globals.linewidth)
                    (Parse.mlower o pp_datatype_theorem PPBackEnd.raw_terminal)

fun print_datatypes s =
  app (fn (_,x) =>
          HOLPP.prettyPrint(print,!Globals.linewidth)
                           (Parse.mlower
                              (pp_datatype_theorem PPBackEnd.raw_terminal x)))
      (datatype_theorems s);

(* ------------------------------------------------------------------------- *)
(* Various pretty-printers                                                   *)
(* ------------------------------------------------------------------------- *)

type override_map = string -> (string * int) option

fun UnicodeOff f = trace ("Unicode", 0) f
  (* can't eta-convert because of value restriction *)

fun raw_pp_term_as_tex overrides tm mdata =
    term_pp.pp_term (Parse.term_grammar())
                    (Parse.type_grammar())
                    (emit_latex overrides)
                    tm
                    mdata
   (* eta-expanded into the monad for the sake of side-effects *)

fun pp_term_as_tex tm = raw_pp_term_as_tex (K NONE) tm |> UnicodeOff

fun raw_pp_type_as_tex overrides ty md =
    type_pp.pp_type (Parse.type_grammar()) (emit_latex overrides) ty md

fun pp_type_as_tex ty = UnicodeOff (raw_pp_type_as_tex (K NONE) ty)

val print_thm_turnstile = ref true
val _ = register_btrace ("EmitTeX: print thm turnstiles", print_thm_turnstile)

fun raw_pp_theorem_as_tex overrides thm =
  if is_datatype_thm thm then
    pp_datatype_theorem (emit_latex overrides) thm
  else
    let
      open PP smpp
      val (turnstrs, width) =
          if (!print_thm_turnstile) then
            case overrides "$Turnstile$" of
                NONE => ([(token_string "Turnstile", 2), (" ",1)], 3)
              | SOME p => ([p], snd p)
          else ([], 0)
    in
      block INCONSISTENT width (
        mapp add_stringsz turnstrs >>
        raw_pp_term_as_tex overrides (concl thm)
      )
    end;

fun pp_theorem_as_tex ostrm =
    raw_pp_theorem_as_tex (K NONE) ostrm |> UnicodeOff
                                         |> trace ("pp_dollar_escapes", 0)

fun pprint f = PP.prettyPrint (print, !Globals.linewidth) o f
val pp_type_as_tex = fn ty => Parse.mlower (pp_type_as_tex ty)
val pp_term_as_tex = fn tm => Parse.mlower (pp_term_as_tex tm)
val pp_theorem_as_tex = fn th => Parse.mlower (pp_theorem_as_tex th)

val print_term_as_tex = pprint pp_term_as_tex;
val print_type_as_tex = pprint pp_type_as_tex;
val print_theorem_as_tex = pprint pp_theorem_as_tex;

val S = PP.add_string
val NL = PP.add_newline
val B = PP.block PP.CONSISTENT 0

fun pp_hol_as_tex_command prefix (s, thm) =
  let
    val es = prefix ^ tex_command_escape s
  in
    B [
      S ("\\begin{SaveVerbatim}{" ^ es ^ "}"), NL,
      pp_theorem_as_tex thm, NL,
      S "\\end{SaveVerbatim}", NL,
      S ("\\newcommand{\\" ^ es ^ "}{\\UseVerbatim{" ^ es ^ "}}"), NL
    ]
  end;

fun pp_hol_as_tex p s = PP.add_string ("\\" ^ p ^ tex_command_escape s);

fun pp_hol_as_tex_with_tag (p1,p2) s =
  let val c = p2 ^ tex_command_escape s
  in
    B [
      S ("\\" ^ p2 ^ "{" ^ !current_theory_name ^ "}" ^ "{" ^ s ^ "}"),
      pp_hol_as_tex p1 s, NL
    ]
  end;

(* ......................................................................... *)

fun pp_newcommand c = PP.add_string ("\\newcommand{\\" ^ c ^ "}{")

fun pp_datatypes_as_tex thms =
  let val prefix = datatype_prefix()
  in
    if null thms then B []
    else
      B (
        map (pp_hol_as_tex_command prefix) thms @
        [pp_newcommand prefix, NL] @
        map (pp_hol_as_tex prefix o fst) thms @
        [S "}", NL]
      )
  end;

fun pp_defnitions_as_tex thms =
  let val prefix = definition_prefix()
  in
    PP.block PP.CONSISTENT 0 (
      if null thms then []
      else
        map (pp_hol_as_tex_command prefix) thms @
        [pp_newcommand prefix, NL] @
        map (pp_hol_as_tex_with_tag (prefix, "HOLDfnTag") o fst) thms @
        [S "}", NL]
    )
  end;

fun pp_theorems_as_tex thms =
  let val prefix = theorem_prefix()
  in
    B (
      if null thms then []
      else
        map (pp_hol_as_tex_command prefix) thms @
        [pp_newcommand prefix, NL] @
        map (pp_hol_as_tex_with_tag (prefix, "HOLThmTag") o fst) thms @
        [S "}", NL]
    )
  end;

fun pp_theory_as_tex name =
  let val _ = current_theory_name := name
      val typs = datatype_theorems name
      val defns = non_type_definitions name
      val thms = non_type_theorems name
      val time = Date.fromTimeLocal (stamp name handle HOL_ERR _ => Time.now())
      val u = current_trace "Unicode"
      val _ = set_trace "Unicode" 0
  in
    if null typs andalso null defns andalso null thms then
      (set_trace "Unicode" u; raise Fail (name ^ "Theory is empty.\n"))
    else
      B [
        pp_newcommand (date_prefix()),
        S (Date.fmt "%d %B %Y" time), S "}", NL,
        pp_newcommand (time_prefix()),
        S (Date.fmt "%H:%M" time), S "}", NL,
        pp_datatypes_as_tex typs,
        pp_defnitions_as_tex defns,
        pp_theorems_as_tex thms
      ] before (set_trace "Unicode" u; current_theory_name := "")
  end;

fun print_theory_as_tex name =
   let val name = case name of "-" => current_theory() | _ => name
       val path = if !emitTeXDir = "" then !current_path else !emitTeXDir
       val path = if path = "" then Path.currentArc else path
       val _ = FileSys.access(path, []) orelse can FileSys.mkDir path
       val _ = FileSys.access(path, [FileSys.A_WRITE, FileSys.A_EXEC])
                 orelse failwith ("Cannot create/access directory: " ^ path)
       val filename = Path.concat(path, prefix_escape name ^ ".tex")
       val ostrm = TextIO.openOut filename
   in
     PP.prettyPrint (curry TextIO.output ostrm, !texLinewidth)
                    (pp_theory_as_tex name)
       handle e => (TextIO.closeOut ostrm; raise e);
     TextIO.closeOut ostrm
   end;

(* ......................................................................... *)

val sec_divide =
  "% :::::::::::::::::::::::::::::::::::::\
    \:::::::::::::::::::::::::::::::::::::";

val subsec_divide =
  "% .....................................";

fun pp_parents_as_tex_doc names =
    B (
      if null names then [S "% No parents", NL]
      else [
        S "\\begin{flushleft}", NL,
        S ("\\textbf{Built:} " ^ "\\" ^ date_prefix() ^ " \\\\[2pt]"), NL,
        S "\\textbf{Parent Theories:} ",
        B (PP.pr_list S [S ",", PP.add_break(1,0)] names), NL,
       S "\\end{flushleft}", NL
      ]
    )

fun pp_datatypes_as_tex_doc empty =
  let val i = index_string() ^ "!Datatypes"
  in
    B (
      if empty then [S "% No datatypes", NL]
      else [
        S "\\subsection{Datatypes}", NL,
        S i, S "}", NL,
        S subsec_divide, NL, NL,
        S ("\\" ^ datatype_prefix()), NL
      ]
    )
  end;

fun pp_defnitions_as_tex_doc empty =
  let val i = index_string() ^ "!Definitions"
  in
    B (
      if empty then [S "% No definitions", NL]
      else [
        S "\\subsection{Definitions}", NL,
        S i, S "}", NL,
        S subsec_divide, NL, NL,
        S ("\\" ^ definition_prefix()), NL
      ]
    )
  end;

fun pp_theorems_as_tex_doc empty =
  let val i = index_string() ^ "!Theorems"
  in
    B (
      if empty then [S "% No theorems", NL]
      else [
        S "\\subsection{Theorems}", NL,
        S i, S "}", NL,
        S subsec_divide, NL, NL,
        S ("\\" ^ theorem_prefix()), NL
      ]
    )
  end;

fun pp_theory_as_tex_doc name =
  let val _ = current_theory_name := name
      val names = parents name handle HOL_ERR _ => []
      val typs = datatype_theorems name
      val defns = non_type_definitions name
      val thms = non_type_theorems name
  in
    B (
      if null names then []
      else [
        S sec_divide, NL,
        S "\\section{", S name, S " Theory}", NL,
        S (index_string()), S "}", NL,
        pp_parents_as_tex_doc names,
        S sec_divide, NL, NL,
        pp_datatypes_as_tex_doc (null typs), NL,
        pp_defnitions_as_tex_doc (null defns), NL,
        pp_theorems_as_tex_doc (null thms)
      ]
    ) before
    current_theory_name := ""
  end;

(* ......................................................................... *)

fun pp_theories_as_tex_doc names =
  B [
    S "\\documentclass[", S texOptions, S "]{article}", NL,
    S "\\usepackage{holtex}", NL, NL,
    S "\\makeindex", NL, NL,
    S "\\begin{document}", NL, NL,
    B (PP.pr_list (fn x => (S ("\\input{" ^ (prefix_escape x) ^ "}")))
               [NL] names), NL,
    S "\\tableofcontents", NL,
    S "\\cleardoublepage", NL,
    S "\\HOLpagestyle", NL, NL,
    B (PP.pr_list pp_theory_as_tex_doc [NL] names),
    S "\\HOLindex", NL, NL,
    S "\\end{document}"
  ]

local
  fun tex_suffix s =
    if Path.ext s = SOME "tex" then s
    else Path.joinBaseExt {base = s, ext = SOME "tex"}
in
  fun print_theories_as_tex_doc names path =
   let val {dir, file} = Path.splitDirFile path
       val dir = if Path.isAbsolute path orelse !emitTeXDir = "" then
                   dir
                 else
                   Path.concat(!emitTeXDir, dir)
       val filename = Path.concat(dir, tex_suffix file)
       val _ = not (FileSys.access (filename, [])) orelse
                 (TextIO.output(TextIO.stdErr,
                    "File " ^ path ^ " already exists.\n");
                  failwith "File exists")
       val _ = current_path := dir
       val _ = app print_theory_as_tex names
       val _ = current_path := Path.currentArc
       val ostrm = TextIO.openOut filename
   in
     PP.prettyPrint (curry TextIO.output ostrm, !texLinewidth)
                    (pp_theories_as_tex_doc names)
       handle e => (TextIO.closeOut ostrm; raise e);
     TextIO.closeOut ostrm
   end
end

fun tex_theory s =
let val c = case s of "-" => current_theory() | _ => s in
  print_theories_as_tex_doc [c] c
end;


(* lower monadic printers to what signature wants (pprinters) *)
val raw_pp_type_as_tex = fn ovm => Parse.mlower o raw_pp_type_as_tex ovm
val raw_pp_term_as_tex = fn ovm => Parse.mlower o raw_pp_term_as_tex ovm
val raw_pp_theorem_as_tex = fn ovm => Parse.mlower o raw_pp_theorem_as_tex ovm

end
