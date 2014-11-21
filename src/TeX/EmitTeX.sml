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
     [s ^ "_BIJ", s ^ "_case"]

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
in
  fun is_datatype_thm thm =
        ((fst o dest_const o fst o dest_comb o concl) thm = "DATATYPE")
             handle HOL_ERR _ => false

  fun datatype_theorems s =
  let val dtype_thms = matchp is_datatype_thm [s]
      fun dtype_name s = String.extract(s, 9, NONE)
  in
    map (fn x => (dtype_name (snd (fst x)), fst (snd x))) dtype_thms
  end

  fun non_type_definitions s =
    List.filter (fn (x,y) => not ((String.sub(x, 0) = #" ") orelse
                              Redblackset.member(type_defn_set s, x) orelse
                              rec_thm y))
                (definitions s)

  fun non_type_theorems s =
    List.filter (fn x => not ((String.sub(fst x, 0) = #" ") orelse
                              Redblackset.member(type_thm_set s, fst x)))
                (theorems s)
end;

(* ------------------------------------------------------------------------- *)
(* fix_inductive_definitions :                                               *)
(*   (string * 'a) list * (string * 'a) list ->                              *)
(*   (string * 'a) list * (string * 'a) list                                 *)
(*                                                                           *)
(* Remove/move inductive definitions                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun is_ind_def_thm names s =
        let val l = size s in
          l > 4 andalso
          (String.extract(s, l - 4, NONE) = "_def" andalso
           exists (fn x => x = String.substring(s, 0, l - 4) ^ "_ind") names)
        end

  fun is_ind_thm names s =
        let val l = size s in
          l > 4 andalso
          (String.extract(s, l - 4, NONE) = "_ind" andalso
           exists (fn x => x = String.substring(s, 0, l - 4) ^ "_def") names)
        end

  fun is_ind_def ps s =
        let fun f p = (s = p ^ "_curried_def")
        in
          isSome (List.find f ps)
        end

  fun filter_ind_thms names [] a b = (a, b)
    | filter_ind_thms names ((l, r)::t) a b =
        if is_ind_def_thm names l then
          filter_ind_thms names t ((l,r)::a) b
        else if is_ind_thm names l then
          filter_ind_thms names t a b
        else
          filter_ind_thms names t a ((l,r)::b)
in
  fun fix_inductive_definitions(defns, thms) =
    let val names = map fst thms
        val (ind_defs, rest) = filter_ind_thms names thms [] []
        val prfxs = map (fn (x, _) =>
                      String.substring(x, 0, String.size x - 4)) ind_defs
        val fix_defs = List.filter (not o is_ind_def prfxs o fst) defns
    in
      (fix_defs @ ind_defs, rest)
    end
end;

(* ------------------------------------------------------------------------- *)
(* An emit TeX back end                                                      *)
(* ------------------------------------------------------------------------- *)

fun token_string s = String.concat ["\\", !texPrefix, "Token", s, "{}"];

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
     | "φ" => greek "phi"
     | "ϕ" => greek "varphi"
     | "Φ" => greek "Phi"
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
        SOME result => result
      | NONE => (UTF8.translate char_map s,case sz of NONE => String.size s | SOME sz => sz)

  fun smap overrides (s,sz) =
      case overrides s of
        NONE => string_map (s,sz)
      | SOME r => r
  fun varmunge s =
      if String.sub(s,0) = #"_" andalso
         CharVector.all (fn c => Char.isDigit c) (String.extract(s,1,NONE))
      then
        "\\HOLTokenUnderscore{}"
      else let
          open Substring
          val ss = full s
          val (pfx,primes) = splitr (equal #"'") ss
          val prime_str_interior = translate (fn _ => "\\prime") primes
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
          core_s ^ digitstr ^ prime_str
        end

  val stringmunge =
    UTF8.translate (fn "\\" => "\\HOLTokenBackslash{}"
                     | "~" => "\\HOLTokenTilde{}"
                     | s => s)

  fun ann_string overrides pps (s,sz_opt,ann) = let
    open PPBackEnd
    val (dollarpfx,dollarsfx,s,szdelta) =
        if String.sub(s,0) = #"$" andalso size s > 1 then
          if !dollar_parens then ("(", ")", String.extract(s,1,NONE),2)
          else ("", "", String.extract(s,1,NONE),0)
        else ("", "", s,0)
    fun addann ty s =
      "\\" ^ !texPrefix ^ ty ^ "{" ^ s ^ "}"
    fun smapper s = smap overrides (s, sz_opt)
    val unmapped_sz = case sz_opt of NONE => size s | SOME i => i
    val (string_to_print, sz) =
        case ann of
            BV _ => apfst (addann "BoundVar" o varmunge) (smapper s)
          | FV _ => apfst (addann "FreeVar" o varmunge) (smapper s)
          | Const _ => apfst (addann "Const") (smapper s)
          | SymConst _ => apfst (addann "SymConst") (smapper s)
          | TyOp _ => apfst (addann "TyOp") (smapper s)
          | Literal StringLit => (addann "StringLit"
                                         (stringmunge
                                           (String.substring(s, 1, size s - 2))),
                                  unmapped_sz)
          | Literal FldName => apfst (addann "FieldName") (smapper s)
          | Literal NumLit => (addann "NumLit" s, unmapped_sz)
          | Literal CharList => (addann "CharLit"
                                        (String.substring(s, 2, size s - 3)),
                                 unmapped_sz)
          | _ => smapper s
  in
    PP.add_stringsz pps (dollarpfx ^ string_to_print ^ dollarsfx, sz + szdelta)
  end

  fun add_string overrides pps (s,sz) = PP.add_stringsz pps (smap overrides (s,sz))
  fun add_xstring overrides pps {s,sz,ann} =
    if isSome ann then ann_string overrides pps (s,sz,valOf ann)
    else add_string overrides pps (s,sz)
in
  fun emit_latex overrides =
    {add_break = PP.add_break,
     add_string = (fn pps => fn s => add_string overrides pps (s,NONE)),
     add_xstring = add_xstring overrides,
     add_newline = PP.add_newline,
     begin_block = PP.begin_block,
     end_block = PP.end_block,
     begin_style = fn pps => fn sty => () ,
     end_style = fn pps => () ,
     name = "emit_latex"}
end;

(* ------------------------------------------------------------------------- *)
(* pp_datatype_theorem : ppstream -> thm -> unit                             *)
(* Pretty-printer for datatype theorems                                      *)
(* ------------------------------------------------------------------------- *)

val print_datatype_names_as_types = ref false
val _ = register_btrace ("EmitTeX: print datatype names as types", print_datatype_names_as_types)

fun pp_datatype_theorem backend ostrm thm =
let val {add_string,add_break,begin_block,add_newline,end_block,add_xstring,...} =
           PPBackEnd.with_ppstream backend ostrm
    val S = add_string
    val SX = add_xstring
    val BR = add_break
    val BB = begin_block
    val NL = add_newline
    val EB = end_block
    val trace = Feedback.trace
    fun PT0 tm =
        term_pp.pp_term (Parse.term_grammar()) (Parse.type_grammar())
                        backend ostrm tm
    val PT = PT0 |> trace ("types", 0)
    val TP0 = type_pp.pp_type (Parse.type_grammar()) backend ostrm
    val adest_type = type_grammar.abb_dest_type (Parse.type_grammar())
    fun TP ty =
        if is_vartype ty orelse null (#2 (adest_type ty)) then TP0 ty
        else
          (S "("; BB PP.INCONSISTENT 0; TP0 ty; EB(); S")")

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
          BB PP.CONSISTENT 0;
          PT t;
          if ll < 2 then ()
          else
            (S " ";
             BB PP.INCONSISTENT 0;
             app (fn x => (TP x; BR(1,0)))
                 (List.take(l, ll - 2));
             TP (List.nth(l, ll - 2));
             EB());
          EB()
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
      val PT0 = if !print_datatype_names_as_types then pp_type_name else PT
    in
      if enumerated_type n then
        (BB PP.CONSISTENT 0;
         PT0 n; S " ";
         BB PP.INCONSISTENT 0;
         S "="; S " ";
         app (fn x => (pp_clause x; BR(1,0); S"|"; S" "))
             (List.take(l, length l - 1));
         pp_clause(last l);
         EB();
         EB())
      else
        (BB PP.CONSISTENT 2;
         PT0 n; S " "; S "="; BR(1,2);
         app (fn x => (pp_clause x; BR(1,0); S "|"; S " "))
             (List.take(l, length l - 1));
         pp_clause (last l);
         EB())
    end

    fun pp_record_spec ty l =
        let val ll = tl l
            fun pp_record x =
              let
                val (x,ty) = dest_var x
                val ann = SOME (PPBackEnd.Literal PPBackEnd.FldName)
              in
                (SX {s=x,sz=NONE,ann=ann}; S " : "; TP ty)
              end
        in
          (if !print_datatype_names_as_types
           then TP0 (mk_type(fst(dest_var(hd l)),type_vars ty))
           else PT (hd l);
           S " ="; BR(1,2);
           BB PP.CONSISTENT 3;
           S "<|"; S " ";
           app (fn x => (pp_record x; S ";"; BR(1,0)))
               (List.take(ll, length ll - 1));
           pp_record (last ll);
           S " "; S "|>";
           EB())
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
  BB PP.CONSISTENT 0;
  app (fn x => (pp_binding x; S " ;"; NL(); NL()))
      (List.take(t, length t - 1));
  pp_binding (last t);
  EB()
end;

val datatype_thm_to_string =
    PP.pp_to_string (!Globals.linewidth)
                    (pp_datatype_theorem PPBackEnd.raw_terminal)

fun print_datatypes s =
  app (fn (_,x) => print (datatype_thm_to_string x ^ "\n"))
    (datatype_theorems s);

(* ------------------------------------------------------------------------- *)
(* Various pretty-printers                                                   *)
(* ------------------------------------------------------------------------- *)

type override_map = string -> (string * int) option

fun UnicodeOff f = trace ("Unicode", 0) f
  (* can't eta-convert because of value restriction *)

fun raw_pp_term_as_tex overrides ostrm tm =
    term_pp.pp_term (Parse.term_grammar())
                    (Parse.type_grammar())
                    (emit_latex overrides)
                    ostrm
                    tm

fun pp_term_as_tex ostrm =
    raw_pp_term_as_tex (K NONE) ostrm |> UnicodeOff

fun raw_pp_type_as_tex overrides ostrm ty =
    type_pp.pp_type (Parse.type_grammar()) (emit_latex overrides) ostrm ty

fun pp_type_as_tex ostrm = UnicodeOff (raw_pp_type_as_tex (K NONE) ostrm)

val print_thm_turnstile = ref true
val _ = register_btrace ("EmitTeX: print thm turnstiles", print_thm_turnstile)

fun raw_pp_theorem_as_tex overrides ostrm thm =
  if is_datatype_thm thm then
    pp_datatype_theorem (emit_latex overrides) ostrm thm
  else
    let val {add_string,begin_block,end_block,...} =
               PPBackEnd.with_ppstream (emit_latex overrides) ostrm
    in
      begin_block Portable.INCONSISTENT 0;
      if (!print_thm_turnstile) then
        (PP.add_stringsz ostrm (token_string "Turnstile",2); add_string " ")
      else ();
      raw_pp_term_as_tex overrides ostrm (concl thm);
      end_block ()
    end;

fun pp_theorem_as_tex ostrm =
    raw_pp_theorem_as_tex (K NONE) ostrm |> UnicodeOff
                                         |> trace ("pp_dollar_escapes", 0)

val print_term_as_tex = Portable.pprint pp_term_as_tex;
val print_type_as_tex = Portable.pprint pp_type_as_tex;
val print_theorem_as_tex = Portable.pprint pp_theorem_as_tex;

fun pp_hol_as_tex_command ostrm prefix (s, thm) =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val es = prefix ^ tex_command_escape s
  in
    PP.begin_block ostrm PP.CONSISTENT 0;
    S ("\\begin{SaveVerbatim}{" ^ es ^ "}"); NL();
    pp_theorem_as_tex ostrm thm; NL();
    S "\\end{SaveVerbatim}"; NL();
    S ("\\newcommand{\\" ^ es ^ "}{\\UseVerbatim{" ^ es ^ "}}"); NL();
    PP.end_block ostrm
  end;

fun pp_hol_as_tex ostrm p s =
  PP.add_string ostrm ("\\" ^ p ^ tex_command_escape s);

fun pp_hol_as_tex_with_tag ostrm (p1,p2) s =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val c = p2 ^ tex_command_escape s
  in
    PP.begin_block ostrm PP.CONSISTENT 0;
    S ("\\" ^ p2 ^ "{" ^ !current_theory_name ^ "}" ^ "{" ^ s ^ "}");
    pp_hol_as_tex ostrm p1 s; NL();
    PP.end_block ostrm
  end;

(* ......................................................................... *)

fun pp_newcommand ostrm c =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
  in
    S ("\\newcommand{\\" ^ c ^ "}{")
  end;

fun pp_datatypes_as_tex ostrm thms =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val prefix = datatype_prefix()
  in
    if null thms then
      ()
    else
      (PP.begin_block ostrm PP.CONSISTENT 0;
       app (pp_hol_as_tex_command ostrm prefix) thms;
       pp_newcommand ostrm prefix; NL();
       app (pp_hol_as_tex ostrm prefix o fst) thms;
       S "}"; NL();
       PP.end_block ostrm)
  end;

fun pp_defnitions_as_tex ostrm thms =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val prefix = definition_prefix()
  in
    if null thms then
      ()
    else
      (PP.begin_block ostrm PP.CONSISTENT 0;
       app (pp_hol_as_tex_command ostrm prefix) thms;
       pp_newcommand ostrm prefix; NL();
       app (pp_hol_as_tex_with_tag ostrm (prefix, "HOLDfnTag") o fst) thms;
       S "}"; NL();
       PP.end_block ostrm)
  end;

fun pp_theorems_as_tex ostrm thms =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val prefix = theorem_prefix()
  in
    if null thms then
      ()
    else
      (PP.begin_block ostrm PP.CONSISTENT 0;
       app (pp_hol_as_tex_command ostrm prefix) thms;
       pp_newcommand ostrm prefix; NL();
       app (pp_hol_as_tex_with_tag ostrm (prefix, "HOLThmTag") o fst) thms;
       S "}"; NL();
       PP.end_block ostrm)
  end;

fun pp_theory_as_tex ostrm name =
  let val _ = current_theory_name := name
      val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val typs = datatype_theorems name
      val defns = non_type_definitions name
      val thms = non_type_theorems name
      val (defns, thms) = fix_inductive_definitions(defns, thms)
      val toLowercase = String.map Char.toLower
      fun thm_compare(a,b) = String.compare(toLowercase (fst a),
                                            toLowercase (fst b))
      val defns = Listsort.sort thm_compare defns
      val thms = Listsort.sort thm_compare thms
      val time = Date.fromTimeLocal (stamp name handle HOL_ERR _ => Time.now())
      val u = current_trace "Unicode"
  in
    if null typs andalso null defns andalso null thms then
      TextIO.output(TextIO.stdErr, name ^ "Theory is empty.\n")
    else
      (PP.begin_block ostrm PP.CONSISTENT 0;
       pp_newcommand ostrm (date_prefix());
       S (Date.fmt "%d %B %Y" time); S "}"; NL();
       pp_newcommand ostrm (time_prefix());
       S (Date.fmt "%H:%M" time); S "}"; NL();
       set_trace "Unicode" 0;
       pp_datatypes_as_tex ostrm typs;
       pp_defnitions_as_tex  ostrm defns;
       pp_theorems_as_tex ostrm thms;
       set_trace "Unicode" u;
       PP.end_block ostrm);
    current_theory_name := ""
  end;

fun print_theory_as_tex name =
   let val name = case name of "-" => current_theory() | _ => name
       val path = if !emitTeXDir = "" then !current_path else !emitTeXDir
       val path = if path = "" then Path.currentArc else path
       val _ = FileSys.access(path, []) orelse can FileSys.mkDir path
       val _ = FileSys.access(path, [FileSys.A_WRITE, FileSys.A_EXEC])
                 orelse failwith ("Cannot create/access directory: " ^ path)
       val filename = Path.concat(path, prefix_escape name ^ ".tex")
       val ostrm = Portable.open_out filename
   in
     PP.with_pp {consumer = Portable.outputc ostrm, linewidth = !texLinewidth,
                 flush = fn () => Portable.flush_out ostrm}
        (Lib.C pp_theory_as_tex name)
     handle e => (Portable.close_out ostrm; raise e);
     Portable.close_out ostrm
   end;

(* ......................................................................... *)

val sec_divide =
  "% :::::::::::::::::::::::::::::::::::::\
    \:::::::::::::::::::::::::::::::::::::";

val subsec_divide =
  "% .....................................";

fun pp_parents_as_tex_doc ostrm names =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
  in
    PP.begin_block ostrm PP.CONSISTENT 0;
    if null names then
      (S "% No parents"; NL())
    else
      (S "\\begin{flushleft}"; NL();
       S ("\\textbf{Built:} " ^ "\\" ^ date_prefix() ^ " \\\\[2pt]"); NL();
       S "\\textbf{Parent Theories:} ";
       app (fn x => S (x ^ ", ")) (List.take(names, length names - 1));
       S (last names); NL();
       S "\\end{flushleft}"; NL());
    PP.end_block ostrm
  end;

fun pp_datatypes_as_tex_doc ostrm empty =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val i = index_string() ^ "!Datatypes"
  in
    PP.begin_block ostrm PP.CONSISTENT 0;
    if empty then
      (S "% No datatypes"; NL())
    else
      (S "\\subsection{Datatypes}"; NL();
       S i; S "}"; NL();
       S subsec_divide; NL(); NL();
       S ("\\" ^ datatype_prefix()); NL());
    PP.end_block ostrm
  end;

fun pp_defnitions_as_tex_doc ostrm empty =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val i = index_string() ^ "!Definitions"
  in
    PP.begin_block ostrm PP.CONSISTENT 0;
    if empty then
      (S "% No definitions"; NL())
    else
      (S "\\subsection{Definitions}"; NL();
       S i; S "}"; NL();
       S subsec_divide; NL(); NL();
       S ("\\" ^ definition_prefix()); NL());
    PP.end_block ostrm
  end;

fun pp_theorems_as_tex_doc ostrm empty =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val i = index_string() ^ "!Theorems"
  in
    PP.begin_block ostrm PP.CONSISTENT 0;
    if empty then
      (S "% No theorems"; NL())
    else
      (S "\\subsection{Theorems}"; NL();
       S i; S "}"; NL();
       S subsec_divide; NL(); NL();
       S ("\\" ^ theorem_prefix()); NL());
    PP.end_block ostrm
  end;

fun pp_theory_as_tex_doc ostrm name =
  let val _ = current_theory_name := name
      val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
      val names = parents name handle HOL_ERR _ => []
      val typs = datatype_theorems name
      val defns = non_type_definitions name
      val thms = non_type_theorems name
      val (defns, thms) = fix_inductive_definitions(defns, thms)
  in
    if null names then
      ()
    else
      (PP.begin_block ostrm PP.CONSISTENT 0;
       S sec_divide; NL();
       S "\\section{"; S name; S " Theory}"; NL();
       S (index_string()); S "}"; NL();
       pp_parents_as_tex_doc ostrm names;
       S sec_divide; NL(); NL();
       pp_datatypes_as_tex_doc ostrm (null typs); NL();
       pp_defnitions_as_tex_doc ostrm (null defns); NL();
       pp_theorems_as_tex_doc ostrm (null thms);
       PP.end_block ostrm);
    current_theory_name := ""
  end;

(* ......................................................................... *)

fun pp_theories_as_tex_doc ostrm names =
  let val S = PP.add_string ostrm
      fun NL() = PP.add_newline ostrm
  in
    PP.begin_block ostrm PP.CONSISTENT 0;
    S "\\documentclass["; S texOptions; S "]{article}"; NL();
    S "\\usepackage{holtex}"; NL(); NL();
    S "\\makeindex"; NL(); NL();
    S "\\begin{document}"; NL(); NL();
    app (fn x => (S ("\\input{" ^ (prefix_escape x) ^ "}"); NL())) names; NL();
    S "\\tableofcontents"; NL();
    S "\\cleardoublepage"; NL();
    S "\\HOLpagestyle"; NL(); NL();
    app (fn x => (pp_theory_as_tex_doc ostrm x; NL())) names;
    S "\\HOLindex"; NL(); NL();
    S "\\end{document}";
    PP.end_block ostrm
  end;

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
       val ostrm = Portable.open_out filename
   in
     PP.with_pp {consumer = Portable.outputc ostrm, linewidth = !texLinewidth,
                 flush = fn () => Portable.flush_out ostrm}
        (Lib.C pp_theories_as_tex_doc names)
     handle e => (Portable.close_out ostrm; raise e);
     Portable.close_out ostrm
   end
end

fun tex_theory s =
let val c = case s of "-" => current_theory() | _ => s in
  print_theories_as_tex_doc [c] c
end;

end
