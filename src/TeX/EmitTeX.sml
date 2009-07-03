structure EmitTeX :> EmitTeX =
struct

open HolKernel boolLib;

(* ------------------------------------------------------------------------- *)
(* Configuration                                                             *)
(* ------------------------------------------------------------------------- *)

val texLinewidth = 78;
val texOptions = "11pt, twoside";

val texPrefix  = ref "HOL";
val emitTeXDir = ref "";

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
    s :: s ^ "_case_def" :: List.concat
      (map (fn x => let val y = s ^ "_" ^ x in [y, y ^ "_fupd"] end) flds)

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
(* pp_datatype_theorem : ppstream -> thm -> unit                             *)
(* Pretty-printer for datatype theorems                                      *)
(* ------------------------------------------------------------------------- *)

fun pp_datatype_theorem ostrm thm =
let val S = PP.add_string ostrm
    val BR = PP.add_break ostrm
    val BB = PP.begin_block ostrm
    fun NL() = PP.add_newline ostrm
    fun EB() = PP.end_block ostrm
    val PT = pp_term ostrm
    val TP = type_pp.pp_type (Parse.type_grammar()) ostrm

    val type_trace = current_trace "types"
    val _ = set_trace "types" 0

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
          (PT t;
             if ll < 2 then
               ()
             else
               (S " of ";
                BB PP.CONSISTENT 0;
                  app (fn x => (TP x; S " =>"; BR(1,0))) (List.take(l, ll - 2));
                  TP (List.nth(l, ll - 2));
                EB()))
        end
    fun enumerated_type n =
          let val l = butlast (strip_type (type_of n))
              val typ = fst (dest_var n)
          in
            all (fn x => fst (dest_type x) = typ) l
          end
    fun pp_constructor_spec (n, l) =
          (PT n;
           BB (if enumerated_type n then PP.INCONSISTENT else PP.CONSISTENT) 1;
             S " = ";
             app (fn x => (pp_clause x; BR(1,0); S "| "))
               (List.take(l, length l - 1));
             pp_clause (last l);
           EB())
    fun pp_record_spec l =
        let val ll = tl l
            fun pp_record x = (PT x; S " : "; TP (type_of x))
        in
          (PT (hd l); S " = ";
           BB PP.CONSISTENT 1;
             S "<|"; BR(1,1);
             app (fn x => (pp_record x; S ";"; BR(1,1)))
               (List.take(ll, length ll - 1));
             pp_record (last ll); BR(1,0);
             S "|>";
           EB())
        end
    fun pp_binding (n, l) =
          if fst (dest_var n) = "record" then
            pp_record_spec l
          else
            pp_constructor_spec (n, l)
    fun pp_datatype l =
          (BB PP.CONSISTENT 0;
             app (fn x => (pp_binding x; S " ;"; NL(); NL()))
               (List.take(l, length l - 1));
             pp_binding (last l);
           EB())

    val t = map strip_comb (strip_conj (snd (dest_comb (concl thm))))
in
  pp_datatype t; PP.flush_ppstream ostrm; set_trace "types" type_trace
end;

val datatype_thm_to_string =
  PP.pp_to_string (!Globals.linewidth) pp_datatype_theorem;

fun print_datatypes s =
  app (fn (_,x) => print (datatype_thm_to_string x ^ "\n"))
    (datatype_theorems s);

(* ------------------------------------------------------------------------- *)
(* theorem2tex : string -> string                                            *)
(* datatype2tex : string -> string                                           *)
(*   Replace HOL tokens in the string with tex code                          *)
(* ------------------------------------------------------------------------- *)

local
  fun token_string s = "\\" ^ !texPrefix ^ "Token" ^ s ^ "{}";
  fun h2t cs s =
    case cs of
      [] => s
    | #"|" :: #"-" :: #">" :: l         => h2t l (s ^ token_string "Mapto")
    | #"-" :: #"-" :: #">" :: l         => h2t l (s ^ token_string "Longmap")
    | #"=" :: #"=" :: #"=" :: #">" :: l => h2t l (s ^ token_string "Longimp")
    | #"-" :: #">" :: l                 => h2t l (s ^ token_string "Map")
    | #"<" :: #"-" :: l                 => h2t l (s ^ token_string "Leftmap")
    | #"=" :: #"=" :: #">" :: l         => h2t l (s ^ token_string "Imp")
    | #"=" :: #">" :: l                 => h2t l (s ^ token_string "Imp")
    | #"|" :: #"-" :: l                 => h2t l (s ^ token_string "Turnstile")
    | #"/" :: #"\\" :: l                => h2t l (s ^ token_string "Conj")
    | #"\\" :: #"/" :: l                => h2t l (s ^ token_string "Disj")
    | #"<" :: #"=" :: #"/" :: #"=" :: #">" :: l
                                        => h2t l (s ^ token_string "NotEquiv")
    | #"<" :: #"=" :: #">" :: l         => h2t l (s ^ token_string "Equiv")
    | #"<" :: #"|" :: l                 => h2t l (s ^ token_string "Leftrec")
    | #"|" :: #">" :: l                 => h2t l (s ^ token_string "Rightrec")
    | #"<" :: #"+" :: l                 => h2t l (s ^ token_string "Lo")
    | #">" :: #"+" :: l                 => h2t l (s ^ token_string "Hi")
    | #"<" :: #"=" :: #"+" :: l         => h2t l (s ^ token_string "Ls")
    | #">" :: #"=" :: #"+" :: l         => h2t l (s ^ token_string "Hs")
    | #"<" :: #"=" :: l                 => h2t l (s ^ token_string "Leq")
    | #">" :: #"=" :: l                 => h2t l (s ^ token_string "Geq")
    | #"{" :: #"}" :: l                 => h2t l (s ^ token_string "Empty")
    | #"*" :: #"*" :: l                 => h2t l (s ^ token_string "Exp")
    | #"#" :: #">" :: #">" :: l         => h2t l (s ^ token_string "Ror")
    | #"#" :: #"<" :: #"<" :: l         => h2t l (s ^ token_string "Rol")
    | #">" :: #">" :: #">" :: l         => h2t l (s ^ token_string "Lsr")
    | #">" :: #">" :: l                 => h2t l (s ^ token_string "Asr")
    | #"<" :: #"<" :: l                 => h2t l (s ^ token_string "Lsl")
    | #"<" :: #">" :: l                 => h2t l (s ^ token_string "Slice")
    | #">" :: #"<" :: l                 => h2t l (s ^ token_string "Extract")
    | #"#" :: #"#" :: l                 => h2t l (s ^ "##")
    | #"#" :: l                         => h2t l (s ^ token_string "Prod")
    | #"|" :: l                         => h2t l (s ^ token_string "Bar")
    | #"'" :: l                         => h2t l (s ^ token_string "Quote")
    | #"~" :: l                         => h2t l (s ^ token_string "Neg")
    | #"_" :: l                         => h2t l (s ^ token_string "Underscore")
    | #"<"::l                           => h2t l (s ^ token_string "Lt")
    | #">"::l                           => h2t l (s ^ token_string "Gt")
    | #"{"::l                           => h2t l (s ^ token_string "Leftbrace")
    | #"}"::l                           => h2t l (s ^ token_string "Rightbrace")
    | #"\n"::l                          => h2t l (s ^ "\n")
    | #"!" :: #"!" :: l                 => h2t l (s ^ token_string "Or")
    | #"?" :: #"?" :: l                 => h2t l (s ^ token_string "Eor")
    | #"!" :: c :: l  => if Char.isAlpha c orelse c = #"(" then
                           h2t l (s ^ token_string "Forall" ^ Char.toString c)
                         else
                           h2t (c :: l) (s ^ "!")
    | #"?" :: c :: l  => if Char.isAlpha c orelse c = #"(" then
                           h2t l (s ^ token_string "Exists" ^ Char.toString c)
                         else
                           if c = #"!" then
                             h2t l (s ^ token_string "Unique")
                           else
                             h2t (c :: l) (s ^ "?")
    | #"\\" :: c :: l => if Char.isAlpha c orelse c = #"(" then
                           h2t l (s ^ token_string "Lambda" ^ Char.toString c)
                         else
                           h2t (c :: l) (s ^ token_string "Backslash")
    | c::l => h2t l (s ^ Char.toString c)
in
  fun hol2tex s  = h2t (explode s) ""
end;

val hol_to_tex  = ref hol2tex;

(* ------------------------------------------------------------------------- *)
(* Various pretty-printers                                                   *)
(* ------------------------------------------------------------------------- *)

fun pp_term_as_tex ostrm t =
let val u = current_trace "Unicode" in
  set_trace "Unicode" 0;
  PP.add_string ostrm (!hol_to_tex (term_to_string t));
  set_trace "Unicode" u
end;

fun pp_type_as_tex ostrm t =
let val u = current_trace "Unicode" in
  set_trace "Unicode" 0;
  PP.add_string ostrm (!hol_to_tex (type_to_string t));
  set_trace "Unicode" u
end;

fun pp_theorem_as_tex ostrm thm =
  PP.add_string ostrm (!hol_to_tex
    (if is_datatype_thm thm then
       datatype_thm_to_string thm
     else
       thm_to_string thm));

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
     PP.with_pp {consumer = Portable.outputc ostrm, linewidth = texLinewidth,
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
     PP.with_pp {consumer = Portable.outputc ostrm, linewidth = texLinewidth,
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
