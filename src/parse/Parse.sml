structure Parse :> Parse =
struct

open Feedback HolKernel HOLgrammars GrammarSpecials term_grammar type_grammar

type pp_element = term_grammar.pp_element
type PhraseBlockStyle = term_grammar.PhraseBlockStyle
type ParenStyle = term_grammar.ParenStyle
type block_info = term_grammar.block_info
type associativity = HOLgrammars.associativity
type 'a frag = 'a Portable.frag

val ERROR = mk_HOL_ERR "Parse";
val ERRORloc = mk_HOL_ERRloc "Parse";
val WARN  = HOL_WARNING "Parse"

val post_process_term = Preterm.post_process_term
val quote = Lib.mlquote

datatype fixity = RF of term_grammar.rule_fixity | Prefix | Binder

fun acc_strip_comb M rands =
  let val (Rator,Rand) = dest_comb M
  in acc_strip_comb Rator (Rand::rands)
  end
  handle HOL_ERR _ => (M,rands);

fun strip_comb tm = acc_strip_comb tm [];

val dest_forall = sdest_binder ("!","bool") (ERROR "dest_forall" "");

fun strip_forall fm =
 let val (Bvar,Body) = dest_forall fm
     val (bvs,core) = strip_forall Body
 in (Bvar::bvs, core)
 end handle HOL_ERR _ => ([],fm);

fun lhs tm = #2(sdest_binop("=","min") (ERROR"lhs" "") tm);

fun ftoString [] = ""
  | ftoString (QUOTE s :: rest) = s ^ ftoString rest
  | ftoString (ANTIQUOTE x :: rest) = "..." ^ ftoString rest

fun lose_constrec_ty {Name,Thy,Ty} = {Name = Name, Thy = Thy}

(*---------------------------------------------------------------------------
    Fixity stuff
 ---------------------------------------------------------------------------*)

datatype fixity
    = RF of rule_fixity
    | Prefix
    | Binder

fun Infix x = x;  (* namespace hackery *)
fun Suffix x = x;
fun Closefix x = x;
fun TruePrefix x = x;

val Infix        = fn (a,i) => RF (term_grammar.Infix (a,i))
val Infixl       = fn i => Infix(LEFT, i)
val Infixr       = fn i => Infix(RIGHT, i)
val Suffix       = fn n => RF (term_grammar.Suffix n)
val Closefix     = RF term_grammar.Closefix
val TruePrefix   = fn n => RF (term_grammar.TruePrefix n)


(*---------------------------------------------------------------------------
         pervasive type grammar
 ---------------------------------------------------------------------------*)

(* type grammar *)
val the_type_grammar = ref type_grammar.min_grammar
val type_grammar_changed = ref false
fun type_grammar() = !the_type_grammar

(*---------------------------------------------------------------------------
         pervasive term grammar
 ---------------------------------------------------------------------------*)

val the_term_grammar = ref term_grammar.min_grammar
val term_grammar_changed = ref false
fun term_grammar () = (!the_term_grammar)

fun current_grammars() = (type_grammar(), term_grammar());

(* ----------------------------------------------------------------------
    Pervasive pretty-printing backend
   ---------------------------------------------------------------------- *)

fun interactive_ppbackend () = let
  open PPBackEnd OS.Process
in
  (* assumes interactive *)
  case getEnv "TERM" of
    SOME s => if String.isPrefix "xterm" s then vt100_terminal
              else raw_terminal
  | _ => raw_terminal
end

val current_backend : PPBackEnd.t ref =
    ref (if !Globals.interactive then interactive_ppbackend()
         else PPBackEnd.raw_terminal)

(*---------------------------------------------------------------------------
         local grammars
 ---------------------------------------------------------------------------*)

val the_lty_grm = ref type_grammar.empty_grammar
val the_ltm_grm = ref term_grammar.stdhol
fun current_lgrms() = (!the_lty_grm, !the_ltm_grm);


fun fixity s =
  case term_grammar.get_precedence (term_grammar()) s
   of SOME rf => RF rf
    | NONE => if Lib.mem s (term_grammar.binders (term_grammar()))
                 then Binder
                 else Prefix

(*---------------------------------------------------------------------------
       Mysterious stuff
 ---------------------------------------------------------------------------*)

(* type parsing *)

val ty_antiq = parse_type.ty_antiq;
val dest_ty_antiq = parse_type.dest_ty_antiq;
val is_ty_antiq = parse_type.is_ty_antiq;

local
  open parse_type Pretype
in
val type_parser1 =
    ref (parse_type termantiq_constructors false (type_grammar()))
val type_parser2 =
    ref (parse_type typantiq_constructors false (type_grammar()))
end



(*---------------------------------------------------------------------------
        pretty printing types
 ---------------------------------------------------------------------------*)

val type_printer = ref (type_pp.pp_type (type_grammar()))

val grammar_term_printer =
  ref (term_pp.pp_term (term_grammar()) (type_grammar()))
fun pp_grammar_term pps t = (!grammar_term_printer) (!current_backend) pps t

val term_printer = ref pp_grammar_term

fun get_term_printer () = (!term_printer)

fun set_term_printer new_pp_term = let
  val old_pp_term = !term_printer
in
  term_printer := new_pp_term;
  old_pp_term
end



fun update_type_fns () =
  if !type_grammar_changed then let
      open Pretype parse_type
    in
     type_parser1 := parse_type termantiq_constructors false (type_grammar());
     type_parser2 := parse_type typantiq_constructors false (type_grammar());
     type_printer := type_pp.pp_type (type_grammar());
     type_grammar_changed := false
  end
  else ()

fun pp_type pps ty = let in
   update_type_fns();
   Portable.add_string pps ":";
   !type_printer (!current_backend) pps ty
 end


fun type_to_string ty =
    Lib.with_flag (current_backend, PPBackEnd.raw_terminal)
                  (Portable.pp_to_string (!Globals.linewidth) pp_type) ty;
fun print_type ty = Portable.output(Portable.std_out, type_to_string ty);

fun type_to_backend_string ty =
   (Portable.pp_to_string (!Globals.linewidth) pp_type) ty;
fun print_backend_type ty =
  Portable.output(Portable.std_out, type_to_backend_string ty);

fun type_pp_with_delimiters ppfn pp ty =
  let open Portable Globals
  in add_string pp (!type_pp_prefix);
     ppfn pp ty;
     add_string pp (!type_pp_suffix)
  end


fun pp_with_bquotes ppfn pp x =
  let open Portable in add_string pp "`"; ppfn pp x; add_string pp "`" end

fun print_from_grammars (tyG, tmG) =
  (type_pp.pp_type tyG (!current_backend),
   term_pp.pp_term tmG tyG (!current_backend))

fun print_term_by_grammar Gs = let
  open TextIO PP
  val con = {consumer = (fn s => output(stdOut, s)),
             linewidth = !Globals.linewidth,
             flush = (fn () => flushOut stdOut)}
  val (_, termprinter) = print_from_grammars Gs
  fun pprint t pps = (begin_block pps CONSISTENT 0;
                      termprinter pps t;
                      add_newline pps;
                      end_block pps)
in
  fn t => with_pp con (pprint t)
end

val min_grammars = (type_grammar.min_grammar, term_grammar.min_grammar)

fun minprint t = let
  fun default t = let
    val (_, baseprinter) =
        Lib.with_flag (current_backend, PPBackEnd.raw_terminal)
                      print_from_grammars
                      min_grammars
    fun printer pps =
        baseprinter pps |> trace ("types", 1) |> trace ("Greek tyvars", 0)
    val t_str =
        String.toString (PP.pp_to_string 1000000 printer t)
  in
    String.concat ["(#2 (parse_from_grammars min_grammars)",
                   "[QUOTE \"", t_str, "\"])"]
  end
in
  if is_const t then let
      val {Name,Thy,...} = dest_thy_const t
      val t' = prim_mk_const {Name = Name, Thy = Thy}
    in
      if aconv t t' then
        String.concat ["(Term.prim_mk_const { Name = ",
                       quote Name, ", Thy = ",
                       quote Thy, "})"]
      else default t
    end
  else default t
end

(*---------------------------------------------------------------------------
              Parsing types
 ---------------------------------------------------------------------------*)

local open parse_type
in
fun parse_Type parser q = let
  open base_tokens qbuf
  val qb = new_buffer q
in
  case qbuf.current qb of
    (BT_Ident s,locn) =>
    if String.sub(s, 0) <> #":" then
      raise ERRORloc "parse_Type" locn "types must begin with a colon"
    else let
        val _ = if size s = 1 then advance qb
                else let val locn' = locn.move_start 1 locn in
                     replace_current (BT_Ident (String.extract(s, 1, NONE)),locn') qb end
        val pt = parser qb
      in
        case current qb of
            (BT_EOI,_) => Pretype.toType pt
          | (_,locn) => raise ERRORloc "parse_Type" locn
                                       ("Couldn't make any sense of remaining input.")
      end
  | (_,locn) => raise ERRORloc "parse_Type" locn "types must begin with a colon"
end
end (* local *)

fun Type q = let in
   update_type_fns();
   parse_Type (!type_parser2) q
 end

fun == q x = Type q;


(*---------------------------------------------------------------------------
             Parsing into abstract syntax
 ---------------------------------------------------------------------------*)

val the_absyn_parser: (term frag list -> Absyn.absyn) ref =
    ref (TermParse.absyn (!the_term_grammar) (!the_type_grammar))

fun update_term_fns() = let
  val _ = update_type_fns()
in
  if !term_grammar_changed then let
  in
    grammar_term_printer := term_pp.pp_term (term_grammar()) (type_grammar());
    the_absyn_parser := TermParse.absyn (!the_term_grammar) (!the_type_grammar);
    term_grammar_changed := false
  end
  else ()
end

fun Absyn q = let
in
  update_term_fns();
  !the_absyn_parser q
end

(* ----------------------------------------------------------------------
      Interlude: ppstream modifications to allow pretty-printers to
                 respect dynamically changing line-widths
   ---------------------------------------------------------------------- *)

fun respect_width_ref iref pprinter pps x = let
  val slist = ref ([] : string list)
  fun output_slist () =
    (app (PP.add_string pps) (List.rev (!slist));
     slist := [])
  fun flush () = output_slist()
  fun consume_string s = let
    open Substring
    val (pfx, sfx) = splitl (fn c => c <> #"\n") (full s)
  in
    if size sfx = 0 then slist := s :: !slist
    else
      (output_slist();
       PP.add_newline pps;
       if size sfx > 1 then consume_string (string (triml 1 sfx))
       else ())
  end
  val consumer = {consumer = consume_string, linewidth = !iref, flush = flush}
  val newpps = PP.mk_ppstream consumer
in
  PP.begin_block pps PP.INCONSISTENT 0;
  PP.begin_block newpps PP.INCONSISTENT 0;
  pprinter newpps x;
  PP.end_block newpps;
  PP.flush_ppstream newpps;
  PP.end_block pps
end


(* ----------------------------------------------------------------------
    Top-level pretty-printing entry-points
   ---------------------------------------------------------------------- *)

fun pp_style_string ppstrm (st, s) =
 let open Portable PPBackEnd
    val {add_string,begin_style,end_style,...} = PPBackEnd.with_ppstream (!current_backend) ppstrm
 in
    begin_style st;
    add_string s;
    end_style ()
 end

fun add_style_to_string st s = (Portable.pp_to_string (!Globals.linewidth) pp_style_string) (st, s);
fun print_with_style st s =  Portable.output(Portable.std_out, add_style_to_string st s);


fun pp_term pps t = (update_term_fns(); !term_printer pps t)
fun term_to_string t =
    Lib.with_flag (current_backend, PPBackEnd.raw_terminal)
                  (Portable.pp_to_string (!Globals.linewidth) pp_term) t;
fun print_term t = Portable.output(Portable.std_out, term_to_string t);

fun term_to_backend_string t =
   (Portable.pp_to_string (!Globals.linewidth) pp_term) t;
fun print_backend_term t =
  Portable.output(Portable.std_out, term_to_backend_string t);


fun term_pp_with_delimiters ppfn pp tm =
  let open Portable Globals
  in add_string pp (!term_pp_prefix);
     ppfn pp tm;
     add_string pp (!term_pp_suffix)
  end

fun pp_thm ppstrm th =
 let open Portable
    fun repl ch alist =
         String.implode (itlist (fn _ => fn chs => (ch::chs)) alist [])
    val {add_string,add_break,begin_block,end_block,...} = with_ppstream ppstrm
    val pp_term = pp_term ppstrm
    fun pp_terms b L =
      (begin_block INCONSISTENT 1; add_string "[";
       if b then pr_list pp_term (fn () => add_string ",")
                                 (fn () => add_break(1,0)) L
       else add_string (repl #"." L); add_string "]";
       end_block())
 in
    begin_block INCONSISTENT 0;
    if !Globals.max_print_depth = 0 then add_string " ... "
    else let open Globals
             val (tg,asl,st,sa) = (tag th, hyp th, !show_tags, !show_assums)
         in if not st andalso not sa andalso null asl then ()
            else (if st then Tag.pp_tag ppstrm tg else ();
                  add_break(1,0);
                  pp_terms sa asl; add_break(1,0)
                 );
            add_string "|- ";
            pp_term (concl th)
         end;
    end_block()
 end;

fun thm_to_string thm =
    Lib.with_flag (current_backend, PPBackEnd.raw_terminal)
                  (Portable.pp_to_string (!Globals.linewidth) pp_thm) thm;
fun print_thm thm     = Portable.output(Portable.std_out, thm_to_string thm);

fun thm_to_backend_string thm =
   (Portable.pp_to_string (!Globals.linewidth) pp_thm) thm;
fun print_backend_thm thm =
  Portable.output(Portable.std_out, thm_to_backend_string thm);


(*---------------------------------------------------------------------------
     Parse into preterm type
 ---------------------------------------------------------------------------*)

fun absyn_to_preterm a = TermParse.absyn_to_preterm (term_grammar()) a

fun Preterm q = q |> Absyn |> absyn_to_preterm

val absyn_to_term =
    TermParse.absyn_to_term (SOME (term_to_string, type_to_string))


(*---------------------------------------------------------------------------
     Parse into term type.
 ---------------------------------------------------------------------------*)

fun Term q = absyn_to_term (term_grammar()) (Absyn q)

fun -- q x = Term q;

fun typedTerm qtm ty =
   let fun trail s = [QUOTE (s^"):"), ANTIQUOTE(ty_antiq ty), QUOTE""]
   in
   Term (case (Lib.front_last qtm)
        of ([],QUOTE s) => trail ("("^s)
         | (QUOTE s::rst, QUOTE s') => (QUOTE ("("^s)::rst) @ trail s'
         | _ => raise ERROR"typedTerm" "badly formed quotation")
   end;

fun parse_from_grammars (tyG, tmG) = let
  val ty_parser = parse_type.parse_type Pretype.typantiq_constructors false tyG
  val tm_parser = absyn_to_term tmG o TermParse.absyn tmG tyG
in
  (parse_Type ty_parser, tm_parser)
end

(* ----------------------------------------------------------------------
    parsing in context
   ---------------------------------------------------------------------- *)

fun parse_in_context FVs q =
    TermParse.ctxt_preterm_to_term (SOME(term_to_string,type_to_string))
                                   FVs
                                   (Preterm q)

fun grammar_parse_in_context(tyg,tmg) =
    TermParse.ctxt_term (SOME(term_to_string,type_to_string)) tmg tyg

val parse_preterm_in_context =
    TermParse.ctxt_preterm_to_term (SOME(term_to_string,type_to_string))


(*---------------------------------------------------------------------------
     Making temporary and persistent changes to the grammars.
 ---------------------------------------------------------------------------*)

val grm_updates = ref [] : (string * string * term option) list ref;

fun pending_updates() = !grm_updates

fun update_grms fname (x,y) = grm_updates := ((x,y,NONE) :: !grm_updates);
fun full_update_grms (x,y,opt) = grm_updates := ((x,y,opt) :: !grm_updates)

fun temp_remove_termtok r = let open term_grammar in
  the_term_grammar := remove_form_with_tok (term_grammar()) r;
  term_grammar_changed := true
 end

fun remove_termtok (r as {term_name, tok}) = let in
   temp_remove_termtok r;
   update_grms "remove_termtok" ("temp_remove_termtok",
                                 String.concat
                                   ["{term_name = ", quote term_name,
                                    ", tok = ", quote tok, "}"])
 end

fun temp_prefer_form_with_tok r = let open term_grammar in
    the_term_grammar := prefer_form_with_tok r (term_grammar());
    term_grammar_changed := true
 end

fun prefer_form_with_tok (r as {term_name,tok}) = let in
    temp_prefer_form_with_tok r;
    update_grms "prefer_form_with_tok"
                ("temp_prefer_form_with_tok",
                 String.concat ["{term_name = ", quote term_name,
                                ", tok = ", quote tok, "}"])
 end


fun temp_set_grammars(tyG, tmG) = let
in
  the_term_grammar := tmG;
  the_type_grammar := tyG;
  term_grammar_changed := true;
  type_grammar_changed := true
end

fun standard_mapped_spacing {term_name,tok,fixity}  = let
  open term_grammar  (* to get fixity constructors *)
  val bstyle = (AroundSamePrec, (Portable.INCONSISTENT, 0))
  val pstyle = OnlyIfNecessary
  val ppels =
      case fixity of
        Infix _ => [HardSpace 1, RE (TOK tok), BreakSpace(1,0)]
      | TruePrefix _ => [RE(TOK tok), HardSpace 1]
      | Suffix _     => [HardSpace 1, RE(TOK tok)]
      | Closefix  => [RE(TOK tok)]
in
  {term_name = term_name, fixity = fixity, pp_elements = ppels,
   paren_style = pstyle, block_style = bstyle}
end

fun standard_spacing name fixity =
    standard_mapped_spacing {term_name = name, tok = name, fixity = fixity}

val std_binder_precedence = 0;

structure Unicode =
struct

  fun temp_set_term_grammar tmg = temp_set_grammars(type_grammar(), tmg)

  val master_unicode_switch = ref true
  fun lift0 f = temp_set_term_grammar (f (term_grammar()))
  fun lift f x = lift0 (f (!master_unicode_switch) x)
  fun unicode_version r = lift ProvideUnicode.unicode_version r
  fun uoverload_on r = lift ProvideUnicode.uoverload_on r
  fun temp_unicode_version r = lift ProvideUnicode.temp_unicode_version r
  fun temp_uoverload_on r = lift ProvideUnicode.temp_uoverload_on r

  fun fixity_prec f = let
    open term_grammar
  in
    case f of
      RF (Infix(_, p)) => SOME p
    | RF (Suffix p) => SOME p
    | RF (TruePrefix p) => SOME p
    | RF Closefix => NONE
    | Prefix => NONE
    | Binder => SOME std_binder_precedence
  end

  exception foo
  fun uset_fixity0 setter s fxty = let
    open term_grammar
    val rule =
      case fxty of
        Prefix => (HOL_MESG "Fixities of Prefix do not affect the grammar";
                   raise foo)
      | Binder => BRULE {tok = s, term_name = s}
      | RF rf => GRULE (standard_spacing s rf)
  in
    lift setter {u = [s], term_name = s, newrule = rule, oldtok = NONE}
  end handle foo => ()

  val temp_uset_fixity = uset_fixity0 ProvideUnicode.temp_uadd_rule
  val uset_fixity = uset_fixity0 ProvideUnicode.uadd_rule

  structure UChar = UnicodeChars
  fun fupd_lambda f {type_intro,lambda,endbinding,restr_binders,res_quanop} =
      {type_intro = type_intro, lambda = f lambda, endbinding = endbinding,
       restr_binders = restr_binders, res_quanop = res_quanop}


  fun bare_lambda() =
      temp_set_term_grammar (fupdate_specials (fupd_lambda (fn _ => ["\\"]))
                                              (term_grammar()))

  fun unicode_lambda () =
      temp_set_term_grammar (fupdate_specials (fupd_lambda (cons UChar.lambda))
                                              (term_grammar()))

  fun traceset n = if n = 0 then
                     if !master_unicode_switch then
                       (master_unicode_switch := false;
                        set_trace "Greek tyvars" 0;
                        bare_lambda();
                        lift0 ProvideUnicode.disable_all)
                     else ()
                   else if not (!master_unicode_switch) then
                     (master_unicode_switch := true;
                      set_trace "Greek tyvars" 1;
                      unicode_lambda();
                      lift0 ProvideUnicode.enable_all)
                   else ()
  fun traceget () = if !master_unicode_switch then 1 else 0

  val _ = register_ftrace ("Unicode", (traceget, traceset), 1)
  val _ = unicode_lambda()

  val _ = traceset 1

  val _ = Theory.register_onload (fn s => lift ProvideUnicode.apply_thydata s)

end




fun temp_add_type s = let open parse_type in
   the_type_grammar := new_tyop (!the_type_grammar) s;
   type_grammar_changed := true;
   term_grammar_changed := true
 end;

fun add_type s = let in
   temp_add_type s;
   update_grms "add_type" ("temp_add_type", Lib.quote s)
 end

fun temp_add_infix_type {Name, ParseName, Assoc, Prec} =
 let open parse_type
 in the_type_grammar
       := new_binary_tyop (!the_type_grammar)
              {precedence = Prec, infix_form = ParseName,
               opname = Name, associativity = Assoc};
    type_grammar_changed := true;
    term_grammar_changed := true
 end

fun add_infix_type (x as {Name, ParseName, Assoc, Prec}) = let in
  temp_add_infix_type x;
  update_grms "add_infix_type"
              ("temp_add_infix_type",
               String.concat
                 ["{Name = ", quote Name,
                  ", ParseName = ",
                  case ParseName of NONE => "NONE"
                                  | SOME s => "SOME "^quote s,
                  ", Assoc = ", assocToString Assoc,
                  ", Prec = ", Int.toString Prec, "}"])
 end

fun temp_type_abbrev (s, ty) = let
  val params = Listsort.sort Type.compare (type_vars ty)
  val (num_vars, pset) =
      List.foldl (fn (ty,(i,pset)) => (i + 1, Binarymap.insert(pset,ty,i)))
                 (0, Binarymap.mkDict Type.compare) params
  fun mk_structure pset ty =
      if is_vartype ty then type_grammar.PARAM (Binarymap.find(pset, ty))
      else let
          val {Thy,Tyop,Args} = dest_thy_type ty
        in
          type_grammar.TYOP {Thy = Thy, Tyop = Tyop,
                             Args = map (mk_structure pset) Args}
        end
in
  the_type_grammar := type_grammar.new_abbreviation (!the_type_grammar)
                                                    (s, mk_structure pset ty);
  type_grammar_changed := true;
  term_grammar_changed := true
end handle GrammarError s => raise ERROR "type_abbrev" s

fun type_abbrev (s, ty) = let
in
  temp_type_abbrev (s, ty);
  full_update_grms ("temp_type_abbrev",
                    String.concat ["(", mlquote s, ", ",
                                   PP.pp_to_string (!Globals.linewidth)
                                                   (TheoryPP.pp_type "U" "T")
                                                   ty,
                                   ")"],
                    SOME (mk_thy_const{Name = "ARB", Thy = "bool", Ty = ty})
                   )
end;

fun temp_disable_tyabbrev_printing s = let
  val tyg = the_type_grammar
in
  tyg := type_grammar.disable_abbrev_printing s (!tyg);
  type_grammar_changed := true;
  term_grammar_changed := true
end

fun disable_tyabbrev_printing s = let
in
  temp_disable_tyabbrev_printing s;
  update_grms "disable_tyabbrev_printing"
              ("temp_disable_tyabbrev_printing", mlquote s)
end


(* Not persistent? *)
fun temp_set_associativity (i,a) = let in
   the_term_grammar := set_associativity_at_level (term_grammar()) (i,a);
   term_grammar_changed := true
 end


fun temp_add_infix(s, prec, associativity) =
 let open term_grammar Portable
 in
   the_term_grammar
    := add_rule (!the_term_grammar)
          {term_name=s, block_style=(AroundSamePrec, (INCONSISTENT,0)),
           fixity=Infix(associativity, prec),
           pp_elements = [HardSpace 1, RE(TOK s), BreakSpace(1,0)],
           paren_style = OnlyIfNecessary}
   ;
   term_grammar_changed := true
  end handle GrammarError s => raise ERROR "add_infix" ("Grammar Error: "^s)

fun add_infix (s, prec, associativity) = let in
  temp_add_infix(s,prec,associativity);
  update_grms "add_infix"
              ("temp_add_infix", String.concat
                  ["(", quote s, ", ", Int.toString prec, ", ",
                        assocToString associativity,")"])
 end;


local open term_grammar
in
fun fixityToString Prefix  = "Prefix"
  | fixityToString Binder  = "Binder"
  | fixityToString (RF rf) = term_grammar.rule_fixityToString rf

fun relToString TM = "TM"
  | relToString (TOK s) = "TOK "^quote s
end

fun rellistToString [] = ""
  | rellistToString [x] = relToString x
  | rellistToString (x::xs) = relToString x ^ ", " ^ rellistToString xs

fun block_infoToString (Portable.CONSISTENT, n) =
        "(CONSISTENT, "^Int.toString n^")"
  | block_infoToString (Portable.INCONSISTENT, n) =
    "(INCONSISTENT, "^Int.toString n^")"

fun ParenStyleToString Always = "Always"
  | ParenStyleToString OnlyIfNecessary = "OnlyIfNecessary"
  | ParenStyleToString ParoundName = "ParoundName"
  | ParenStyleToString ParoundPrec = "ParoundPrec"

fun BlockStyleToString AroundSameName = "AroundSameName"
  | BlockStyleToString AroundSamePrec = "AroundSamePrec"
  | BlockStyleToString AroundEachPhrase = "AroundEachPhrase"
  | BlockStyleToString NoPhrasing = "NoPhrasing"


fun ppToString pp =
  case pp
   of PPBlock(ppels, bi) =>
      "PPBlock(["^pplistToString ppels^"], "^ block_infoToString bi^")"
    | EndInitialBlock bi => "EndInitialBlock "^block_infoToString bi
    | BeginFinalBlock bi => "BeginFinalBlock "^block_infoToString bi
    | HardSpace n => "HardSpace "^Int.toString n^""
    | BreakSpace(n,m) => "BreakSpace("^Int.toString n^", "^Int.toString m^")"
    | RE rel => relToString rel
    | _ => raise Fail "Don't want to print out First or Last TM values"
and
    pplistToString [] = ""
  | pplistToString [x] = ppToString x
  | pplistToString (x::xs) = ppToString x ^ ", " ^ pplistToString xs





(*---------------------------------------------------------------------------*)
(* Apply a function to its argument. If it fails, revert the grammars        *)
(*---------------------------------------------------------------------------*)

fun try_grammar_extension f x =
 let val (tyG,tmG) = current_grammars()
     val updates = !grm_updates
 in
    f x handle e
    => (the_term_grammar := tmG;
        the_type_grammar := tyG;
        term_grammar_changed := true;
        type_grammar_changed := true;
        grm_updates := updates; raise e)
 end;

fun includes_unicode s = not (CharVector.all (fn c => Char.ord c < 128) s)
val els_include_unicode = let
in
  List.exists (fn RE (TOK s) => includes_unicode s | _ => false)
end

fun temp_add_binder name = let in
   the_term_grammar :=
     add_binder {term_name = name, tok = name} (!the_term_grammar);
   term_grammar_changed := true
 end

fun add_binder name = let in
    temp_add_binder name;
    update_grms "add_binder" ("temp_add_binder",
                              String.concat
                                ["(", quote name,
                                 ", std_binder_precedence)"])
  end

datatype 'a erroption = Error of string | Some of 'a
fun prule_to_grule {term_name,fixity,pp_elements,paren_style,block_style} = let
  open term_grammar
in
  case fixity of
    Prefix => Error "Fixities of Prefix do not affect the grammar"
  | Binder => let
    in
      case rule_elements pp_elements of
        [TOK s] => Some (BRULE {term_name = term_name, tok = s})
      | _ => Error "Rules for binders must feature exactly one TOK and no TMs"
    end
  | RF rf => Some (GRULE {term_name = term_name, fixity = rf,
                          pp_elements = pp_elements,
                          paren_style = paren_style,
                          block_style = block_style})
end

fun temp_add_grule gr = let
  val uni_on = get_tracefn "Unicode" () > 0
  val toks = userdelta_toks gr
in
  if List.exists includes_unicode toks then let
    in
      if uni_on then ()
      else HOL_WARNING "Parse" "temp_add_rule"
                       "Adding a Unicode-ish rule without Unicode trace \
                       \being true";
      the_term_grammar := ProvideUnicode.temp_uadd_rule uni_on {
        u = toks, term_name = userdelta_name gr,
        newrule = gr,
        oldtok = NONE
      } (term_grammar());
      term_grammar_changed := true
    end
  else let
    in
      the_term_grammar := term_grammar.add_delta gr (!the_term_grammar) ;
      term_grammar_changed := true
    end
end handle GrammarError s => raise ERROR "add_rule" ("Grammar error: "^s)

fun temp_add_rule rule =
    case prule_to_grule rule of
      Error s => raise mk_HOL_ERR "Parse" "add_rule" s
    | Some gr => temp_add_grule gr

fun add_rule (r as {term_name, fixity, pp_elements,
                    paren_style, block_style = (bs,bi)}) = let in
  temp_add_rule r;
  update_grms "add_rule"
              ("temp_add_rule",
               String.concat
                 ["{term_name = ", quote term_name,
                  ", fixity = ", fixityToString fixity, ",\n",
                  "pp_elements = [", pplistToString pp_elements, "],\n",
                  "paren_style = ", ParenStyleToString paren_style,",\n",
                  "block_style = (", BlockStyleToString bs, ", ",
                  block_infoToString bi,")}"])
 end

fun temp_overload_on (s, t) = let
  val uni_on = get_tracefn "Unicode" () > 0
in
  if includes_unicode s then
    (if not uni_on then
       HOL_WARNING "Parse" "overload_on"
                   "Adding a Unicode-ish rule without Unicode trace \
                   \being true"
     else
       term_grammar_changed := true;
     Unicode.temp_uoverload_on (s,t))
  else
    (the_term_grammar := fupdate_overload_info
                             (Overload.add_overloading (s, t))
                             (term_grammar());
     term_grammar_changed := true)
end

fun overload_on (s, t) = let
in
  temp_overload_on (s, t);
  full_update_grms
    ("temp_overload_on",
     String.concat ["(", quote s, ", ", minprint t, ")"],
    SOME t)
end


fun temp_add_listform x = let open term_grammar in
    the_term_grammar := add_listform (term_grammar()) x;
    term_grammar_changed := true
  end

fun add_listform x = let
  val {separator,leftdelim,rightdelim,cons,nilstr,block_info} = x
in
  temp_add_listform x;
  update_grms "add_listform"
              ("temp_add_listform",
               String.concat
                 ["{separator = [",   pplistToString separator, "]\n",
                  ", leftdelim = [",  pplistToString leftdelim, "]\n",
                  ", rightdelim = [", pplistToString rightdelim, "]\n",
                  ", cons = ",        quote cons,
                  ", nilstr = ",      quote nilstr,
                  ", block_info = ",  block_infoToString block_info,
                  "}"])
 end

fun temp_add_bare_numeral_form x =
 let val _ = Lib.can Term.prim_mk_const{Name="NUMERAL", Thy="arithmetic"}
             orelse raise ERROR "add_numeral_form"
            ("Numeral support not present; try load \"arithmeticTheory\"")
 in
    the_term_grammar := term_grammar.add_numeral_form (term_grammar()) x;
    term_grammar_changed := true
 end

fun add_bare_numeral_form (c, stropt) =
    (temp_add_bare_numeral_form (c, stropt);
     update_grms "add_bare_numeral_form"
                 ("temp_add_bare_numeral_form",
                  String.concat
                    ["(#", quote(str c), ", ",
                     case stropt of
                       NONE => "NONE"
                     | SOME s => "SOME "^quote s,")"]));

fun temp_give_num_priority c = let open term_grammar in
    the_term_grammar := give_num_priority (term_grammar()) c;
    term_grammar_changed := true
  end

fun give_num_priority c = let in
  temp_give_num_priority c;
  update_grms "give_num_priority" ("temp_give_num_priority",
                                   String.concat ["#", Lib.quote(str c)])
 end

fun temp_remove_numeral_form c = let in
   the_term_grammar := term_grammar.remove_numeral_form (term_grammar()) c;
   term_grammar_changed := true
  end

fun remove_numeral_form c = let in
  temp_remove_numeral_form c;
  update_grms "remove_numeral_form" ("temp_remove_numeral_form",
                                     String.concat ["#", Lib.quote(str c)])
  end

fun temp_associate_restriction (bs, s) =
 let val lambda = #lambda (specials (term_grammar()))
     val b = if mem bs lambda then NONE else SOME bs
 in
    the_term_grammar :=
    term_grammar.associate_restriction (term_grammar())
                                       {binder = b, resbinder = s};
    term_grammar_changed := true
 end

fun associate_restriction (bs, s) = let in
   temp_associate_restriction (bs, s);
   update_grms "associate_restriction"
               ("temp_associate_restriction",
                String.concat["(", quote bs, ", ", quote s, ")"])
 end

fun temp_remove_rules_for_term s = let open term_grammar in
    the_term_grammar := remove_standard_form (term_grammar()) s;
    term_grammar_changed := true
  end

fun remove_rules_for_term s = let in
   temp_remove_rules_for_term s;
   update_grms "remove_rules_for_term" ("temp_remove_rules_for_term", quote s)
 end

fun temp_set_mapped_fixity {fixity,term_name,tok} = let
  val nmtok = {term_name = term_name, tok = tok}
in
  temp_remove_termtok nmtok;
  case fixity of
    Prefix => ()
  | RF rf => temp_add_grule
                 (GRULE (standard_mapped_spacing {fixity = rf, tok = tok,
                                                  term_name = term_name}))
  | Binder => if term_name <> tok then
                raise ERROR "set_mapped_fixity"
                            "Can't map binders to different strings"
              else
                temp_add_grule (BRULE nmtok)
end

fun set_mapped_fixity (arg as {fixity,term_name,tok}) = let
in
  temp_set_mapped_fixity arg;
  update_grms "set_mapped_fixity"
              ("(fn () => (temp_set_mapped_fixity {term_name = "^
               quote term_name^", "^ "tok = "^quote tok^", fixity = "^
               fixityToString fixity^"}))", "()")
end

fun temp_set_fixity s f =
    temp_set_mapped_fixity {fixity = f, term_name = s, tok = s}

fun set_fixity s f = let in
    temp_set_fixity s f;
    update_grms "set_fixity"
                ("(temp_set_fixity "^quote s^")", "("^fixityToString f^")")
 end

(* ----------------------------------------------------------------------
    Post-processing : adding user transformations to the parse processs.
   ---------------------------------------------------------------------- *)

fun temp_add_absyn_postprocessor x = let
  open term_grammar
in
  the_term_grammar := new_absyn_postprocessor x (!the_term_grammar)
end

fun add_absyn_postprocessor (x as (nm,_)) = let
in
  temp_add_absyn_postprocessor x;
  update_grms "add_absyn_postprocessor"
              ("temp_add_absyn_postprocessor", "(" ^ quote nm ^ ", " ^ nm ^ ")")
end


(*-------------------------------------------------------------------------
        Overloading
 -------------------------------------------------------------------------*)

fun temp_overload_on_by_nametype s {Name, Thy} = let
  open term_grammar
in
  the_term_grammar :=
    fupdate_overload_info
    (Overload.add_actual_overloading {opname=s, realname=Name, realthy=Thy})
    (term_grammar());
  term_grammar_changed := true
end

fun overload_on_by_nametype s (r as {Name, Thy}) = let in
   temp_overload_on_by_nametype s r;
   full_update_grms
     ("(temp_overload_on_by_nametype "^quote s^")",
      String.concat
        [" {Name = ", quote Name, ", ", "Thy = ", quote Thy, "}"],
      SOME (prim_mk_const r)
     )
 end

fun temp_send_to_back_overload s {Name, Thy} = let
  open term_grammar
in
  the_term_grammar :=
    fupdate_overload_info
    (Overload.send_to_back_overloading {opname=s, realname=Name, realthy=Thy})
    (term_grammar());
  term_grammar_changed := true
end

fun send_to_back_overload s (r as {Name, Thy}) = let in
   temp_send_to_back_overload s r;
   full_update_grms
     ("(temp_send_to_back_overload "^quote s^")",
      String.concat
        [" {Name = ", quote Name, ", ", "Thy = ", quote Thy, "}"],
      SOME (prim_mk_const r)
     )
 end

fun temp_bring_to_front_overload s {Name, Thy} = let
  open term_grammar
in
  the_term_grammar :=
    fupdate_overload_info
    (Overload.bring_to_front_overloading {opname=s, realname=Name, realthy=Thy})
    (term_grammar());
  term_grammar_changed := true
end

fun bring_to_front_overload s (r as {Name, Thy}) = let in
   temp_bring_to_front_overload s r;
   full_update_grms
     ("(temp_bring_to_front_overload "^quote s^")",
      String.concat
        [" {Name = ", quote Name, ", ", "Thy = ", quote Thy, "}"],
      SOME (prim_mk_const r)
     )
 end


fun temp_clear_overloads_on s = let
  open term_grammar
in
  the_term_grammar :=
    #1 (mfupdate_overload_info
        (Overload.remove_overloaded_form s) (term_grammar()));
  app (curry temp_overload_on s) (Term.decls s);
  term_grammar_changed := true
end

fun clear_overloads_on s = let in
  temp_clear_overloads_on s;
  update_grms "clear_overloads_on" ("temp_clear_overloads_on", quote s)
end

fun temp_remove_ovl_mapping s crec = let open term_grammar in
  the_term_grammar :=
    fupdate_overload_info (Overload.remove_mapping s crec) (term_grammar());
  term_grammar_changed := true
end

fun remove_ovl_mapping s (crec as {Name,Thy}) = let
in
  temp_remove_ovl_mapping s crec;
  update_grms "remove_ovl_mapping"
              ("(temp_remove_ovl_mapping "^quote s^")",
               String.concat
                 [" {Name = ", quote Name, ", ", "Thy = ", quote Thy, "}"])
end


fun temp_add_record_field (fldname, term) = let
  val recfldname = recsel_special^fldname
in
  temp_overload_on(recfldname, term)
end

fun add_record_field (fldname, term) = let
  val recfldname = recsel_special^fldname
in
  overload_on(recfldname, term)
end

fun temp_add_record_fupdate (fldname, term) = let
  val recfldname = recfupd_special ^ fldname
in
  temp_overload_on(recfldname, term)
end

fun add_record_fupdate (fldname, term) = let
  val recfldname = recfupd_special ^ fldname
in
  overload_on(recfldname, term)
end

fun temp_add_numeral_form (c, stropt) = let
  val _ =
    Lib.can Term.prim_mk_const{Name="NUMERAL", Thy="arithmetic"}
    orelse
      raise ERROR "add_numeral_form"
      ("Numeral support not present; try load \"arithmeticTheory\"")
  val num = Type.mk_thy_type {Tyop="num", Thy="num",Args = []}
  val fromNum_type = num --> alpha
  val const_record =
    case stropt of
      NONE => {Name = nat_elim_term, Thy = "arithmetic"}
    | SOME s =>
        case Term.decls s of
          [] => raise ERROR "add_numeral_form" ("No constant with name "^s)
        | h::_ => lose_constrec_ty (dest_thy_const h)
in
  temp_add_bare_numeral_form (c, stropt);
  temp_overload_on_by_nametype fromNum_str const_record;
  if isSome stropt then
    temp_overload_on_by_nametype num_injection const_record
  else ()
end

fun add_numeral_form (c, stropt) = let in
  temp_add_numeral_form (c, stropt);
  update_grms "add_numeral_form"
              ("temp_add_numeral_form",
               String.concat
               ["(#", quote (str c), ", ",
                case stropt of NONE => "NONE" | SOME s => "SOME "^quote s, ")"
               ])
 end


(*---------------------------------------------------------------------------
     Visibility of identifiers
 ---------------------------------------------------------------------------*)

fun hide s = let
  val (newg, (tms1,tms2)) =
    mfupdate_overload_info (Overload.remove_overloaded_form s)
                           (!the_term_grammar)
  fun to_nthyrec t = let
    val {Name,Thy,Ty} = dest_thy_const t
  in
    SOME {Name = Name, Thy = Thy}
  end handle HOL_ERR _ => NONE

in
  the_term_grammar := newg;
  term_grammar_changed := true;
  (List.mapPartial to_nthyrec tms1, List.mapPartial to_nthyrec tms2)
end;

fun update_overload_maps s nthyrec_pair = let
in
  the_term_grammar :=
    fupdate_overload_info (Overload.raw_map_insert s nthyrec_pair)
    (term_grammar());
  term_grammar_changed := true
end handle Overload.OVERLOAD_ERR s =>
  raise ERROR "update_overload_maps" ("Overload: "^s)

fun reveal s =
  case Term.decls s of
    [] => WARN "reveal" (s^" not a constant; reveal ignored")
  | cs => let
    in
      app (fn c => temp_overload_on (s, c)) cs
    end

fun known_constants() = term_grammar.known_constants (term_grammar())

fun is_constname s = let
  val oinfo = term_grammar.overload_info (term_grammar())
in
  Overload.is_overloaded oinfo s
end

fun hidden s =
  let val declared = Term.all_consts()
      val names = map (fst o Term.dest_const) declared
  in
    Lib.mem s (Lib.subtract names (known_constants()))
  end

fun set_known_constants sl = let
  val (ok_names, bad_names) = partition (not o null o Term.decls) sl
  val _ = List.app (fn s => WARN "set_known_constants"
                               (s^" not a constant; ignored")) bad_names
in
  the_term_grammar :=
    fupdate_overload_info (K Overload.null_oinfo) (term_grammar());
  app reveal ok_names
end

fun add_const s      = let
  val c = prim_mk_const{Name = s, Thy = current_theory()}
in
  overload_on(s,c)
end;


(*----------------------------------------------------------------------
  User changes to the printer and parser
  ----------------------------------------------------------------------*)

fun temp_add_user_printer (name, pattern, pfn) = let
in
  the_term_grammar :=
    term_grammar.add_user_printer (name, pattern, pfn)
                                  (term_grammar());
  term_grammar_changed := true
end

fun temp_remove_user_printer name = let
  val (newg, printfnopt) =
      term_grammar.remove_user_printer name (term_grammar())
in
  the_term_grammar := newg;
  term_grammar_changed := true;
  printfnopt
end


fun add_user_printer(name,pattern,pfn) = let
in
  update_grms "add_user_printer"
              ("temp_add_user_printer",
               String.concat ["(", quote name, ", ",
                              "#2 (parse_from_grammars min_grammars)",
                              "[QUOTE \"", minprint pattern, "\"], ",
                              name, ")"]);
  temp_add_user_printer(name, pattern, pfn)
end;

fun remove_user_printer name = let
in
  update_grms "remove_user_printer"
              ("(ignore o temp_remove_user_printer)", mlquote name);
  temp_remove_user_printer name
end;


(*---------------------------------------------------------------------------
     Updating the global and local grammars when a theory file is
     loaded.

     The function "update_grms" updates both the local and global
     grammars by pointer swapping. Ugh! Relies on fact that no
     other state than that of the current global grammars changes
     in a call to f.

     TODO: handle exceptions coming from application of "f" to "x"
           and print out informative messages.
 ---------------------------------------------------------------------------*)

fun update_grms f x = let
  val _ = f x                          (* update global grammars *)
    handle HOL_ERR {origin_structure, origin_function, message} =>
      (WARN "update_grms"
       ("Update to global grammar failed in "^origin_function^
        " with message: "^message^"\nproceeding anyway."))

  val (tyG, tmG) = current_grammars()  (* save global grm. values *)
  val (tyL0,tmL0) = current_lgrms()    (* read local grm. values *)
  val _ = the_type_grammar := tyL0     (* mv locals into globals *)
  val _ = the_term_grammar := tmL0
  val _ = f x                          (* update global (really local) grms *)
    handle HOL_ERR {origin_structure, origin_function, message} =>
      (WARN "update_grms"
       ("Update to local grammar failed in "^origin_function^
        " with message: "^message^"\nproceeding anyway."))
  val (tyL1, tmL1) = current_grammars()
  val _ = the_lty_grm := tyL1          (* mv updates into locals *)
  val _ = the_ltm_grm := tmL1
in
  the_type_grammar := tyG;             (* restore global grm. values *)
  the_term_grammar := tmG
end

fun merge_grm (gname, (tyG0, tmG0)) (tyG1, tmG1) =
  (type_grammar.merge_grammars (tyG0, tyG1),
   term_grammar.merge_grammars (tmG0, tmG1)
  )
  handle HOLgrammars.GrammarError s
   => (Feedback.HOL_WARNING "Parse" "mk_local_grms"
       (String.concat["Error ", s, " while merging grammar ",
                      gname, "; ignoring it.\n"])
      ; (tyG1, tmG1));

fun mk_local_grms [] = raise ERROR "mk_local_grms" "no grammars"
  | mk_local_grms ((n,gg)::t) =
      let val (ty_grm0,tm_grm0) = itlist merge_grm t gg
      in the_lty_grm := ty_grm0;
         the_ltm_grm := tm_grm0
      end;

fun parent_grammars () = let
  open Theory
  fun echo s = (quote s, s)
  fun grm_string "min" = echo "min_grammars"
    | grm_string s     = echo (s^"Theory."^s^"_grammars")
  val ct = current_theory()
in
  case parents ct of
    [] => raise ERROR "parent_grammars"
                        ("no parents found for theory "^quote ct)
  | plist => map grm_string plist
 end;

local fun sig_addn s = String.concat
       ["val ", s, "_grammars : type_grammar.grammar * term_grammar.grammar"]
      open Portable
in
fun setup_grammars (oldname, thyname) = let
in
  if not (null (!grm_updates)) andalso thyname <> oldname then
    HOL_WARNING "Parse" "setup_grammars"
                ("\"new_theory\" is throwing away grammar changes for "^
                 "theory "^oldname^":\n"^
                 String.concat (map (fn (s1, s2, _) => s1 ^ " - " ^ s2 ^ "\n")
                                    (!grm_updates)))
  else ();
  grm_updates := [];
  adjoin_to_theory
  {sig_ps = SOME (fn pps => Portable.add_string pps (sig_addn thyname)),
   struct_ps = SOME (fn ppstrm =>
     let val {add_string,add_break,begin_block,end_block,add_newline,...}
              = with_ppstream ppstrm
         val B  = begin_block CONSISTENT
         val IB = begin_block INCONSISTENT
         val EB = end_block
         fun pr_sml_list pfun L =
           (B 0; add_string "["; IB 0;
               pr_list pfun (fn () => add_string ",")
                            (fn () => add_break(0,0))  L;
            EB(); add_string "]"; EB())
         fun pp_update(f,x,topt) =
             if isSome topt andalso
                not (Theory.uptodate_term (valOf topt))
             then ()
             else
               (B 5;
                add_string "val _ = update_grms"; add_break(1,0);
                add_string f; add_break(1,0);
                B 0; add_string x;  (* can be more fancy *)
                EB(); EB())
         fun pp_pair f1 f2 (x,y) =
              (B 0; add_string"(";
                    B 0; f1 x;
                         add_string",";add_break(0,0);
                         f2 y;
                    EB(); add_string")"; EB())
         val (names,rules) = partition (equal"reveal" o #1)
                                (List.rev(!grm_updates))
         val reveals = map #2 names
         val _ = grm_updates := []
     in
       B 0;
         add_string "local open Portable GrammarSpecials Parse";
         add_newline();
         add_string "in"; add_newline();
         add_string "val _ = mk_local_grms [";
             IB 0; pr_list (pp_pair add_string add_string)
                          (fn () => add_string ",")
                          (fn () => add_break(1,0)) (parent_grammars());
             EB();
         add_string "]"; add_newline();
         B 10; add_string "val _ = List.app (update_grms reveal)";
              add_break(1,0);
              pr_sml_list add_string reveals;
         EB(); add_newline();
         pr_list pp_update (fn () => ()) add_newline rules;
         add_newline();
         add_string (String.concat
             ["val ", thyname, "_grammars = Parse.current_lgrms()"]);
         add_newline();
         add_string "end"; add_newline();
       EB()
     end)}
 end
end

val _ = let
  fun rawpp_thm pps th =
      Lib.with_flag (current_backend, PPBackEnd.raw_terminal)
                    (pp_thm pps) th
in
  Theory.pp_thm := rawpp_thm
end
val _ = Theory.after_new_theory setup_grammars;


fun export_theorems_as_docfiles dirname thms = let
  val {arcs,isAbs,vol} = Path.fromString dirname
  fun check_arcs checked arcs =
    case arcs of
      [] => checked
    | x::xs => let
        val nextlevel = Path.concat (checked, x)
      in
        if FileSys.access(nextlevel, []) then
          if FileSys.isDir nextlevel then check_arcs nextlevel xs
          else raise Fail (nextlevel ^ " exists but is not a directory")
        else let
        in
          FileSys.mkDir nextlevel
          handle (OS.SysErr(s, erropt)) => let
            val part2 = case erropt of SOME err => OS.errorMsg err | NONE => ""
          in
            raise Fail ("Couldn't create directory "^nextlevel^": "^s^" - "^
                        part2)
          end;
          check_arcs nextlevel xs
        end
      end
  val dirname = check_arcs (Path.toString {arcs=[],isAbs=isAbs,vol=vol}) arcs
  fun write_thm (thname, thm) = let
    open Theory TextIO
    val outstream = openOut (Path.concat (dirname, thname^".doc"))
  in
    output(outstream, "\\THEOREM "^thname^" "^current_theory()^"\n");
    output(outstream, thm_to_string thm);
    output(outstream, "\n\\ENDTHEOREM\n");
    closeOut outstream
  end
in
  app write_thm thms
end handle IO.Io {function,name,...} =>
           HOL_WARNING "Parse" "export_theorems_as_docfiles"
                       ("Giving up on IO error: "^function^" : "^name)
         | Fail s =>
           HOL_WARNING "Parse" "export_theorems_as_docfiles"
                       ("Giving up after error: "^s)

(*---------------------------------------------------------------------------
     pp_element values that are brought across from term_grammar.
     Tremendous potential for confusion: TM and TOK are constructed
     values, but not constructors, here. Other things of this ilk
     are the constructors for the datatypes pp_element,
     PhraseBlockStyle, and ParenStyle.
 ---------------------------------------------------------------------------*)

fun TM x = x; fun TOK x = x;   (* remove constructor status *)

val TM = term_grammar.RE term_grammar.TM
val TOK = term_grammar.RE o term_grammar.TOK

(* ----------------------------------------------------------------------
    hideous hack section
   ---------------------------------------------------------------------- *)

    val _ = initialise_typrinter
            (fn G => type_pp.pp_type G PPBackEnd.raw_terminal)
    val _ = Definition.new_specification_hook := List.app add_const;

(* when new_theory is called, and if the new theory has the same name
   as the theory segment we were in anyway, then arrange that
   constants from this segment in the overload info section are removed.

   This needs to be done because no such constant can exist any more *)

  fun clear_thy_consts_from_oinfo thy oinfo = let
    val all_parse_consts = Overload.oinfo_ops oinfo
    fun bad_parse_guy (nm, {actual_ops, ...}) = let
      fun bad_guy t = let
        val {Name,Thy,...} = dest_thy_const t
      in
        if Thy = thy then SOME (nm, {Name = Name, Thy = Thy})
        else NONE
      end
    in
      List.mapPartial bad_guy actual_ops
    end
    val parses_to_remove = List.concat (map bad_parse_guy all_parse_consts)
    val all_print_consts = Overload.print_map oinfo
    fun bad_print_guy (x as {Name,Thy}, nm) =
        if Thy = thy then SOME (nm, x) else NONE
    val prints_to_remove = List.mapPartial bad_print_guy all_print_consts
    fun foldthis ((nm, r), oi) = Overload.remove_mapping nm r oi
  in
    foldl foldthis (foldl foldthis oinfo parses_to_remove) prints_to_remove
  end

  fun clear_thy_consts_from_grammar thy = let
    val new_grammar =
        term_grammar.fupdate_overload_info (clear_thy_consts_from_oinfo thy)
                                           (term_grammar())
  in
    the_term_grammar := new_grammar;
    term_grammar_changed := true
  end

  val _ = after_new_theory
          (fn (old, new) => if old = new then clear_thy_consts_from_grammar old
                            else ())

end
