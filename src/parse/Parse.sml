structure Parse :> Parse =
struct

open Feedback HolKernel HOLgrammars GrammarSpecials term_grammar type_grammar
open term_grammar_dtype

type pp_element = term_grammar.pp_element
type PhraseBlockStyle = term_grammar.PhraseBlockStyle
type ParenStyle = term_grammar.ParenStyle
type block_info = term_grammar.block_info
type associativity = HOLgrammars.associativity
type 'a frag = 'a Portable.frag
type 'a pprinter = 'a -> HOLPP.pretty

val ERROR = mk_HOL_ERR "Parse";
val ERRORloc = mk_HOL_ERRloc "Parse";
val WARN  = HOL_WARNING "Parse"

val post_process_term = Preterm.post_process_term
val quote = Lib.mlquote

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

val Infixl       = fn i => Infix(LEFT, i)
val Infixr       = fn i => Infix(RIGHT, i)


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
  case getEnv "COLORTERM" of
      SOME _ => vt100_terminal
    | NONE =>
      case getEnv "TERM" of
          SOME s => if String.isPrefix "xterm" s orelse
                       String.isPrefix "tmux" s then vt100_terminal
                    else raw_terminal
        | NONE => raw_terminal
end

val current_backend : PPBackEnd.t ref =
    ref (if !Globals.interactive then interactive_ppbackend()
         else PPBackEnd.raw_terminal)

fun rawterm_pp f x =
    Lib.with_flag(current_backend, PPBackEnd.raw_terminal) f x

fun mlower m =
  case smpp.lower m term_pp_utils.dflt_pinfo of
      NONE => raise Fail "p/printer returned NONE!"
    | SOME(p, _, _) => p

fun ulower fm x = mlower (fm x)

(*---------------------------------------------------------------------------
         local grammars
 ---------------------------------------------------------------------------*)

val the_lty_grm = ref type_grammar.empty_grammar
val the_ltm_grm = ref term_grammar.stdhol
fun current_lgrms() = (!the_lty_grm, !the_ltm_grm);


fun fixity s = term_grammar.get_precedence (term_grammar()) s

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

fun get_term_printer () = ulower (!term_printer)

fun set_term_printer new_pp_term =
  let
    open smpp
    val old_pp_term = !term_printer
  in
    term_printer := lift new_pp_term;
    ulower old_pp_term
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

val dflt_pinfo = term_pp_utils.dflt_pinfo

fun pp_type ty =
  let
    open smpp
    val _ = update_type_fns()
    val mptr = smpp.add_string ":" >> !type_printer (!current_backend) ty
  in
    lower mptr dflt_pinfo |> valOf |> #1
  end

val type_to_string = rawterm_pp (ppstring pp_type)
val print_type = print o type_to_string

fun type_pp_with_delimiters ppfn ty =
  let
    open Portable Globals smpp
  in
    mlower (
      add_string (!type_pp_prefix) >>
      block CONSISTENT (UTF8.size (!type_pp_prefix)) (lift ppfn ty) >>
      add_string (!type_pp_suffix)
    )
  end

fun print_from_grammars (tyG, tmG) =
  (ulower (type_pp.pp_type tyG (!current_backend)),
   ulower (term_pp.pp_term tmG tyG (!current_backend)))

fun stdprint x =
  HOLPP.prettyPrint (TextIO.print, !Globals.linewidth) x

fun print_term_by_grammar Gs t =
  let
    val (_, termprinter) = print_from_grammars Gs
  in
    stdprint (termprinter t) ;
    print "\n"
end

val min_grammars = (type_grammar.min_grammar, term_grammar.min_grammar)

type grammarDB_info = type_grammar.grammar * term_grammar.grammar

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

(* Pretty-print the grammar rules *)
fun print_term_grammar() = let
  fun tmprint g = snd (print_from_grammars (!the_type_grammar,g))
  fun ppg g = let
    open smpp
  in
    block PP.CONSISTENT 0 (
      prettyprint_grammar_rules (lift o tmprint) (ruleset g) >>
      add_newline
    )
  end
in
  stdprint (ulower ppg (!the_term_grammar))
end


(* Pretty-printing terms and types without certain overloads or abbreviations *)

fun overload_info_for s = let
  val (g,(ls1,ls2)) = term_grammar.mfupdate_overload_info
                        (Overload.remove_overloaded_form s)
                        (!the_term_grammar)
  val (_,ppfn0) = print_from_grammars (!the_type_grammar,g)
  val ppfn = ppfn0 |> Feedback.trace ("types", 1)
  val ppaction = let
    open smpp
  in
    block PP.CONSISTENT 0
     (add_string (s ^ " parses to:") >>
      add_break(1,2) >>
      block PP.INCONSISTENT 0 (pr_list (lift ppfn) add_newline ls1) >>
      add_newline >>
      add_string (s ^ " might be printed from:") >>
      add_break(1,2) >>
      block PP.INCONSISTENT 0 (pr_list (lift ppfn) add_newline ls2) >>
      add_newline)
  end
  fun act_topp pps a = ignore (a ((), pps))
in
  stdprint (mlower ppaction)
end

fun pp_term_without_overloads_on ls t = let
  fun remove s = #1 o term_grammar.mfupdate_overload_info
                        (Overload.remove_overloaded_form s)
  val g = Lib.itlist remove ls (!the_term_grammar)
in
  #2 (print_from_grammars (!the_type_grammar,g)) t
end
fun pp_term_without_overloads ls t = let
  fun remove (s,t) = term_grammar.fupdate_overload_info
                       (Overload.gen_remove_mapping s t)
  val g = Lib.itlist remove ls (!the_term_grammar)
in
  #2 (print_from_grammars (!the_type_grammar,g)) t
end
fun pp_type_without_abbrevs ls ty = let
  val g = Lib.itlist type_grammar.disable_abbrev_printing ls (!the_type_grammar)
in
  #1 (print_from_grammars (g,!the_term_grammar)) ty
end

(* ----------------------------------------------------------------------
    Top-level pretty-printing entry-points
   ---------------------------------------------------------------------- *)

fun pp_style_string (st, s) =
 let open Portable PPBackEnd
    val {add_string,ustyle,...} = (!current_backend)
    val m = ustyle st (add_string s)
 in
   mlower m
 end

fun add_style_to_string st s = ppstring pp_style_string (st, s);
fun print_with_style st s = stdprint (pp_style_string (st,s))

fun pp_term t = (update_term_fns(); mlower (!term_printer t))

val term_to_string = rawterm_pp (ppstring pp_term)
fun print_term t = stdprint (rawterm_pp pp_term t)

fun term_pp_with_delimiters ppfn tm =
  let
    open Portable Globals smpp
  in
    mlower (
      add_string (!term_pp_prefix) >>
      block CONSISTENT (UTF8.size (!term_pp_prefix)) (lift ppfn tm) >>
      add_string (!term_pp_suffix)
    )
  end

fun pp_thm th =
  let
    open Portable smpp
    val prt = lift pp_term
    fun repl ch alist = CharVector.tabulate (length alist, fn _ => ch)
    fun pp_terms b L =
      block INCONSISTENT 1 (
        add_string "[" >>
        (if b then pr_list prt (add_string "," >> add_break(1,0)) L
         else add_string (repl #"." L)) >>
        add_string "]"
      )
    val m =
        block INCONSISTENT 0 (
          if !Globals.max_print_depth = 0 then add_string " ... "
          else
            let
              open Globals
              val (tg,asl,st,sa) = (tag th, hyp th, !show_tags, !show_assums)
            in
              (if not st andalso not sa andalso null asl then nothing
               else
                 (if st then lift Tag.pp_tag tg else nothing) >>
                 add_break(1,0) >> pp_terms sa asl >> add_break(1,0)) >>
              add_string (!Globals.thm_pp_prefix) >>
              block CONSISTENT (UTF8.size (!Globals.thm_pp_prefix))
                    (prt (concl th)) >>
              add_string (!Globals.thm_pp_suffix)
            end
        )
  in
    mlower m
  end;

val thm_to_string = rawterm_pp (ppstring pp_thm)
val print_thm = print o thm_to_string

(*---------------------------------------------------------------------------
     Parse into preterm type
 ---------------------------------------------------------------------------*)

fun absyn_to_preterm a = TermParse.absyn_to_preterm (term_grammar()) a

fun Preterm q =
  case (q |> Absyn |> absyn_to_preterm) Pretype.Env.empty of
      errormonad.Error e => raise Preterm.mkExn e
    | errormonad.Some (_, pt) => pt

val absyn_to_term =
    TermParse.absyn_to_term (SOME (term_to_string, type_to_string))


(*---------------------------------------------------------------------------
     Parse into term type.
 ---------------------------------------------------------------------------*)

fun Term q = absyn_to_term (term_grammar()) (Absyn q)

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

fun smashErrm m =
  case m Pretype.Env.empty of
      errormonad.Error e => raise Preterm.mkExn e
    | errormonad.Some (_, result) => result
val stdprinters = SOME(term_to_string,type_to_string)

fun parse_in_context FVs q =
  let
    open errormonad
    val m =
        (q |> Absyn |> absyn_to_preterm) >-
        TermParse.ctxt_preterm_to_term stdprinters NONE FVs
  in
    smashErrm m
  end

fun grammar_parse_in_context(tyg,tmg) ctxt q =
    TermParse.ctxt_term stdprinters tmg tyg NONE ctxt q |> smashErrm

fun grammar_typed_parses_in_context (tyg,tmg) ty ctxt q =
  TermParse.ctxt_termS tmg tyg (SOME ty) ctxt q

fun grammar_typed_parse_in_context gs ty ctxt q =
  case seq.cases (grammar_typed_parses_in_context gs ty ctxt q) of
      SOME(tm, _) => tm
    | NONE => raise ERROR "grammar_typed_parse_in_context" "No consistent parse"

fun typed_parse_in_context ty ctxt q =
  let
    fun mkA q = Absyn.TYPED(locn.Loc_None, Absyn q, Pretype.fromType ty)
  in
    case seq.cases (TermParse.prim_ctxt_termS mkA (term_grammar()) ctxt q) of
        SOME (tm, _) => tm
      | NONE => raise ERROR "typed_parse_in_context" "No consistent parse"
  end

(*---------------------------------------------------------------------------
     Making temporary and persistent changes to the grammars.
 ---------------------------------------------------------------------------*)

val grm_updates = ref [] : (string * string * term option) list ref;

fun update_grms fname (x,y) = grm_updates := ((x,y,NONE) :: !grm_updates);
fun full_update_grms (x,y,opt) = grm_updates := ((x,y,opt) :: !grm_updates)

fun apply_udeltas uds =
  let
  in
    term_grammar_changed := true;
    the_term_grammar :=
      List.foldl (uncurry term_grammar.add_delta) (term_grammar()) uds
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

structure Unicode =
struct

  structure UChar = UnicodeChars
  fun unicode_version r =
    let
      open ProvideUnicode
      val uds = mk_unicode_version r (term_grammar())
    in
      apply_udeltas uds;
      List.app GrammarDeltas.record_tmdelta uds
    end

  fun temp_unicode_version r =
    ProvideUnicode.mk_unicode_version r (term_grammar()) |> apply_udeltas

end

fun core_process_tyds f x k =
  let
    open type_grammar
    val tyds = f x
  in
    the_type_grammar :=
      List.foldl (uncurry apply_delta) (!the_type_grammar) tyds;
    type_grammar_changed := true;
    term_grammar_changed := true;
    k tyds
  end

fun mk_temp_tyd f x = core_process_tyds f x (fn uds => ())
fun mk_perm_tyd f x =
  core_process_tyds f x (List.app GrammarDeltas.record_tydelta)

fun add_qtype0 kid = [NEW_TYPE kid]

val temp_add_qtype = mk_temp_tyd add_qtype0
val add_qtype = mk_perm_tyd add_qtype0

fun temp_add_type s = temp_add_qtype {Thy=current_theory(), Name = s}
fun add_type s = add_qtype {Thy=current_theory(), Name = s}

fun add_infix_type0 {Name,ParseName,Assoc,Prec} =
  let
    val pnm = case ParseName of NONE => Name | SOME s => s
  in
    [NEW_INFIX{Prec=Prec,ParseName=pnm,Name=Name,Assoc=Assoc}]
  end

val temp_add_infix_type = mk_temp_tyd add_infix_type0
val add_infix_type = mk_perm_tyd add_infix_type0

fun replace_exnfn fnm f x =
  f x handle HOL_ERR {message = m, origin_structure = s, ...} =>
             raise HOL_ERR {message = m, origin_function = fnm,
                            origin_structure = s}

fun thytype_abbrev0 r = [TYABBREV r]
val temp_thytype_abbrev = mk_temp_tyd thytype_abbrev0
val thytype_abbrev = mk_perm_tyd thytype_abbrev0

fun mktyabbrev_rec p (s,ty) = ({Thy = Theory.current_theory(), Name = s}, ty, p)
val temp_type_abbrev =
  replace_exnfn "temp_type_abbrev" temp_thytype_abbrev o mktyabbrev_rec false
val type_abbrev =
  replace_exnfn "type_abbrev" thytype_abbrev o mktyabbrev_rec false

fun disable_tyabbrev_printing0 s = [DISABLE_TYPRINT s]
val temp_disable_tyabbrev_printing = mk_temp_tyd disable_tyabbrev_printing0
val disable_tyabbrev_printing = mk_perm_tyd disable_tyabbrev_printing0

val temp_type_abbrev_pp =
    replace_exnfn "temp_type_abbrev_pp" temp_thytype_abbrev o
    mktyabbrev_rec true
val type_abbrev_pp =
    replace_exnfn "type_abbrev_pp" thytype_abbrev o mktyabbrev_rec true

fun remove_type_abbrev0 s = [RM_TYABBREV s]
val temp_remove_type_abbrev = mk_temp_tyd remove_type_abbrev0
val remove_type_abbrev = mk_perm_tyd remove_type_abbrev0

(* Not persistent? *)
fun temp_set_associativity (i,a) = let in
   the_term_grammar := set_associativity_at_level (term_grammar()) (i,a);
   term_grammar_changed := true
 end

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

val unicode_off_but_unicode_act_complaint = ref true
val _ = register_btrace("Parse.unicode_trace_off_complaints",
                        unicode_off_but_unicode_act_complaint)

fun make_add_rule gr =
  let
  in
    the_term_grammar := term_grammar.add_delta (GRULE gr) (!the_term_grammar);
    term_grammar_changed := true
  end handle GrammarError s => raise ERROR "add_rule" ("Grammar error: "^s)

fun core_udprocess f k x =
  let
    val uds = f x
    fun apply_one ud =
      case ud of
          GRULE gr => make_add_rule gr
        | _ => apply_udeltas [ud]
  in
    List.app apply_one uds ;
    k uds
  end

fun mk_temp f = core_udprocess f (fn uds => ())
fun mk_perm f = core_udprocess f (List.app GrammarDeltas.record_tmdelta)

fun remove_termtok0 r = [RMTMTOK r]
val temp_remove_termtok = mk_temp remove_termtok0
val remove_termtok = mk_perm remove_termtok0



val temp_add_rule = mk_temp (fn x => [GRULE x])
val add_rule = mk_perm (fn x => [GRULE x])

fun temp_add_infix(s, prec, associativity) =
   temp_add_rule (standard_spacing s (Infix(associativity, prec)))

fun add_infix (s, prec, associativity) =
  add_rule (standard_spacing s (Infix(associativity, prec)))

fun make_overload_on add (s, t) =
  (the_term_grammar := fupdate_overload_info (add (s, t)) (term_grammar());
   term_grammar_changed := true)

val temp_overload_on =
    make_overload_on Overload.add_overloading
val temp_inferior_overload_on =
    make_overload_on Overload.add_inferior_overloading

fun overload_on p =
  (make_overload_on Overload.add_overloading p ;
   GrammarDeltas.record_tmdelta (OVERLOAD_ON p))
fun inferior_overload_on p =
  (make_overload_on Overload.add_inferior_overloading p;
   GrammarDeltas.record_tmdelta (IOVERLOAD_ON p))

fun add_listform0 x = [GRULE (listform_to_rule x)]
val temp_add_listform = mk_temp add_listform0
val add_listform = mk_perm add_listform0

fun add_bare_numeral_form0 x = [ADD_NUMFORM x]
val temp_add_bare_numeral_form = mk_temp add_bare_numeral_form0
val add_bare_numeral_form = mk_perm add_bare_numeral_form0

fun add_strliteral_form0 {ldelim,inj} =
    let
      val (nm, _) = dest_const inj
                    handle HOL_ERR _ => raise ERROR "add_strliteral_form"
                                              "Injector must be constant"
      val _ = Literal.delim_pair{ldelim=ldelim} (* checks it's legit *)
              handle Fail s => raise ERROR "add_strliteral_form" s
      val injname = GrammarSpecials.mk_stringinjn_name ldelim
    in
      [IOVERLOAD_ON(injname,inj),
       ADD_STRLIT{ldelim=ldelim,tmnm=nm}]
    end
val temp_add_strliteral_form = mk_temp add_strliteral_form0
val add_strliteral_form = mk_perm add_strliteral_form0

fun remove_strliteral_form0 (r as {tmnm : string}) =
    case strlit_map (term_grammar()) r of
        NONE => raise ERROR "remove_strliteral_form"
                      "No such term as string literal injector"
      | SOME ldelim =>
        let
          open Overload
          val injname = GrammarSpecials.mk_stringinjn_name ldelim
          val oinfo = overload_info (term_grammar())
          fun find_term ({actual_ops,...} : overloaded_op_info) =
              List.find (fn t => #1 (dest_const t) = tmnm
                                 handle HOL_ERR _ => false)
                        actual_ops
        in
          case Option.mapPartial find_term (info_for_name oinfo injname) of
              NONE => raise ERROR "remove_strliteral_form"
                            "No constant with that name in overloading info"
            | SOME t => [
                RM_STRLIT r,
                RMOVMAP(injname, {Name = tmnm, Thy = #Thy (dest_thy_const t)})
              ]
        end
val temp_remove_strliteral_form = mk_temp remove_strliteral_form0
val remove_strliteral_form = mk_perm remove_strliteral_form0

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

fun associate_restriction0 (bs, s) =
 let val lambda = #lambda (specials (term_grammar()))
     val b = if mem bs lambda then NONE else SOME bs
 in
   [ASSOC_RESTR{binder = b, resbinder = s}]
 end

val temp_associate_restriction = mk_temp associate_restriction0
val associate_restriction = mk_perm associate_restriction0

fun temp_remove_rules_for_term s = let open term_grammar in
    the_term_grammar := remove_standard_form (term_grammar()) s;
    term_grammar_changed := true
  end

fun remove_rules_for_term s = let in
   temp_remove_rules_for_term s;
   GrammarDeltas.record_tmdelta (RMTMNM s)
 end

fun set_mapped_fixity0 (r as {tok,...}) =
  [RMTOK tok, r |> standard_mapped_spacing |> GRULE]
fun set_fixity0 (s, f) = set_mapped_fixity0 {fixity = f, term_name = s, tok = s}


val temp_set_mapped_fixity = mk_temp set_mapped_fixity0
val temp_set_fixity = curry (mk_temp set_fixity0)
val set_mapped_fixity = mk_perm set_mapped_fixity0
val set_fixity = curry (mk_perm set_fixity0)

(* ----------------------------------------------------------------------
    Post-processing : adding user transformations to the parse processs.
   ---------------------------------------------------------------------- *)

fun temp_add_absyn_postprocessor x = let
  open term_grammar
in
  the_term_grammar := new_absyn_postprocessor x (!the_term_grammar)
end

val add_absyn_postprocessor =
  mk_perm (fn s => [ADD_ABSYN_POSTP {codename = s}])

fun temp_remove_absyn_postprocessor s =
  let
    val (g, res) = term_grammar.remove_absyn_postprocessor s (!the_term_grammar)
  in
    the_term_grammar := g;
    term_grammar_changed := true;
    res
  end

fun temp_add_preterm_processor k f =
  the_term_grammar := term_grammar.new_preterm_processor k f (!the_term_grammar)

fun temp_remove_preterm_processor k =
  let
    val (g, res) = term_grammar.remove_preterm_processor k (!the_term_grammar)
  in
    the_term_grammar := g;
    term_grammar_changed := true;
    res
  end

(*-------------------------------------------------------------------------
        Overloading
 -------------------------------------------------------------------------*)

fun overload_on_by_nametype0 (s, recd as {Name, Thy}) = let
  val c = prim_mk_const recd handle HOL_ERR _ =>
              raise ERROR "temp_overload_on_by_nametype"
                    ("No such constant: "^Thy^"$"^Name)
in
  [OVERLOAD_ON (s,c)]
end

val temp_overload_on_by_nametype = curry (mk_temp overload_on_by_nametype0)
val overload_on_by_nametype = curry (mk_perm overload_on_by_nametype0)

val temp_send_to_back_overload =
    curry (mk_temp (fn skid => [MOVE_OVLPOSN{frontp = false, skid = skid}]))
val send_to_back_overload =
    curry (mk_perm (fn skid => [MOVE_OVLPOSN{frontp = false, skid = skid}]))

val temp_bring_to_front_overload =
    curry (mk_temp (fn skid => [MOVE_OVLPOSN{frontp = true, skid = skid}]))
val bring_to_front_overload =
    curry (mk_perm (fn skid => [MOVE_OVLPOSN{frontp = true, skid = skid}]))

fun clear_overloads_on0 s =
  CLR_OVL s :: map (fn t => OVERLOAD_ON(s,t)) (Term.decls s)
val temp_clear_overloads_on = mk_temp clear_overloads_on0
val clear_overloads_on = mk_perm clear_overloads_on0

fun remove_ovl_mapping0 (s, kid) = [RMOVMAP(s,kid)]
val temp_remove_ovl_mapping = curry (mk_temp remove_ovl_mapping0)
val remove_ovl_mapping = curry (mk_perm remove_ovl_mapping0)

val temp_gen_remove_ovl_mapping = curry (mk_temp (fn p => [GRMOVMAP p]))
val gen_remove_ovl_mapping = curry (mk_perm (fn p => [GRMOVMAP p]))

fun permahide t =
    let val {Name,Thy,...} = dest_thy_const t
    in
      remove_ovl_mapping Name {Name = Name, Thy = Thy}
    end

fun primadd_rcdfld f ovopn (fldname, t) = let
  val (d,r) = dom_rng (type_of t)
              handle HOL_ERR _ =>
              raise ERROR f "field selection term must be of type t -> a"
  val r = mk_var("rcd", d)
  val recfldname = recsel_special^fldname
in
  ovopn(recfldname, mk_abs(r, mk_comb(t, r)))
end

val temp_add_record_field =
    primadd_rcdfld "temp_add_record_field" temp_overload_on
val add_record_field = primadd_rcdfld "add_record_field" overload_on

fun buildfupdt f ovopn (fnm, t) = let
  val (argtys, rty) = strip_fun (type_of t)
  val err = ERROR f "fupdate term must be of type (a -> a) -> t -> t"
  val f = mk_var("f", hd argtys) handle Empty => raise err
  val x = mk_var("x", hd (tl argtys)) handle Empty => raise err
  val recfldname = recfupd_special ^ fnm
in
  ovopn(recfldname, list_mk_abs([f,x], list_mk_comb(t, [f,x])))
end

val temp_add_record_fupdate =
    buildfupdt "temp_add_record_fupdate" temp_overload_on
val add_record_fupdate = buildfupdt "add_record_fupdate" overload_on

fun add_numeral_form0 (c, stropt) = let
  val _ =
    Lib.can Term.prim_mk_const{Name="NUMERAL", Thy="arithmetic"}
    orelse
      raise ERROR "add_numeral_form"
      ("Numeral support not present; try load \"arithmeticTheory\"")
  val num = Type.mk_thy_type {Tyop="num", Thy="num",Args = []}
  val fromNum_type = num --> alpha
  val const =
    case stropt of
      NONE => prim_mk_const {Name = nat_elim_term, Thy = "arithmetic"}
    | SOME s =>
        case Term.decls s of
          [] => raise ERROR "add_numeral_form" ("No constant with name "^s)
        | h::_ => h
in
  ADD_NUMFORM (c, stropt) :: OVERLOAD_ON (fromNum_str, const) ::
  (if isSome stropt then [OVERLOAD_ON (num_injection, const)] else [])
end

val temp_add_numeral_form = mk_temp add_numeral_form0
val add_numeral_form = mk_perm add_numeral_form0

(* to print a term using current grammars,
  but with "non-trivial" overloads deleted *)
fun print_without_macros tm =
  let val (tyG, tmG) = current_grammars () ;
  in print_term_by_grammar (tyG, term_grammar.clear_overloads tmG) tm end ;

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

fun constant_string_printer s : term_grammar.userprinter =
  let
    fun result (tyg, tmg) _ _ ppfns (pgr,lgr,rgr) depth tm =
      let
        val {add_string,...} = ppfns
      in
        add_string s
      end
  in
    result
  end

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


val add_user_printer =
  mk_perm (fn (s,t) => [ADD_UPRINTER {codename=s,pattern=t}])

fun remove_user_printer name = let
in
  update_grms "remove_user_printer"
              ("(ignore o temp_remove_user_printer)", mlquote name);
  temp_remove_user_printer name
end;


(* ----------------------------------------------------------------------
     Updating the global and local grammars when a theory file is
     loaded.
   ---------------------------------------------------------------------- *)

fun gparents {thyname} =
  case GrammarAncestry.ancestry {thy = thyname} of
      [] => parents thyname
    | thys => thys

val {merge = merge_grammars0, set_parents = set_grammar_ancestry0,
     DB = grammarDB0, parents = gparents} =
    let
      open GrammarDeltas
      fun apply (TYD tyd) (tyG, tmG) = (type_grammar.apply_delta tyd tyG, tmG)
        | apply (TMD tmd) (tyG, tmG) = (tyG, term_grammar.add_delta tmd tmG)
      fun side_effect delta =
          let
            val (tyG, tmG) = apply delta (!the_type_grammar, !the_term_grammar)
          in
            the_type_grammar := tyG;
            the_term_grammar := tmG;
            type_grammar_changed := true;
            term_grammar_changed := true
          end
    in
      AncestryData.make {
        info = {tag = "grammar",
                initial_values = [("min", min_grammars)],
                apply_delta = apply},
        get_deltas = GrammarDeltas.thy_deltas,
        delta_side_effects = side_effect
      }
    end

fun merge_grammars sl =
    case merge_grammars0 sl of
        NONE => raise ERROR "merge_grammars"
                      ("None of " ^ String.concatWith ", " sl ^
                       " have defined grammars")
      | SOME gv => gv

fun grammarDB thyname = grammarDB0 thyname


fun set_grammar_ancestry slist =
    let
      val _ = GrammarDeltas.clear_deltas()
      val (tyg,tmg) = valOf (set_grammar_ancestry0 slist)
                      handle Option => raise Fail "No merge for grammars!"
    in
      the_type_grammar := tyg;
      the_term_grammar := tmg;
      type_grammar_changed := true;
      term_grammar_changed := true
    end

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
  adjoin_to_theory {
    sig_ps = SOME (fn _ => PP.add_string (sig_addn thyname)),
    struct_ps = NONE
  };
  adjoin_after_completion (
    fn () =>
       PP.add_string ("val " ^ thyname ^
                      "_grammars = valOf (Parse.grammarDB {thyname = " ^
                      quote thyname ^ "})\n")
  )
end
end (* local *)

val _ = let
  val rawpp_thm =
      pp_thm
        |> Lib.with_flag (current_backend, PPBackEnd.raw_terminal)
        |> trace ("paranoid string literal printing", 1)
in
  Theory.pp_thm := rawpp_thm
end

val _ = Theory.register_hook
            ("Parse.setup_grammars",
             (fn TheoryDelta.NewTheory{oldseg,newseg} =>
                 setup_grammars(oldseg, newseg)
               | _ => ()))


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
              (fn G => ulower (type_pp.pp_type G PPBackEnd.raw_terminal))
    val _ = let
      open TheoryDelta
      fun tempchk f nm = if Theory.is_temp_binding nm then ()
                         else ignore (f nm)
      fun hook ev =
          case ev of
            NewConstant{Thy,Name} => tempchk add_const Name
          | NewTypeOp{Thy,Name} => tempchk add_type Name
          | DelConstant{Thy,Name} => tempchk hide Name
          | _ => ()
    in
      Theory.register_hook ("Parse.watch_constants", hook)
    end

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

  val _ = Theory.register_hook
              ("Parse.clear_consts_from_grammar",
               fn TheoryDelta.NewTheory{oldseg,newseg} =>
                  if oldseg = newseg then
                    clear_thy_consts_from_grammar oldseg
                  else ()
                | _ => ())

end
