structure Unicode :> Unicode =
struct

structure UChar = UnicodeChars

open HolKernel Parse Feedback

open term_grammar

type term = Term.term

fun temp_set_term_grammar g = temp_set_grammars(type_grammar(), g)

val master_unicode_switch = ref true

datatype stored_data =
         RuleUpdate of { u : string, term_name : string,
                         newrule : (int option * grammar_rule),
                         oldtok : string option }
       | OverloadUpdate of { u : string, oldname : string option,
                             ts : term list }

(* This stored data record encodes a number of different options for
   the way in which a Unicode string can be an alternative for a
   syntactic form.

   If it's a RuleUpdate{u,term_name,newrule,oldtok} form, then the
   Unicode symbol u appears is a token of newrule, which maps to term_name,
   and oldtok is an ASCII token of the old rule (if any).


   If it's a OverloadUpdate{u,oldname,t} then u is to be put in as an
   additional overload from u to the term t, and oldname is the ASCII
   version of u (if any)
*)

val term_table = ref ([] : stored_data list)

fun getrule G term_name = let
  fun replace {term_name, elements, preferred, block_style, paren_style} s =
      {term_name = term_name,
       elements = map (fn (RE (TOK _)) => RE (TOK s) | x => x) elements,
       preferred = false,
       block_style = block_style,
       paren_style = paren_style}
  fun tok_of0 es =
      case es of
        [] => raise Fail "Unicode.getrule: should never happen"
      | RE (TOK s) :: _ => s
      | _ :: rest => tok_of0 rest
  fun tok_of {elements, ...} = tok_of0 elements

  fun search_rrlist f alt rrlist = let
    fun srch ({term_name = nm, preferred, elements, ...} : rule_record) =
        term_name = nm andalso preferred andalso
        length (List.filter (fn (RE (TOK _)) => true | _ => false) elements) = 1
  in
    case List.find srch rrlist of
      NONE => alt()
    | SOME r => f (r, replace r, tok_of r)
  end

  fun breplace {term_name,tok,preferred} s =
      {term_name = term_name, tok = s, preferred = false}
  fun search_bslist f alt blist = let
    fun srch {term_name = nm, preferred, tok} =
        term_name = nm andalso preferred
  in
    case List.find srch blist of
      NONE => alt()
    | SOME r => f (r, breplace r, #tok r)
  end

  fun con c (r,f,tok) = (c [r], (fn s => c [f s]), tok)
  fun addfix fopt (r,f,tok) = SOME ((fopt, r), (fn s => (fopt, f s)), tok)
  fun STD_infix' assoc (r,f,tok) = (INFIX (STD_infix([r],assoc)),
                                    (fn s => INFIX (STD_infix([f s], assoc))),
                                    tok)
  fun BinderString' (r, f, tok) =
      (PREFIX (BINDER [BinderString r]),
       (fn s => PREFIX (BINDER [BinderString (f s)])),
       tok)
  fun sing x = [x]
  fun get_rule_data rs =
      case rs of
        [] => NONE
      | (fixopt, grule) :: rest => let
        in
          case grule of
            PREFIX (BINDER blist) => let
              fun extract_bs (BinderString r) = SOME r
                | extract_bs _ = NONE
              val bslist = List.mapPartial extract_bs blist
            in
              search_bslist (addfix fixopt o BinderString')
                            (fn () => get_rule_data rest)
                            bslist
            end
          | PREFIX (STD_prefix rrlist) =>
            search_rrlist (addfix fixopt o con (PREFIX o STD_prefix))
                          (fn () => get_rule_data rest)
                          rrlist
          | SUFFIX TYPE_annotation => get_rule_data rest
          | SUFFIX (STD_suffix rrlist) =>
            search_rrlist (addfix fixopt o con (SUFFIX o STD_suffix))
                          (fn () => get_rule_data rest)
                          rrlist
          | INFIX (STD_infix (rrlist, assoc)) =>
            search_rrlist (addfix fixopt o STD_infix' assoc)
                          (fn () => get_rule_data rest)
                          rrlist
          | INFIX _ => get_rule_data rest
          | CLOSEFIX _ => get_rule_data rest
             (* only support single token overloads and a closefix form must
                involve two tokens at once *)
          | LISTRULE _ => get_rule_data rest (* likewise *)
        end
in
  get_rule_data (rules G)
end


fun constid t = let
  val {Name,Thy,Ty} = dest_thy_const t
in
  {Name = Name, Thy = Thy}
end

fun mktemp_resb s = "_" ^ s ^ "resb"

fun enable_one sd =
    case sd of
      RuleUpdate {u,term_name,newrule = r,oldtok} => let
        val g0 = term_grammar()
        val g' = add_grule g0 r
      in
        temp_set_grammars (type_grammar(), g');
        temp_prefer_form_with_tok {term_name = term_name, tok = u}
      end
    | OverloadUpdate{u,oldname,ts} => app (fn t => temp_overload_on(u,t)) ts

fun fupd_lambda f {type_intro,lambda,endbinding,restr_binders,res_quanop} =
    {type_intro = type_intro, lambda = f lambda, endbinding = endbinding,
     restr_binders = restr_binders, res_quanop = res_quanop}
fun fupd_restrs f {type_intro,lambda,endbinding,restr_binders,res_quanop} =
    {type_intro = type_intro, lambda = lambda, endbinding = endbinding,
     restr_binders = f restr_binders, res_quanop = res_quanop}

fun remove_uoverload s = let
  val G = term_grammar()
  val (G', _) = term_grammar.mfupdate_overload_info
                    (Overload.remove_overloaded_form s)
                    G
in
  temp_set_term_grammar G'
end


fun disable_one sd =
    case sd of
      RuleUpdate{u,term_name,newrule,oldtok} => let
      in
        temp_remove_termtok {tok = u, term_name = term_name};
        case oldtok of
          NONE => ()
        | SOME s =>
          temp_prefer_form_with_tok { tok = s, term_name = term_name}
      end
    | OverloadUpdate{u,oldname,ts} => let
        fun doit s t = temp_overload_on (s,t)
      in
        remove_uoverload u;
        case oldname of NONE => () | SOME s => app (doit s) ts
      end

fun new_action a =
    (if !master_unicode_switch then enable_one a else ();
     term_table := a :: !term_table)

fun temp_unicode_version {u,tmnm} = let
  val G = term_grammar()
  val oi = term_grammar.overload_info G
  val sd =
      case getrule G tmnm of
        NONE => let
        in
          case Overload.info_for_name oi tmnm of
            NONE => raise mk_HOL_ERR "Unicode" "unicode_version"
                                     ("No data for term with name "^tmnm)
          | SOME ops => OverloadUpdate{u = u, oldname = SOME tmnm,
                                       ts = #actual_ops ops}
        end
      | SOME(r,f,s) => RuleUpdate{u = u,term_name = tmnm, newrule = f u,
                                  oldtok = SOME s}
in
  new_action sd
end

exception foo
fun temp_uset_fixity s fxty = let
  val rule =
      case fxty of
        Prefix => (HOL_MESG "Fixities of Prefix do not affect the grammar";
                   raise foo)
      | Binder => (SOME std_binder_precedence,
                   PREFIX (BINDER [BinderString {tok = s, term_name = s,
                                                 preferred = true}]))
      | RF rf => let
        val {term_name,pp_elements,paren_style,block_style,...} =
            Parse.standard_spacing s fxty
        val irule = {term_name = term_name, elements = pp_elements,
                     preferred = true, block_style = block_style,
                     paren_style = paren_style}
        in
          case rf of
            Infix (ass, prec) => (SOME prec, INFIX (STD_infix([irule], ass)))
          | TruePrefix prec => (SOME prec, PREFIX (STD_prefix [irule]))
          | Suffix prec => (SOME prec, SUFFIX (STD_suffix [irule]))
          | Closefix => (NONE, CLOSEFIX [irule])
        end
in
  new_action (RuleUpdate{u = s, term_name = s, newrule = rule, oldtok = NONE})
end handle foo => ()

fun temp_uoverload_on (s, t) = let
  val G = term_grammar()
  val oi = term_grammar.overload_info G
  val oldname =
      case Overload.oi_strip_comb oi (#2 (strip_abs t)) of
        NONE => NONE
      | SOME (f,_) => SOME (unprefix GrammarSpecials.fakeconst_special
                                     (#1 (dest_var f)))
                       handle HOL_ERR _ => NONE
in
  new_action (OverloadUpdate { u = s, ts = [t], oldname = oldname })
end

datatype ThyUpdateInfo = UV of {u:string,tmnm:string}
                       | SF of string * fixity
                       | OVL of string * term

val updates = ref ([] : ThyUpdateInfo list)

fun unicode_version p = let
in
  updates := UV p :: !updates;
  temp_unicode_version p
end

fun uset_fixity s f = let
in
  updates := SF (s,f) :: !updates;
  temp_uset_fixity s f
end

fun uoverload_on st = let
in
  updates := OVL st :: !updates;
  temp_uoverload_on st
end

fun bare_lambda() =
    temp_set_term_grammar (fupdate_specials (fupd_lambda (fn _ => ["\\"]))
                                            (term_grammar()))

fun unicode_lambda () =
    temp_set_term_grammar (fupdate_specials (fupd_lambda (cons UChar.lambda))
                                            (term_grammar()))



fun enable_all () = List.app enable_one (List.rev (!term_table))
fun disable_all () = List.app disable_one (!term_table)

fun traceset n = if n = 0 then (master_unicode_switch := false;
                                set_trace "Greek tyvars" 0;
                                bare_lambda();
                                disable_all())
                 else (master_unicode_switch := true;
                       set_trace "Greek tyvars" 1;
                       unicode_lambda();
                       enable_all())
fun traceget () = if !master_unicode_switch then 1 else 0

val _ = register_ftrace ("Unicode", (traceget, traceset), 1)

val _ = traceset 1

fun print_update pps update =
    case update of
      UV {tmnm,u} => let
      in
        PP.add_string
            pps
            ("val _ = Unicode.temp_unicode_version {u = \""^String.toString u^
             "\", tmnm = \""^String.toString tmnm^"\"}\n")
      end
    | SF (s,f) => let
      in
        PP.add_string
            pps
            ("val _ = Unicode.temp_uset_fixity \"" ^ String.toString s ^
             "\" (" ^ Parse.fixityToString f ^ ")\n")
      end
    | OVL (s,t) => let
      in
        PP.add_string
            pps
            ("val _ = Unicode.temp_uoverload_on (\"" ^ String.toString s ^
             "\", " ^ minprint t ^")\n")
      end


fun setup (oldname, thyname) = let
in
  if not (null (!updates)) andalso thyname <> oldname then
    HOL_WARNING "Unicode" "setup"
                ("\"new_theory\" is throwing away Unicode updates for theory "^
                 oldname)
  else ();
  updates := [];
  adjoin_to_theory {
    sig_ps = NONE,
    struct_ps = SOME (fn pps => app (print_update pps) (!updates))
  }
end;

val _ = Theory.after_new_theory setup


end (* struct *)
