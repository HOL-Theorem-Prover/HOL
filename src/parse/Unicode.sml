structure Unicode :> Unicode =
struct

structure UChar = UnicodeChars

open HolKernel Parse Feedback

open term_grammar

type term = Term.term

fun temp_set_term_grammar g = temp_set_grammars(type_grammar(), g)

val master_unicode_switch = ref false

datatype stored_data =
         RuleUpdate of { u : string, term_name : string,
                         newrule : (int option * grammar_rule),
                         oldtok : string }
       | OverloadUpdate of { u : string, oldname : string, ts : term list }

(* This stored data record encodes a number of different options for
   the way in which a Unicode string can be an alternative for a
   syntactic form.

   If it's a RuleUpdate{u,term_name,newrule,oldtok} form, then the
   Unicode symbol u appears is a token of newrule, which maps to term_name,
   and oldtok is an ASCII token of the old rule.


   If it's a OverloadUpdate{u,oldname,t} then u is to be put in as an
   additional overload from u to the term t, and oldname is the ASCII
   version of u.
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


fun disable_one sd =
    case sd of
      RuleUpdate{u,term_name,newrule,oldtok} => let
      in
        temp_remove_termtok {tok = u, term_name = term_name};
        temp_prefer_form_with_tok { tok = oldtok, term_name = term_name}
      end
    | OverloadUpdate{u,oldname,ts} => let
        fun doit t = (temp_remove_ovl_mapping u (constid t) ;
                      temp_overload_on (oldname, t))
      in
        app doit ts
      end

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
          | SOME ops => OverloadUpdate{u = u, oldname = tmnm,
                                       ts = #actual_ops ops}
        end
      | SOME(r,f,s) => RuleUpdate{u = u,term_name = tmnm, newrule = f u,
                                  oldtok = s}
in
  if !master_unicode_switch then enable_one sd else ();
  term_table := sd :: !term_table
end

val updates = ref ([] : {u:string,tmnm:string} list)

fun unicode_version p = let
in
  updates := p :: !updates;
  temp_unicode_version p
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
                                bare_lambda();
                                disable_all())
                 else (master_unicode_switch := true;
                       unicode_lambda();
                       enable_all())
fun traceget () = if !master_unicode_switch then 1 else 0

val _ = register_ftrace ("Unicode", (traceget, traceset), 1)

fun print_update pps {u,tmnm} =
    PP.add_string
        pps
      ("val _ = Unicode.temp_unicode_version {u = \""^String.toString u^
       "\", tmnm = \""^String.toString tmnm^"\"}\n")


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
