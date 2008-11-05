structure Unicode :> Unicode =
struct

structure UChar = UnicodeChars

open HolKernel Parse Feedback

open term_grammar

type term = Term.term

fun temp_set_term_grammar g = temp_set_grammars(type_grammar(), g)

val master_unicode_switch = ref false

datatype stored_data =
         SD of { t : term, u : string, non_u : string option,
                 newrule : (int option * grammar_rule) option,
                 oldtok : string option}

(* This stored data record encodes a number of different options for
   the way in which a Unicode string can be an alternative for a
   syntactic form.

   Fields:
     u  - the Unicode string
     t  - Always recorded, as a term is given as an input to the user-level
          functions.

          Used if u is directly overloaded to a term (a constant)
            * this has to happen with binders
            * can happen with constants that don't have concrete
              syntax.  (For example, I might want to bind Unicode beta
              to "beta", the relation expressing beta reduction which
              is not an infix.)


     non_u - the printing form of the given constant, as per the
             overload map.  Will often just be the name of the
             constant.  Will be NONE, if the constant is hidden
             (combin$C for example).  Will be different if the
             constant prints via some other string (e.g.,
             integer$int_le prints as "<=")

     newrule - the concrete syntax rule, if any, that is to be added to
               the term_grammar.

     oldtok - the token associated with the concrete syntax that in turn
              linked to non_u.  Needed so that on turning Unicode off, we
              can "prefer" this form.
*)

val term_table = ref ([] : stored_data list)

fun rule_is_binder (fixopt, grule) =
  case grule of
    PREFIX (BINDER _) => true
  | _ => false

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
    | SOME r => f (r, replace r, SOME (tok_of r))
  end

  fun breplace {term_name,tok,preferred} s = 
      {term_name = term_name, tok = s, preferred = false}
  fun search_bslist f alt blist = let 
    fun srch {term_name = nm, preferred, tok} = 
        term_name = nm andalso preferred 
  in
    case List.find srch blist of 
      NONE => alt()
    | SOME r => f (r, breplace r, SOME (#tok r))
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

fun enable_one (SD {t, u, non_u, newrule, oldtok}) = let
in
  case newrule of
    NONE => temp_overload_on (u, t)
  | SOME r => let
      val g0 = term_grammar()
      val g' = add_grule g0 r
    in
      temp_set_grammars (type_grammar(), g');
      temp_prefer_form_with_tok {term_name = valOf non_u, tok = u}
    end
end

fun fupd_lambda f {type_intro,lambda,endbinding,restr_binders,res_quanop} =
    {type_intro = type_intro, lambda = f lambda, endbinding = endbinding,
     restr_binders = restr_binders, res_quanop = res_quanop}
fun fupd_restrs f {type_intro,lambda,endbinding,restr_binders,res_quanop} =
    {type_intro = type_intro, lambda = lambda, endbinding = endbinding,
     restr_binders = f restr_binders, res_quanop = res_quanop}


fun disable_one (SD {t, u, non_u, newrule, oldtok}) = let
in
  case newrule of
    NONE => (temp_remove_ovl_mapping u (constid t) ;
             case non_u of
               NONE => ()
             | SOME nu => temp_overload_on (nu, t))
  | SOME r => let
    in
      temp_remove_termtok {tok = u, term_name = valOf non_u};
      temp_prefer_form_with_tok { tok = valOf oldtok,
                                  term_name = valOf non_u}
    end
end

fun temp_unicode_version (uni_s, t) = let
  val G = term_grammar()
  val oinfo = overload_info G
  val current_nm = Overload.overloading_of_term oinfo t
  val data =
      case current_nm of
        NONE => {t = t, u = uni_s, non_u = NONE, newrule = NONE, oldtok = NONE}
      | SOME nm => let
        in
          case getrule G nm of
            NONE => {t = t, u = uni_s, non_u = current_nm, newrule = NONE,
                     oldtok = NONE}
          | SOME (r,f,s) => {t = t, u = uni_s, non_u = current_nm,
                             newrule = SOME (f uni_s), oldtok = s}
        end
in
  if !master_unicode_switch then enable_one (SD data) else ();
  term_table := SD data :: !term_table
end

val updates = ref ([] : (string * term) list)

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

fun print_update pps (uni_s, t) = let
  val {Thy,Name,...} = dest_thy_const t
in
  PP.add_string
      pps
      ("val _ = Unicode.temp_unicode_version (\""^String.toString uni_s^"\", \
       \Term.prim_mk_const {Thy = \""^String.toString Thy^"\",\
       \Name = \""^String.toString Name^"\"})\n")
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
