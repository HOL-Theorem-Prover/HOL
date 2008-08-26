structure Unicode :> Unicode =
struct

structure UChar = struct

(* Greek letters *)
val alpha = "\u00ce\u00b1"
val beta = "\u00ce\u00b2"
val gamma = "\u00ce\u00b3"
val delta = "\u00ce\u00b4"
val zeta = "\u00ce\u00b6"
val eta = "\u00ce\u00b7"
val theta = "\u00ce\u00b8"
val lambda = "\u00ce\u00bb"
val mu = "\u00ce\u00bc"
val nu = "\u00ce\u00bd"
val xi = "\u00ce\u00be"
val sigma = "\u00cf\u0083"
val tau = "\u00cf\u0084"
val phi = "\u00cf\u0086"
val psi = "\u00cf\u0088"
val omega = "\u00cf\u0089"

val Gamma = "\u00ce\u0093"
val Delta = "\u00ce\u0094"
val Theta = "\u00ce\u0098"
val Lambda = "\u00ce\u009b"
val Xi = "\u00ce\u009e"
val Sigma = "\u00ce\u00a3"
val Phi = "\u00ce\u00a6"
val Psi = "\u00ce\u00a8"
val Omega = "\u00ce\u00a9"

(* Boolean gadgets *)
val forall = "\u00e2\u0088\u0080";
val exists = "\u00e2\u0088\u0083";
val conj = "\u00e2\u0088\u00a7";
val disj = "\u00e2\u0088\u00a8";
(* val imp = "\u00e2\u0086\u0092";  single arrow *)
val imp = "\u00e2\u0087\u0092";
val neg = "\u00c2\u00ac"

(* not a constant, but might be useful *)
val neq = "\u00e2\u0089\u00a0"
val turnstile = "\u00e2\u008a\u00a2";

(* probably needs a proportional font to print well - would be good for
   implication if available *)
val longdoublerightarrow = "\u00e2\u009f\u00b9"

val setelementof = "\u00e2\u0088\u0088"

(* arithmetic *)
val leq = "\u00e2\u0089\u00a4"
val geq = "\u00e2\u0089\u00a5"
val nats = "\u00e2\u0084\u0095"

(* sets *)
val emptyset = "\u00e2\u0088\u0085"
val subset = "\u00e2\u008a\u0086"
val inter = "\u00e2\u0088\u00a9"
val union = "\u00e2\u0088\u00aa"

(* words *)
val lo = "<\u00e2\u0082\u008a"
val hi = ">\u00e2\u0082\u008a"
val ls = leq ^ "\u00e2\u0082\u008a"
val hs = geq ^ "\u00e2\u0082\u008a"
val or = "\u00e2\u0080\u0096"
val xor = "\u00e2\u008a\u0095"
val lsl = "\u00e2\u0089\u00aa"
val asr = "\u00e2\u0089\u00ab"
val lsr = "\u00e2\u008b\u0099"
val rol = "\u00e2\u0087\u0086"
val ror = "\u00e2\u0087\u0084"
end (* UChar struct *)



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

fun getprec s =
    case get_precedence (term_grammar()) s of
      NONE => if is_binder (term_grammar()) s then SOME Binder
              else NONE
    | SOME f => SOME (Parse.RF f)

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
  fun con c (r,f,tok) = (c [r], (fn s => c [f s]), tok)
  fun addfix fopt (r,f,tok) = SOME ((fopt, r), (fn s => (fopt, f s)), tok)
  fun STD_infix' assoc (r,f,tok) = (INFIX (STD_infix([r],assoc)), 
                                    (fn s => INFIX (STD_infix([f s], assoc))), 
                                    tok)
  fun get_rule_data rs = 
      case rs of 
        [] => NONE
      | (fixopt, grule) :: rest => let 
        in
          case grule of 
            PREFIX (BINDER blist) => 
            if mem (BinderString term_name) blist then 
              SOME ((fixopt, PREFIX (BINDER [BinderString term_name])), 
                    (fn s => (fixopt, PREFIX (BINDER [BinderString s]))), 
                    NONE)
            else get_rule_data rest
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
  fun do_binder () = let 
    val G = term_grammar()
    open Overload
    val oinfo = overload_info G 
    val restrictions = #restr_binders (specials G)
    val myrestrs = filter (fn (b,s) => b = BinderString (valOf non_u)) 
                          restrictions
    fun appthis (b,s) = let 
      val res_t = mk_thy_const 
                    (hd (#actual_ops (valOf (info_for_name oinfo s))))
    in
      temp_overload_on (mktemp_resb u, res_t);
      temp_associate_restriction(u, mktemp_resb u)
    end handle Option => ()
  in
    temp_overload_on (u,t);
    List.app appthis myrestrs
  end
in 
  case newrule of 
    NONE => temp_overload_on (u, t)
  | SOME r => let 
      val g0 = term_grammar()
      val g' = add_grule g0 r
    in 
      temp_set_grammars (type_grammar(), g');
      if rule_is_binder r then do_binder ()
      else temp_prefer_form_with_tok {term_name = valOf non_u, tok = u}
    end
end

fun fupd_lambda f {type_intro,lambda,endbinding,restr_binders,res_quanop} = 
    {type_intro = type_intro, lambda = f lambda, endbinding = endbinding,
     restr_binders = restr_binders, res_quanop = res_quanop}
fun fupd_restrs f {type_intro,lambda,endbinding,restr_binders,res_quanop} = 
    {type_intro = type_intro, lambda = lambda, endbinding = endbinding,
     restr_binders = f restr_binders, res_quanop = res_quanop}


fun disable_one (SD {t, u, non_u, newrule, oldtok}) = let 
  fun do_binder() = let 
    val nu = valOf non_u
    val G = term_grammar()
    val restrs = #restr_binders (specials G)
    val oinfo = overload_info G
    fun foldthis ((b,s),acc) = 
        (* a fold with side effects - a bit ghastly *)
        if b = BinderString u then (temp_clear_overloads_on s; acc)
        else if b = BinderString nu then 
          case Overload.info_for_name oinfo s of 
            NONE => (b,s)::acc
          | SOME {actual_ops,...} => let 
              val t = mk_thy_const (hd actual_ops)
            in
              (temp_overload_on (s, t); (b,s)::acc)
            end
        else ((b,s)::acc)
    val new_rbs = List.rev (List.foldl foldthis [] restrs)
  in
    temp_remove_termtok {tok = u, term_name = u}; 
    temp_remove_ovl_mapping u (constid t);
    temp_overload_on (valOf non_u, t);
    temp_set_term_grammar (fupdate_specials (fupd_restrs (fn _ => new_rbs))
                                            (term_grammar()))
  end
in
  case newrule of 
    NONE => (temp_remove_ovl_mapping u (constid t) ;
             case non_u of 
               NONE => ()
             | SOME nu => temp_overload_on (nu, t))
  | SOME r => let
    in
      if rule_is_binder r then do_binder()
      else (temp_remove_termtok {tok = u, term_name = valOf non_u};
            temp_prefer_form_with_tok { tok = valOf oldtok, 
                                        term_name = valOf non_u})
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
