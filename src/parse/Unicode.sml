structure Unicode :> Unicode =
struct

open HolKernel Parse Feedback

type term = Term.term

val master_unicode_switch = ref false

val term_table = ref ([] : { t : term, u : string, non_u : string option} list)

fun getprec s =
    case term_grammar.get_precedence (term_grammar()) s of
      NONE => if term_grammar.is_binder (term_grammar()) s then SOME Binder
              else NONE
    | SOME f => SOME (Parse.RF f)


fun constid t = let
  val {Name,Thy,Ty} = dest_thy_const t
in
  {Name = Name, Thy = Thy}
end

fun enable_one {t, u, non_u} = let 
  val fix = case non_u of NONE => NONE 
                        | SOME s => getprec s
in 
  temp_overload_on (u, t); 
  case fix of NONE => () | SOME f => temp_set_fixity u f
end

fun disable_one {t, u, non_u} = 
    (temp_remove_ovl_mapping u (constid t) ;
     case non_u of NONE => () | SOME s => temp_overload_on(s, t))
    (* leave the concrete syntax alone because it's too hard to figure out 
       what to do for the moment *)

fun temp_unicode_version (uni_s, t) = let
  val oinfo = term_grammar.overload_info (term_grammar())
  val current_nm = Overload.overloading_of_term oinfo t
  val data = {t = t, u = uni_s, non_u = current_nm}
in
  if !master_unicode_switch then enable_one data else ();
  term_table := data :: !term_table
end

val updates = ref ([] : (string * term) list)

fun unicode_version p = let
in
  updates := p :: !updates;
  temp_unicode_version p
end



fun enable_all () = List.app enable_one (List.rev (!term_table))
fun disable_all () = List.app disable_one (!term_table)

fun traceset n = if n = 0 then (master_unicode_switch := false;
                                disable_all())
                 else (master_unicode_switch := true;
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

(*


fun words_printing () = let
in
  add_rule (standard_spacing leq (getprec "<="));
  overload_on_by_nametype leq {Name = "word_le", Thy = "words"};

  add_rule (standard_spacing geq (getprec ">="));
  overload_on_by_nametype geq {Name = "word_ge", Thy = "words"};

  add_rule (standard_spacing lo (getprec "<+"));
  overload_on_by_nametype lo {Name = "word_lo", Thy = "words"};

  add_rule (standard_spacing hi (getprec ">+"));
  overload_on_by_nametype hi {Name = "word_hi", Thy = "words"};

  add_rule (standard_spacing ls (getprec "<=+"));
  overload_on_by_nametype ls {Name = "word_ls", Thy = "words"};

  add_rule (standard_spacing hs (getprec ">=+"));
  overload_on_by_nametype hs {Name = "word_hs", Thy = "words"};

  add_rule (standard_spacing or (getprec "!!"));
  overload_on_by_nametype or {Name = "word_or", Thy = "words"};

  add_rule (standard_spacing xor (getprec "??"));
  overload_on_by_nametype xor {Name = "word_xor", Thy = "words"};

  add_rule (standard_spacing lsl (getprec "<<"));
  overload_on_by_nametype lsl {Name = "word_lsl", Thy = "words"};

  add_rule (standard_spacing asr (getprec ">>"));
  overload_on_by_nametype asr {Name = "word_asr", Thy = "words"};

  add_rule (standard_spacing lsr (getprec ">>>"));
  overload_on_by_nametype lsr {Name = "word_lsr", Thy = "words"};

  add_rule (standard_spacing rol (getprec "#<<"));
  overload_on_by_nametype rol {Name = "word_rol", Thy = "words"};

  add_rule (standard_spacing ror (getprec "#>>"));
  overload_on_by_nametype ror {Name = "word_ror", Thy = "words"}
end



*)
end (* struct *)
