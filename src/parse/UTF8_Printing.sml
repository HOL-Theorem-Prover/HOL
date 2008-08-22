structure UTF8_Printing :> UTF8_Printing =
struct

open Parse

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


fun getprec s = 
    Parse.RF (valOf (term_grammar.get_precedence (term_grammar()) s))

fun bool_printing () = let 
in
  add_binder(forall, 0);
  overload_on(forall, ``bool$! : ('a -> bool) -> bool``);

  add_binder(exists, 0);
  overload_on(exists, ``bool$? : ('a -> bool) -> bool``);

  add_rule (standard_spacing conj (getprec "/\\"));
  overload_on(conj, ``bool$/\``);

  add_rule (standard_spacing disj (getprec "\\/"));
  overload_on(disj, ``bool$\/``);

  add_rule (standard_spacing imp (getprec "==>"));
  overload_on(imp, ``min$==>``);

  add_rule {term_name   = "~",
            fixity      = getprec "~",
            pp_elements = [TOK neg],
            paren_style = OnlyIfNecessary,
            block_style = (AroundEachPhrase, (PP.CONSISTENT, 0))};

  add_rule (standard_spacing setelementof (getprec "IN"));
  overload_on (setelementof, ``bool$IN : 'a -> ('a -> bool) -> bool``)
end



val leq = "\u00e2\u0089\u00a4"
val geq = "\u00e2\u0089\u00a5"
val nats = "\u00e2\u0084\u0095"

fun arith_printing () = let 
in
  add_rule (standard_spacing leq (getprec "<="));
  overload_on(leq, ``arithmetic$<=``);

  add_rule (standard_spacing leq (getprec ">="));
  overload_on(geq, ``arithmetic$>=``);
  type_abbrev(nats, ``:num``)
end

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


val emptyset = "\u00e2\u0088\u0085"
val subset = "\u00e2\u008a\u0086"
val inter = "\u00e2\u0088\u00a9"
val union = "\u00e2\u0088\u00aa"

fun set_printing0 () = let 
in
  overload_on (emptyset, ``pred_set$EMPTY``);

  add_rule (standard_spacing inter (getprec "INTER"));
  overload_on (inter, ``pred_set$INTER``);

  add_rule (standard_spacing union (getprec "UNION"));
  overload_on (union, ``pred_set$UNION``);

  add_rule (standard_spacing subset (getprec "SUBSET"));
  overload_on (subset, ``pred_set$SUBSET``) 
end

val set_printing = 
    Feedback.trace ("notify type variable guesses", 0)
                   set_printing0 

fun all_printing () = (bool_printing(); arith_printing(); set_printing())

end (* struct *)
