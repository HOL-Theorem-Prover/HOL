structure UTF8_Printing :> UTF8_Printing =
struct

open Parse

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

val lambda = "\u00ce\u00bb"

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


val emptyset = "\u00e2\u0088\u0085"
val inter = "\u00e2\u0088\u00a9"
val union = "\u00e2\u0088\u00aa"

fun set_printing0 () = let 
in
  overload_on (emptyset, ``pred_set$EMPTY``);

  add_rule (standard_spacing inter (getprec "INTER"));
  overload_on (inter, ``pred_set$INTER``);

  add_rule (standard_spacing union (getprec "UNION"));
  overload_on (union, ``pred_set$UNION``)
end

val set_printing = 
    Feedback.trace ("notify type variable guesses", 0)
                   set_printing0 

fun all_printing () = (bool_printing(); arith_printing(); set_printing())

end (* struct *)
