signature quantHeuristicsLibSimple =
sig
  include Abbrev

  (************************************)
  (* Main functionality               *)
  (************************************)

  (* SIMPLE_QUANT_INSTANTIATE_CONV implements functionality for
     finding GAP guesses fast. Moreover, the found instantiations may
     not contain free variables. As such, the functionality is similar
     to Unwind. It allows more syntax than Unwind and can be
     extended. It is much faster than the general quantifier
     instantiations heuristics, but also far less powerful. *)

  val SIMPLE_QUANT_INSTANTIATE_CONV   : conv
  val SIMPLE_QUANT_INST_ss            : simpLib.ssfrag
  val SIMPLE_QUANT_INSTANTIATE_TAC    : tactic

  val SIMPLE_EXISTS_INSTANTIATE_CONV  : conv
  val SIMPLE_FORALL_INSTANTIATE_CONV  : conv
  val SIMPLE_UEXISTS_INSTANTIATE_CONV : conv
  val SIMPLE_SOME_INSTANTIATE_CONV    : conv
  val SIMPLE_SELECT_INSTANTIATE_CONV  : conv



  (************************************)
  (* Extensions                       *)
  (************************************)

  (* A simple_guess_seaech_fun is a function that searches a guess. Given a

     - avoid : a set of variables to avoid in the instantiation
     - ty    : search a guess for either universal or existential quantification
     - v     : variable to search an instance for
     - tm    : a term to search an instantiation in

     it (if it succeeds) results in a theorem of the form

       |- SIMPLE_GUESS_EXISTS v i tm

     or

       |- SIMPLE_GUESS_FORALL v i tm

     depending on the value of ty. Moreover i does not contain any variable from avoid.

     Having an additional callback argument to search guesses for subterms is also useful.
     combine_sgsfwcs then allows combining a list of such search functions with callback
     into a single search function.
  *)

  datatype simple_guess_type = sgty_exists | sgty_forall
  type simple_guess_search_fun = term HOLset.set -> simple_guess_type -> term -> term -> thm
  type simple_guess_search_fun_with_callback = simple_guess_search_fun -> simple_guess_search_fun

  val combine_sgsfwcs : simple_guess_search_fun_with_callback list -> simple_guess_search_fun

  (* search functions for common operations *)
  val sgsfwc_eq     : simple_guess_search_fun_with_callback (* v = _ / _ = v *)
  val sgsfwc_eq_var : simple_guess_search_fun_with_callback (* v *)
  val sgsfwc_neg    : simple_guess_search_fun_with_callback (* ~ _ *)
  val sgsfwc_and    : simple_guess_search_fun_with_callback (* _ /\ _ *)
  val sgsfwc_or     : simple_guess_search_fun_with_callback (* _ \/ _ *)
  val sgsfwc_imp    : simple_guess_search_fun_with_callback (* _ ==> _ *)
  val sgsfwc_forall : simple_guess_search_fun_with_callback (* !z. _ *)
  val sgsfwc_exists : simple_guess_search_fun_with_callback (* ?z. _ *)

  (* to find guesses for equations, a function can also be applied to
     both sides of the equation first. For example, to find guesses
     for "x" in "(x, y) = f z" it might be useful to apply "FST" to
     both sides. This is done by "sgsfwc_eq_fun". It gets a list of
     functions to try. Entries of this list are triples containing the
     function to apply, a check when to apply and a theorem about how
     to rewrite in case the check succeeds.  For FST the entries would
     look like: (``FST``, pairSyntax.is_pair, pairTheory.FST). *)
  val sgsfwc_eq_fun : (term * (term -> bool) * thm) list -> (* ?z. _ = _ *)
                      simple_guess_search_fun_with_callback

  (* List of eq_funs for pairs, lists, options and sum types. *)
  val default_eq_funs : (term * (term -> bool) * thm) list

  val default_sgsfwcs : simple_guess_search_fun_with_callback list

  (* Generalised conversions that allow specifying which search functions to use *)
  val SIMPLE_EXISTS_INSTANTIATE_CONV_GEN  : simple_guess_search_fun_with_callback list -> conv
  val SIMPLE_FORALL_INSTANTIATE_CONV_GEN  : simple_guess_search_fun_with_callback list -> conv
  val SIMPLE_UEXISTS_INSTANTIATE_CONV_GEN : simple_guess_search_fun_with_callback list -> conv
  val SIMPLE_SOME_INSTANTIATE_CONV_GEN    : simple_guess_search_fun_with_callback list -> conv
  val SIMPLE_SELECT_INSTANTIATE_CONV_GEN  : simple_guess_search_fun_with_callback list -> conv

  val SIMPLE_QUANT_INSTANTIATE_CONV_GEN   : simple_guess_search_fun_with_callback list -> conv
  val SIMPLE_QUANT_INST_GEN_ss            : simple_guess_search_fun_with_callback list -> simpLib.ssfrag

end
