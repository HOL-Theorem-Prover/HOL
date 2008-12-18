signature quantHeuristicsLib =
sig
  include Abbrev


(*some general conversions, that might be useful
  in other context as well *)
  val TOP_ONCE_REWRITE_CONV        : thm list -> conv;
  val NEG_NEG_INTRO_CONV           : conv;
  val NEG_NEG_ELIM_CONV            : conv;
  val NOT_FORALL_LIST_CONV         : conv;
  val NOT_EXISTS_LIST_CONV         : conv;
  val STRIP_NUM_QUANT_CONV         : int -> conv -> conv;
  val BOUNDED_NOT_EXISTS_LIST_CONV : int -> conv;
  val BOUNDED_REPEATC              : int -> conv -> conv;

  val EXISTS_NOT_LIST_CONV         : conv;
  val FORALL_NOT_LIST_CONV         : conv;
  val QUANT_SIMP_CONV              : conv;

  val NOT_OR_CONV                  : conv;
  val NOT_AND_CONV                 : conv;
  val AND_NOT_CONV                 : conv;
  val OR_NOT_CONV                  : conv;



(*Guesses*)

  datatype guess =
    (*A guess with no particular reason at all, no justification. This
      is for example used by EXISTS_TAC.

      guess_general (i, [fv1,...,fvn])

      can be used to proof

      ?fv1 ... fvn. P i ==> ?v. P v   and
      !v. P v ==> !fv1 ... fvn. P i

      or if one want's to use equations 

      ?v. P v = (?fv1 ... fvn. P i) \/ 
                   ?v. (!fv1 ... fvn. ~(i = v)) /\ (P v)  and

      !v. P v = (!fv1 ... fvn. P i) /\
		   (!v. (?fv1 ... fvn. ~(i = v)) ==> P v)


      These two possibilies are always available and
      choosen if the other guesses don't provide a theorem.
    *)
    guess_general of term * term list 

    (* Guess_untrusted, is an untrusted guess recording guesses for
       subterms. It is mainly used to
       give some feedback to the user, not for instantations.
       It is introduced if a guess of subterms can not be ported to
       the whole term. *)
  | guess_untrusted of term * guess
    

    (*i makes P i false

      This can be used to proof
      !v. P v = F

      If a theorem is provided it has to be of the form 
      !fv1 ... fvn. ~(P i)
    *)
  | guess_false of term * term list * thm option 

    (*i makes P i true

      This can be used to proof
      ?v. P v = T

      The theorem has to be of the form 
      !fv1 ... fvn. P i
    *)
  | guess_true of term * term list * thm option 

    (*if i does satisfy P then all other i' as well

      This can be used to proof
      !v. P v = !fv1 ... fvn. P i


      The theorem has to be of the form 
      (!fv1 ... fvn. P i) ==> !v. P v
    *)
  | guess_only_not_possible of term * term list * thm option 

    (*if i does not satisfy P then all other i' don't as well

      This can be used to proof
      ?v. P v = ?fv1 ... fvn. P i

      The theorem has to be of the form 
      (!fv1 ... fvn. ~(P i)) ==> !v. ~(P v)
    *)
  | guess_only_possible of term * term list * thm option

    (*all instantiations except i do not satisfy P 

      This can be used to proof
      ?v. P v = ?fv1 ... fvn. P i

      The theorem has to be of the form 
      !v. (!fv1 ... fvn. ~(v = i)) ==> ~P v
    *)
  | guess_others_not_possible of term * term list * thm option 

    (*all instantiations except i do not satisfy P 

      This can be used to proof
      !v. P v = !fv1 ... fvn. P i

      The theorem has to be of the form 
      !v. (!fv1 ... fvn. ~(v = i)) ==> P v
    *)
  | guess_others_satisfied of term * term list * thm option;


  val is_guess_general             : guess -> bool
  val is_guess_untrusted           : guess -> bool
  val is_guess_true                : bool -> guess -> bool
  val is_guess_false               : bool -> guess -> bool
  val is_guess_only_possible       : bool -> guess -> bool
  val is_guess_only_not_possible   : bool -> guess -> bool
  val is_guess_others_not_possible : bool -> guess -> bool
  val is_guess_others_satisfied    : bool -> guess -> bool

  val split_guess_list             :  guess list ->
      guess list * guess list * guess list * guess list * 
      guess list * guess list * guess list * guess list

  val guess_set_thm_opt            : thm option -> guess -> guess
  val guess_remove_thm             : guess -> guess
  val make_guess_thm_term          : term -> term -> guess -> term option
  val make_guess_thm_opt           : term -> term -> guess -> conv -> thm option
  val make_set_guess_thm_opt       : term -> term -> guess -> conv -> guess

  (*Warning: this one is for debugging only. It uses mk_thm to
    create the thm added to the guess*)
  val make_guess_thm_opt___dummy : term -> term -> guess -> thm option
  val make_set_guess_thm_opt___dummy : term -> term -> guess -> guess


  val guess_flatten : guess -> guess
  val guess_extract : guess -> term * term list * thm option
  val guess___do_not_trust : term -> guess -> guess
  val guess_to_string : bool -> guess -> string

  val check_guess        : term -> term -> guess -> bool
  val correct_guess      : term -> term -> guess -> guess option
  val correct_guess_list :
     term -> term -> guess list -> guess list
  val normalise_guess_list :
     bool -> term -> term -> guess list -> guess list
  val normalise_correct_guess_list :
     term -> term -> guess list -> guess list
  val filter_trusted_guess_list : guess list -> guess list

  val term_variant : term list -> term list -> term -> term * term list


(*Some types*)
  type quant_heuristic = term list -> term -> term -> guess list;
  type quant_heuristic_combine_argument = 
     (thm list * thm list * thm list * conv list * (quant_heuristic -> quant_heuristic) list);



(*Heuristics that might be useful to write own ones*)
  val QUANT_INSTANTIATE_HEURISTIC___REWRITE :
  quant_heuristic -> term list -> term -> thm -> guess list
  val QUANT_INSTANTIATE_HEURISTIC___CONV :
  conv -> quant_heuristic -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___EQUATION_distinct : thm list -> quant_heuristic -> quant_heuristic;
  val QUANT_INSTANTIATE_HEURISTIC___EQUATION_cases : thm -> quant_heuristic -> quant_heuristic;

  val QUANT_INSTANTIATE_HEURISTIC___max_rec_depth : int ref

  val QUANT_INSTANTIATE_HEURISTIC___COMBINE :
  ((quant_heuristic -> quant_heuristic) list) -> quant_heuristic;


(*The most important functions *)

  val PURE_QUANT_INSTANTIATE_CONV : conv;
  val QUANT_INSTANTIATE_CONV      : conv;

  val EXT_PURE_QUANT_INSTANTIATE_CONV : 
      bool -> bool -> quant_heuristic_combine_argument -> conv;
  val EXT_QUANT_INSTANTIATE_CONV : 
      bool -> bool -> quant_heuristic_combine_argument -> conv;


(*functions to add stuff to QUANT_INSTANTIATE_CONV*)


  val quant_heuristic___get_combine_argument :
     unit -> quant_heuristic_combine_argument
  val quant_heuristic___clear_combine_argument : 
     unit -> unit
  val quant_heuristic___add_combine_argument :
     quant_heuristic_combine_argument -> unit;

  val quant_heuristic___add_distinct_thms : thm list -> unit;
  val quant_heuristic___add_cases_thms    : thm list -> unit;
  val quant_heuristic___add_rewrite_thms  : thm list -> unit;
  val quant_heuristic___add_rewrite_convs : conv list -> unit;
  val quant_heuristic___add_heuristic     : (quant_heuristic -> quant_heuristic) -> unit;



  val empty_quant_heuristic_combine_argument : quant_heuristic_combine_argument;

  val COMBINE___QUANT_HEURISTIC_COMBINE_ARGUMENT :
     quant_heuristic_combine_argument -> quant_heuristic_combine_argument ->
     quant_heuristic_combine_argument;

  val COMBINE___QUANT_HEURISTIC_COMBINE_ARGUMENTS :
     quant_heuristic_combine_argument list -> quant_heuristic_combine_argument;





end
