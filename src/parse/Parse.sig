signature Parse = sig
  type term = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm
  type associativity = HOLgrammars.associativity
  type pp_element = term_grammar.pp_element
  type PhraseBlockStyle = term_grammar.PhraseBlockStyle
  type ParenStyle = term_grammar.ParenStyle
  type block_info = term_grammar.block_info

  datatype fixity
     = RF of term_grammar.rule_fixity
     | Prefix
     | Binder

  (* Parsing Types *)
  val type_grammar : unit -> parse_type.grammar
  val Type         : hol_type frag list -> hol_type
  val ==           : hol_type frag list -> 'a -> hol_type


  (* the parsing algorithm for types admits the possibility that type
     suffixes might be of looser binding than infixes, but the
     following interface always puts suffixes into the grammar at the
     same precedence level (equivalent to 100).  Infix operators can
     have precedences that are more or less than this. *)

  (* The new_type call below can always be used, but if the type is
     actually a unary or binary operator, then the given call should be
     used.  If an operator is claimed to be binary when it isn't, attempts
     to parse strings of the form   ty1 op ty2 will fail when mk_type is
     called with a list that is of the wrong length.

     The converse is not so dangerous: i.e., just using new_type for
     a binary operator as this will just remove the possibility of using
     an infix form. *)
  val add_type : string -> unit
  val temp_add_type : string -> unit
  val add_infix_type : {Prec : int,
                        ParseName : string option,
                        Name : string,
                        Assoc : associativity} -> unit
  val temp_add_infix_type : {Prec : int,
                             ParseName : string option,
                             Name : string,
                             Assoc : associativity} -> unit
  (* Examples for add_infix_type:
     - add_infix_type {precedence = 10, infix_form = SOME "#",
                       opname = "prod", associativity = RIGHT};
     - add_infix_type {precedence = 5, infix_form = SOME "+",
                       opname = "sum", associativity = RIGHT};
  *)

  (* completely removes a type from the grammar *)
(*  val remove_type : string -> unit
  (* removes a particular infix, allowing infixes to be gotten rid of, if
     desired, without removing the possibility of writing the type in
     suffix form *)
  val remove_type_infix : string -> unit *)

  (* Parsing terms *)
    val absyn_to_term    : term_grammar.grammar -> Absyn.absyn -> term
    val absyn_to_preterm : Absyn.absyn -> Preterm.preterm
    val Absyn            : term frag list -> Absyn.absyn
    val Preterm          : term frag list -> Preterm.preterm
    val Term             : term frag list -> term
    val --               : term frag list -> 'a -> term
    val typedTerm        : term frag list -> hol_type -> term
    val parse_in_context : term list -> term frag list -> term
    val parse_from_grammars :
      (parse_type.grammar * term_grammar.grammar) ->
      ((hol_type frag list -> hol_type) * (term frag list -> term))
    val print_from_grammars :
      (parse_type.grammar * term_grammar.grammar) ->
      ((Portable.ppstream -> hol_type -> unit) *
       (Portable.ppstream -> term -> unit))

    val term_grammar : unit -> term_grammar.grammar

    (* the following functions modify the grammar, and do so in such a
       way that the exported theory will have the same grammar
    *)
    val add_const  : string -> unit
    val add_infix  : string * int * associativity -> unit
    val std_binder_precedence : int
    val add_binder : string * int -> unit
    val add_rule   : {term_name : string, fixity :fixity,
                      pp_elements: pp_element list, paren_style : ParenStyle,
                      block_style : PhraseBlockStyle * block_info} -> unit
    val add_listform : {separator : string, leftdelim : string,
                        rightdelim : string, cons : string,
                        nilstr : string} -> unit
    val add_numeral_form : (char * string option) -> unit
    val add_bare_numeral_form : (char * string option) -> unit
    val give_num_priority : char -> unit
    val remove_numeral_form : char -> unit
    val associate_restriction : (string * string) -> unit
    val prefer_form_with_tok : {term_name : string, tok : string} -> unit
    val clear_prefs_for_term : string -> unit
    val set_fixity : string * fixity -> unit

    val remove_rules_for_term : string -> unit
    val remove_termtok : {term_name : string, tok : string} -> unit

    (* overloading and records *)
    val overload_on : string * term -> unit
    val overload_on_by_nametype : string -> {Name: string, Thy: string} -> unit
    val clear_overloads_on : string -> unit
    val add_record_field : string * term -> unit
    val add_record_update : string * term -> unit
    val add_record_fupdate : string * term -> unit


    (* the following functions affect the grammar, but not so that the
       grammar exported to disk will be modified *)
    val temp_set_grammars : (parse_type.grammar * term_grammar.grammar) -> unit
    val temp_add_binder : (string * int) -> unit
    val temp_add_rule :
      {term_name : string, fixity : fixity,
       pp_elements: pp_element list, paren_style : ParenStyle,
       block_style : PhraseBlockStyle * block_info}  -> unit
    val temp_add_infix : (string * int * associativity) -> unit
    val temp_add_listform : {separator : string, leftdelim : string,
                             rightdelim : string, cons : string,
                             nilstr : string} -> unit
    val temp_add_numeral_form : (char * string option) -> unit
    val temp_add_bare_numeral_form : (char * string option) -> unit
    val temp_give_num_priority : char -> unit
    val temp_remove_numeral_form : char -> unit
    val temp_associate_restriction : (string * string) -> unit
    val temp_prefer_form_with_tok : {term_name : string, tok : string} -> unit
    val temp_clear_prefs_for_term : string -> unit
    val temp_set_fixity : string * fixity -> unit

    val temp_remove_rules_for_term : string -> unit
    val temp_remove_termtok : {term_name : string, tok : string} -> unit
    val temp_set_associativity : (int * associativity) -> unit

    val temp_overload_on : string * term -> unit
    val temp_overload_on_by_nametype :
      string -> {Name: string, Thy: string} -> unit
    val temp_clear_overloads_on : string -> unit
    val temp_add_record_field : string * term -> unit
    val temp_add_record_update : string * term -> unit
    val temp_add_record_fupdate : string * term -> unit

    val standard_spacing : string -> fixity
                           -> {term_name   : string, fixity:fixity,
                               pp_elements : pp_element list,
                               paren_style : ParenStyle,
                               block_style : PhraseBlockStyle * block_info}

  (* Pretty printing *)
  val pp_term : General.ppstream -> term -> unit
  val pp_type : General.ppstream -> hol_type -> unit
  val pp_thm : General.ppstream -> thm -> unit
  val pp_with_bquotes :
    (General.ppstream -> 'a -> unit) -> (General.ppstream -> 'a -> unit)
  val term_pp_with_delimiters :
    (General.ppstream -> term -> unit) -> General.ppstream -> term -> unit
  val type_pp_with_delimiters :
    (General.ppstream -> hol_type -> unit) ->
    General.ppstream -> hol_type -> unit
  val get_term_printer : unit -> (General.ppstream -> term -> unit)
  val set_term_printer : (General.ppstream -> term -> unit) ->
                               General.ppstream -> term -> unit

  val term_to_string : term -> string
  val type_to_string : hol_type -> string
  val thm_to_string : thm -> string

  val print_thm : thm -> unit
  val print_type : hol_type -> unit
  val print_term : term -> unit

  val export_theory_as_docfiles : string -> unit
  val export_theorems_as_docfiles : string -> (string * thm) list -> unit

  val update_grms   : ('a -> unit) -> 'a -> unit
  val mk_local_grms :
    (string * (parse_type.grammar * term_grammar.grammar)) list ->
    unit


  val hide : string -> unit
  val reveal : string -> unit
  val hidden : string -> bool
  val known_constants : unit -> string list
  val set_known_constants : string list -> unit

  (* Call this function to get a call to reveal to happen in the
     theory file generated by export_theory(); if this isn't called,
     things will fail to parse as constants in later theories.

     This function is called by new_definition and friends, so it shouldn't
     be necessary for users to call it in most circumstances. *)
  val remember_const : string -> unit

  val LEFT       : associativity
  val RIGHT      : associativity
  val NONASSOC   : associativity

  val Infixl     : int -> fixity
  val Infixr     : int -> fixity
  val Infix      : associativity * int -> fixity
  val TruePrefix : int -> fixity
  val Closefix   : fixity
  val Suffix     : int -> fixity
  val fixity     : string -> fixity

  (* more constructors/values that come across from term_grammar *)

  val TM               : pp_element
  val TOK              : string -> pp_element
  val BreakSpace       : int * int -> pp_element
  val HardSpace        : int -> pp_element
  val BeginFinalBlock  : block_info -> pp_element
  val EndInitialBlock  : block_info -> pp_element
  val PPBlock          : pp_element list * block_info -> pp_element

  val OnlyIfNecessary  : ParenStyle
  val ParoundName      : ParenStyle
  val ParoundPrec      : ParenStyle
  val Always           : ParenStyle

  val AroundEachPhrase : PhraseBlockStyle
  val AroundSamePrec   : PhraseBlockStyle
  val AroundSameName   : PhraseBlockStyle

  val min_grammars : parse_type.grammar * term_grammar.grammar
  val current_lgrms : unit -> parse_type.grammar * term_grammar.grammar


end
