local
  open HolKernel HOLgrammars
in
  datatype fixity = RF of term_grammar.rule_fixity | Prefix | Binder
  (* these are convenience values *)
  val Infixl : int -> fixity
  val Infixr : int -> fixity
  val Infix : (associativity * int) -> fixity
  val TruePrefix : int -> fixity
  val Closefix : fixity
  val Suffix : int -> fixity

  val fixity : string -> fixity

  (* more constructors/values that come across from term_grammar *)
  val TM : term_grammar.pp_element
  val TOK : string -> term_grammar.pp_element
  val BreakSpace : (int * int) -> term_grammar.pp_element
  val HardSpace : int -> term_grammar.pp_element
  val BeginFinalBlock : term_grammar.block_info -> term_grammar.pp_element
  val EndInitialBlock : term_grammar.block_info -> term_grammar.pp_element
  val PPBlock :
    (term_grammar.pp_element list * term_grammar.block_info) ->
    term_grammar.pp_element

  val OnlyIfNecessary : term_grammar.ParenStyle
  val ParoundName : term_grammar.ParenStyle

  val AroundEachPhrase : term_grammar.PhraseBlockStyle
  val AroundSamePrec : term_grammar.PhraseBlockStyle
  val AroundSameName : term_grammar.PhraseBlockStyle



  val fromTGfixity : term_grammar.rule_fixity -> fixity
  val LEFT : associativity
  val RIGHT : associativity
  val NONASSOC : associativity

  (* Parsing Types *)
  val Type : hol_type frag list -> hol_type
  val == : hol_type frag list -> 'a -> hol_type

  val type_grammar : unit -> parse_type.grammar

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
  local
    open term_grammar
  in
    val parse_preTerm : term frag list -> term parse_term.preterm
    val preTerm : term frag list -> Preterm.preterm
    val Term : term frag list -> term
    val -- : term frag list -> 'a -> term
    val term_grammar : unit -> grammar

    (* the following functions modify the grammar, and do so in such a
       way that the exported theory will have the same grammar *)
    val add_infix : string * int * associativity -> unit
    val add_rule : {term_name : string, fixity : fixity,
                    pp_elements: pp_element list, paren_style : ParenStyle,
                    block_style : PhraseBlockStyle * block_info} -> unit
    val add_binder : (string * int) -> unit
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
    val set_fixity : string -> fixity -> unit

    val remove_term : string -> unit
    val remove_termtok : {term_name : string, tok : string} -> unit
    (* overloading *)
    val allow_for_overloading_on : string * Type.hol_type -> unit
    val overload_on : string * term -> unit
    val overload_on_by_nametype : string * string * Type.hol_type -> unit
    val clear_overloads_on : string -> unit

    val temp_allow_for_overloading_on : string * Type.hol_type -> unit
    val temp_overload_on : string * term -> unit
    val temp_overload_on_by_nametype : string * string * Type.hol_type -> unit
    val temp_clear_overloads_on : string -> unit

    (* the following functions affect the grammar, but not so that the
       grammar exported to disk will be modified *)
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
    val temp_set_fixity : string -> fixity -> unit

    val temp_remove_term : string -> unit
    val temp_remove_termtok : {term_name : string, tok : string} -> unit
    val temp_set_associativity : (int * associativity) -> unit
  end

  (* Pretty printing *)
  val pp_term : General.ppstream -> term -> unit
  val pp_type : General.ppstream -> hol_type -> unit
  val pp_thm : General.ppstream -> thm -> unit
  val pp_with_bquotes :
    (General.ppstream -> 'a -> unit) -> (General.ppstream -> 'a -> unit)

  val term_to_string : term -> string
  val type_to_string : hol_type -> string
  val thm_to_string : thm -> string

  val print_thm : thm -> unit
  val print_type : hol_type -> unit
  val print_term : term -> unit

  (* definitional principles that have an impact on parsing *)
  val new_infixl_definition : (string * term * int) -> thm
  val new_infixr_definition : (string * term * int) -> thm
  val new_binder_definition : (string * term) -> thm
  val new_gen_definition : (string * term * fixity) -> thm
  val new_infix : {Name : string, Ty : hol_type, Prec : int} -> unit
  val new_binder : {Name : string, Ty : hol_type} -> unit
  val new_type : {Name : string, Arity : int} -> unit
  val new_type_definition :
    {name : string, pred : term, inhab_thm : thm} -> thm
  val new_infix_type : {Name : string, Arity : int, ParseName : string option,
                        Assoc : associativity, Prec : int} -> unit

  val new_specification :
    {name : string, sat_thm : thm,
     consts : {fixity : fixity, const_name : string} list} -> thm

  (* Theory manipulation functions that also have an impact *)
  val new_theory : string -> unit
  val export_theory : unit -> unit
  val export_theory_as_docfiles : string -> unit
  val export_theorems_as_docfiles : string -> (string * thm) list -> unit
  val print_theory : unit -> unit

  (* stuff inserted rather after the fact that used to be in old Parse,
     and is still needed *)
  val typedTerm : term frag list -> hol_type -> term
  val hide : string -> unit
  val reveal : string -> unit
  val hidden : string -> bool


end
