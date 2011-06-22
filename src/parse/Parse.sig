signature Parse = sig

  type term = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm
  type associativity = HOLgrammars.associativity
  type pp_element = term_grammar.pp_element
  type PhraseBlockStyle = term_grammar.PhraseBlockStyle
  type ParenStyle = term_grammar.ParenStyle
  type block_info = term_grammar.block_info
  type 'a frag = 'a Portable.frag
  type ppstream = Portable.ppstream

  datatype fixity
     = RF of term_grammar.rule_fixity
     | Binder
  val fixityToString : fixity -> string

  (* Parsing Types *)

  val type_grammar : unit -> type_grammar.grammar
  val Type         : hol_type frag list -> hol_type
  val ==           : hol_type frag list -> 'a -> hol_type

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

  val temp_type_abbrev : string * hol_type -> unit
  val type_abbrev : string * hol_type -> unit
  val temp_disable_tyabbrev_printing : string -> unit
  val disable_tyabbrev_printing : string -> unit

  (* Parsing terms *)

  val post_process_term: (term -> term) ref
  val add_absyn_postprocessor : (string * (Absyn.absyn->Absyn.absyn)) -> unit
  val temp_add_absyn_postprocessor :
      (string * (Absyn.absyn->Absyn.absyn)) -> unit
  val absyn_to_term    : term_grammar.grammar -> Absyn.absyn -> term
  val absyn_to_preterm : Absyn.absyn -> Preterm.preterm
  val Absyn            : term frag list -> Absyn.absyn
  val Preterm          : term frag list -> Preterm.preterm
  val Term             : term frag list -> term
  val --               : term frag list -> 'a -> term
  val typedTerm        : term frag list -> hol_type -> term
  val ty_antiq         : hol_type -> term
  val parse_in_context : term list -> term frag list -> term
  val parse_preterm_in_context : term list -> Preterm.preterm -> term
  val grammar_parse_in_context :
      (type_grammar.grammar * term_grammar.grammar) ->
      term list -> term frag list -> term
  val parse_from_grammars :
      (type_grammar.grammar * term_grammar.grammar) ->
      ((hol_type frag list -> hol_type) * (term frag list -> term))
  val print_from_grammars :
      (type_grammar.grammar * term_grammar.grammar) ->
      ((Portable.ppstream -> hol_type -> unit) *
       (Portable.ppstream -> term -> unit))
  val print_term_by_grammar :
        (type_grammar.grammar * term_grammar.grammar) -> term -> unit

  val term_grammar : unit -> term_grammar.grammar

  (* the following functions modify the grammar, and do so in such a
     way that the exported theory will have the same grammar  *)

  val add_const  : string -> unit
  val add_infix  : string * int * associativity -> unit
  val std_binder_precedence : int
  val add_binder : string -> unit
  val add_rule   : {term_name : string, fixity :fixity,
                    pp_elements: pp_element list, paren_style : ParenStyle,
                    block_style : PhraseBlockStyle * block_info} -> unit
  val add_listform : {separator : pp_element list, leftdelim : pp_element list,
                      rightdelim : pp_element list, cons : string,
                      nilstr : string, block_info : block_info} -> unit
  val add_numeral_form : (char * string option) -> unit
  val add_bare_numeral_form : (char * string option) -> unit
  val give_num_priority : char -> unit
  val remove_numeral_form : char -> unit
  val associate_restriction : (string * string) -> unit
  val prefer_form_with_tok : {term_name : string, tok : string} -> unit
  val set_fixity : string -> fixity -> unit
  val set_mapped_fixity : {term_name : string, tok : string, fixity : fixity} ->
                          unit

  val remove_rules_for_term : string -> unit
  val remove_termtok : {term_name : string, tok : string} -> unit

  (* overloading and records *)

  val overload_on : string * term -> unit
  val inferior_overload_on : string * term -> unit
  val overload_on_by_nametype : string -> {Name: string, Thy: string} -> unit
  val send_to_back_overload : string -> {Name: string, Thy: string} -> unit
  val bring_to_front_overload : string -> {Name: string, Thy: string} -> unit
  val clear_overloads_on : string -> unit
  val remove_ovl_mapping : string -> {Name:string, Thy:string} -> unit
  val add_record_field : string * term -> unit
  val add_record_fupdate : string * term -> unit

  (* printing overloads and abbreviations *)

  val pp_overloads_on : string -> (ppstream -> unit) list * (ppstream -> unit) list
  val print_overloads_on : string -> unit
  val pp_abbrev : string -> ppstream -> unit
  val print_abbrev : string -> unit

  (* printing without overloads or abbreviations *)

  val pp_term_without_overloads_on : string list -> ppstream -> term -> unit
  val term_without_overloads_on_to_string : string list -> term -> string
  val term_without_overloads_on_to_backend_string : string list -> term -> string
  val print_term_without_overloads_on : string list -> term -> unit
  val print_backend_term_without_overloads_on : string list -> term -> unit
  val pp_term_without_overloads : (string * term) list -> ppstream -> term -> unit
  val term_without_overloads_to_string : (string * term) list -> term -> string
  val term_without_overloads_to_backend_string : (string * term) list -> term -> string
  val print_term_without_overloads : (string * term) list -> term -> unit
  val print_backend_term_without_overloads : (string * term) list -> term -> unit
  val pp_type_without_abbrevs : string list -> ppstream -> hol_type -> unit
  val type_without_abbrevs_to_string : string list -> hol_type -> string
  val type_without_abbrevs_to_backend_string : string list -> hol_type -> string
  val print_type_without_abbrevs : string list -> hol_type -> unit
  val print_backend_type_without_abbrevs : string list -> hol_type -> unit

  (* adding and removing user parsers and printers to the grammar *)

  val add_user_printer : (string * term * term_grammar.userprinter) -> unit
  val remove_user_printer : string -> (term * term_grammar.userprinter) option

 (* the following functions affect the grammar, but not so that the
    grammar exported to disk will be modified *)

  val temp_set_grammars : (type_grammar.grammar * term_grammar.grammar) -> unit
  val temp_add_binder : string -> unit
  val temp_add_rule :
    {term_name : string, fixity : fixity,
     pp_elements: pp_element list, paren_style : ParenStyle,
     block_style : PhraseBlockStyle * block_info}  -> unit
  val temp_add_infix : (string * int * associativity) -> unit
  val temp_add_listform : {separator : pp_element list,
                           leftdelim : pp_element list,
                           rightdelim : pp_element list, cons : string,
                           nilstr : string, block_info : block_info} -> unit
  val temp_add_numeral_form : (char * string option) -> unit
  val temp_add_bare_numeral_form : (char * string option) -> unit
  val temp_give_num_priority : char -> unit
  val temp_remove_numeral_form : char -> unit
  val temp_associate_restriction : (string * string) -> unit
  val temp_prefer_form_with_tok : {term_name : string, tok : string} -> unit
  val temp_set_fixity : string -> fixity -> unit
  val temp_set_mapped_fixity :
      {term_name : string, tok : string, fixity : fixity} -> unit

  val temp_remove_rules_for_term : string -> unit
  val temp_remove_termtok : {term_name : string, tok : string} -> unit
  val temp_set_associativity : (int * associativity) -> unit

  val temp_overload_on : string * term -> unit
  val temp_inferior_overload_on : string * term -> unit
  val temp_overload_on_by_nametype : string -> {Name:string,Thy:string} -> unit
  val temp_send_to_back_overload : string -> {Name:string,Thy:string} -> unit
  val temp_bring_to_front_overload : string -> {Name:string,Thy:string} -> unit
  val temp_clear_overloads_on : string -> unit
  val temp_remove_ovl_mapping : string -> {Name:string, Thy:string} -> unit

  val temp_add_record_field : string * term -> unit
  val temp_add_record_fupdate : string * term -> unit

  val temp_add_user_printer : (string * term * term_grammar.userprinter) ->
                              unit
  val temp_remove_user_printer : string ->
                                 (term * term_grammar.userprinter) option

  val try_grammar_extension : ('a -> 'b) -> 'a -> 'b


  (* Pretty printing *)
  val current_backend : PPBackEnd.t ref
  val interactive_ppbackend : unit -> PPBackEnd.t
  val pp_term : ppstream -> term -> unit
  val pp_type : ppstream -> hol_type -> unit
  val pp_thm : ppstream -> thm -> unit
  val pp_with_bquotes :
    (ppstream -> 'a -> unit) -> (ppstream -> 'a -> unit)
  val term_pp_with_delimiters :
    (ppstream -> term -> unit) -> ppstream -> term -> unit
  val respect_width_ref :
      int ref -> (ppstream -> 'a -> unit) ->
      (ppstream -> 'a -> unit)
  val type_pp_with_delimiters :
    (ppstream -> hol_type -> unit) ->
    ppstream -> hol_type -> unit
  val get_term_printer : unit -> (ppstream -> term -> unit)
  val set_term_printer : (ppstream -> term -> unit) ->
                               ppstream -> term -> unit

  val minprint               : term -> string
  val add_style_to_string    : PPBackEnd.pp_style list -> string -> string
  val print_with_style       : PPBackEnd.pp_style list -> string -> unit
  val term_to_string         : term -> string
  val term_to_backend_string : term -> string
  val type_to_string         : hol_type -> string
  val type_to_backend_string : hol_type -> string
  val thm_to_string          : thm -> string
  val thm_to_backend_string  : thm -> string

  val print_thm              : thm -> unit
  val print_backend_thm      : thm -> unit
  val print_type             : hol_type -> unit
  val print_backend_type     : hol_type -> unit
  val print_term             : term -> unit
  val print_backend_term     : term -> unit


  val export_theorems_as_docfiles : string -> (string * thm) list -> unit

  val update_grms   : ('a -> unit) -> 'a -> unit
  val pending_updates : unit -> (string * string * term option) list
  val mk_local_grms
    : (string * (type_grammar.grammar * term_grammar.grammar)) list -> unit


  val hide   : string -> ({Name : string, Thy : string} list *
                          {Name : string, Thy : string} list)
  val update_overload_maps :
    string -> ({Name : string, Thy : string} list *
               {Name : string, Thy : string} list) -> unit

  val reveal : string -> unit
  val hidden : string -> bool
  val known_constants     : unit -> string list
  val set_known_constants : string list -> unit
  val is_constname : string -> bool

  val LEFT       : associativity
  val RIGHT      : associativity
  val NONASSOC   : associativity

  val Infixl     : int -> fixity
  val Infixr     : int -> fixity
  val Infix      : associativity * int -> fixity
  val Prefix     : int -> fixity
  val Closefix   : fixity
  val Suffix     : int -> fixity
  val fixity     : string -> fixity option

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
  val NoPhrasing       : PhraseBlockStyle

  val min_grammars : type_grammar.grammar * term_grammar.grammar
  val current_lgrms : unit -> type_grammar.grammar * term_grammar.grammar
  val current_grammars : unit -> type_grammar.grammar * term_grammar.grammar

  structure Unicode : sig
    val unicode_version : {u:string,tmnm:string} -> unit
    val uoverload_on : string * term -> unit
    val uset_fixity : string -> fixity -> unit

    val temp_unicode_version : {u:string,tmnm:string} -> unit
    val temp_uoverload_on : string * term -> unit
    val temp_uset_fixity : string -> fixity -> unit

    structure UChar : UnicodeChars
  end


end
