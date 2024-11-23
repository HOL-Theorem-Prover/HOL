signature Parse = sig

  type term = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm
  type associativity = HOLgrammars.associativity
  type pp_element = term_grammar.pp_element
  type PhraseBlockStyle = term_grammar.PhraseBlockStyle
  type ParenStyle = term_grammar.ParenStyle
  type block_info = term_grammar.block_info
  type 'a frag = 'a PP.frag
  type 'a pprinter = 'a -> HOLPP.pretty

  datatype fixity = datatype term_grammar_dtype.fixity

  type grammarDB_info = type_grammar.grammar * term_grammar.grammar
  val grammarDB : {thyname:string} -> grammarDB_info option
  val set_grammar_ancestry : string list -> unit

  (* Parsing Types *)

  val type_grammar : unit -> type_grammar.grammar
  val Type         : hol_type frag list -> hol_type
  val ==           : hol_type frag list -> 'a -> hol_type

  val add_type : string -> unit
  val add_qtype : {Thy:string,Name:string} -> unit
  val temp_add_type : string -> unit
  val temp_add_qtype : {Thy:string,Name:string} -> unit
  val add_infix_type : {Prec : int,
                        ParseName : string option,
                        Name : string,
                        Assoc : associativity} -> unit
  val temp_add_infix_type : {Prec : int,
                             ParseName : string option,
                             Name : string,
                             Assoc : associativity} -> unit

  val temp_thytype_abbrev : KernelSig.kernelname * hol_type * bool -> unit
  val thytype_abbrev : KernelSig.kernelname * hol_type * bool -> unit
  val temp_type_abbrev : string * hol_type -> unit
  val type_abbrev : string * hol_type -> unit
  val temp_disable_tyabbrev_printing : string -> unit
  val disable_tyabbrev_printing : string -> unit
  val remove_type_abbrev : string -> unit
  val temp_remove_type_abbrev : string -> unit
  val temp_type_abbrev_pp : string * hol_type -> unit
  val type_abbrev_pp : string * hol_type -> unit

  (* Parsing terms *)

  val post_process_term: (term -> term) ref
  val add_absyn_postprocessor : string -> unit
  val temp_add_absyn_postprocessor :
      (string * term_grammar.absyn_postprocessor) -> unit
  val temp_remove_absyn_postprocessor :
      string -> term_grammar.absyn_postprocessor option
  val temp_add_preterm_processor :
      string * int -> term_grammar.preterm_processor -> unit
  val temp_remove_preterm_processor :
      string * int -> term_grammar.preterm_processor option

  val absyn_to_term    : term_grammar.grammar -> Absyn.absyn -> term
  val absyn_to_preterm : Absyn.absyn -> Preterm.preterm Pretype.in_env
  val Absyn            : term frag list -> Absyn.absyn
  val Preterm          : term frag list -> Preterm.preterm
  val Term             : term frag list -> term
  val typedTerm        : term frag list -> hol_type -> term
  val ty_antiq         : hol_type -> term
  val parse_in_context : term list -> term frag list -> term
  val typed_parse_in_context : hol_type -> term list -> term frag list -> term
  val parse_from_grammars :
      (type_grammar.grammar * term_grammar.grammar) ->
      ((hol_type frag list -> hol_type) * (term frag list -> term))
  val print_from_grammars :
      (type_grammar.grammar * term_grammar.grammar) ->
      (hol_type pprinter * term pprinter)
  val print_term_by_grammar :
        (type_grammar.grammar * term_grammar.grammar) -> term -> unit
  val print_without_macros : term -> unit

  val term_grammar : unit -> term_grammar.grammar

  val print_term_grammar : unit -> unit

  (* the following functions modify the grammar, and do so in such a
     way that the exported theory will have the same grammar  *)

  val add_const  : string -> unit
  val add_infix  : string * int * associativity -> unit
  val std_binder_precedence : int
  val add_rule   : {term_name : string, fixity :fixity,
                    pp_elements: pp_element list, paren_style : ParenStyle,
                    block_style : PhraseBlockStyle * block_info} -> unit
  val add_listform : {separator : pp_element list, leftdelim : pp_element list,
                      rightdelim : pp_element list, cons : string,
                      nilstr : string, block_info : block_info} -> unit
  val add_numeral_form : (char * string option) -> unit
  val add_strliteral_form : {ldelim:string,inj:term} -> unit
  val remove_strliteral_form : {tmnm : string} -> unit
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
  val gen_remove_ovl_mapping : string -> term -> unit
  val add_record_field : string * term -> unit
  val add_record_fupdate : string * term -> unit

  (* information about overloads and abbreviations;
     call interactively for information printed to stdout *)
  val overload_info_for : string -> unit

  (* printing without overloads or abbreviations *)
  val pp_term_without_overloads_on : string list -> term pprinter
  val pp_term_without_overloads : (string * term) list -> term pprinter
  val pp_type_without_abbrevs : string list -> hol_type pprinter

  (* adding and removing user parsers and printers to the grammar *)

  val add_user_printer : (string * term) -> unit
  val remove_user_printer : string -> (term * term_grammar.userprinter) option
  val constant_string_printer : string -> term_grammar.userprinter

 (* the following functions affect the grammar, but not so that the
    grammar exported to disk will be modified *)

  val temp_set_grammars : (type_grammar.grammar * term_grammar.grammar) -> unit
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
  val temp_add_strliteral_form : {ldelim:string,inj:term} -> unit
  val temp_remove_strliteral_form : {tmnm : string} -> unit
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
  val temp_gen_remove_ovl_mapping : string -> term -> unit

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
  val mlower : (term_pp_types.printing_info,'a)smpp.t -> HOLPP.pretty
  val pp_term : term pprinter
  val pp_type : hol_type pprinter
  val pp_thm : thm pprinter
  val stdprinters : ((term -> string) * (hol_type -> string)) option

  val pp_type_without_colon   : hol_type pprinter
  val term_pp_with_delimiters : term pprinter -> term pprinter
  val type_pp_with_delimiters : hol_type pprinter -> hol_type pprinter
  val get_term_printer : unit -> term pprinter
  val set_term_printer : term pprinter -> term pprinter

  val rawterm_pp             : ('a -> 'b) -> 'a -> 'b
  val add_style_to_string    : PPBackEnd.pp_style list -> string -> string
  val print_with_style       : PPBackEnd.pp_style list -> string -> unit
  val term_to_string         : term -> string
  val type_to_string         : hol_type -> string
  val thm_to_string          : thm -> string

  val print_thm              : thm -> unit
  val print_type             : hol_type -> unit
  val print_term             : term -> unit


  val export_theorems_as_docfiles : string -> (string * thm) list -> unit

  val hide   : string -> ({Name : string, Thy : string} list *
                          {Name : string, Thy : string} list)
  val permahide : term -> unit
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
  val fixity     : string -> fixity option

  (* more constructors/values that come across from term_grammar *)

  val TM               : pp_element
  val TOK              : string -> pp_element
  val BreakSpace       : int * int -> pp_element
  val HardSpace        : int -> pp_element
  val BeginFinalBlock  : block_info -> pp_element
  val EndInitialBlock  : block_info -> pp_element
  val PPBlock          : pp_element list * block_info -> pp_element
  val ListForm         : {separator:pp_element list, cons : string,
                          nilstr : string, block_info : block_info} ->
                         pp_element

  val OnlyIfNecessary  : ParenStyle
  val ParoundName      : ParenStyle
  val ParoundPrec      : ParenStyle
  val Always           : ParenStyle
  val NotEvenIfRand    : ParenStyle
  val IfNotTop         : {realonly:bool} -> ParenStyle

  val AroundEachPhrase : PhraseBlockStyle
  val AroundSamePrec   : PhraseBlockStyle
  val AroundSameName   : PhraseBlockStyle
  val NoPhrasing       : PhraseBlockStyle

  val min_grammars : type_grammar.grammar * term_grammar.grammar
  val merge_grammars : string list ->
                       type_grammar.grammar * term_grammar.grammar
  val current_grammars : unit -> type_grammar.grammar * term_grammar.grammar

  structure Unicode : sig
    val unicode_version : {u:string,tmnm:string} -> unit
    val temp_unicode_version : {u:string,tmnm:string} -> unit

    structure UChar : UnicodeChars
  end


end
