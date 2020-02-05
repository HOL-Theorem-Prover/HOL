signature term_grammar =
sig

  type block_info = term_grammar_dtype.block_info
  type overload_info = Overload.overload_info
  type associativity = term_grammar_dtype.associativity
  type grule = term_grammar_dtype.grule

  datatype rule_element = datatype term_grammar_dtype.rule_element
  val RE_compare : rule_element * rule_element -> order

  datatype pp_element = datatype term_grammar_dtype.pp_element
  datatype PhraseBlockStyle = datatype term_grammar_dtype.PhraseBlockStyle
  datatype ParenStyle = datatype term_grammar_dtype.ParenStyle

  val rule_elements  : pp_element list -> rule_element list
  val pp_elements_ok : pp_element list -> bool
  val first_rtok : rule_element list -> string
  val first_tok : pp_element list -> string

  val reltoString    : rule_element -> string

  datatype binder = datatype term_grammar_dtype.binder
  datatype prefix_rule = datatype term_grammar_dtype.prefix_rule
  datatype suffix_rule = datatype term_grammar_dtype.suffix_rule
  datatype infix_rule = datatype term_grammar_dtype.infix_rule
  datatype grammar_rule = datatype term_grammar_dtype.grammar_rule
  datatype fixity = datatype term_grammar_dtype.fixity
  datatype user_delta = datatype term_grammar_dtype.user_delta
  type listspec = term_grammar_dtype.listspec
  type rule_record = term_grammar_dtype.rule_record

  type grammar

  val grule_toks : grule -> string list
  val grule_name : grule -> string

  val stdhol         : grammar
  val min_grammar    : grammar

  val binder_grule   : {term_name : string, tok : string} -> grule
  val standard_mapped_spacing :
      {term_name:string,tok:string,fixity:fixity} -> grule
  val standard_spacing : string -> fixity -> grule

  val merge_grammars : grammar * grammar -> grammar
  val fupdate_overload_info :
    (overload_info -> overload_info) -> grammar -> grammar
  val mfupdate_overload_info :
    (overload_info -> overload_info * 'a) -> grammar -> grammar * 'a


  (* User code additions *)
  (* Users can add special-purpose printers and parsers to grammars *)
  type term = Term.term
  type userprinter =
       (type_grammar.grammar * grammar,grammar) term_pp_types.userprinter
  val add_user_printer :
    (string * term * userprinter) -> grammar ->
    grammar
  val remove_user_printer :
    string -> grammar -> (grammar * (term * userprinter) option)
  val user_printers :
    grammar -> (term * string * userprinter)FCNet.t

  type absyn_postprocessor = grammar -> Absyn.absyn -> Absyn.absyn
  type AbPTME = Absyn.absyn -> Parse_supportENV.preterm_in_env
  type preterm_processor = grammar -> AbPTME -> AbPTME

  structure userSyntaxFns :
    sig
      type 'a getter = string -> 'a
      type 'a setter = {name : string, code : 'a} -> unit
      val register_userPP : userprinter setter
      val get_userPP : userprinter getter
      val get_absynPostProcessor : absyn_postprocessor getter
      val register_absynPostProcessor : absyn_postprocessor setter
    end

  val absyn_postprocessors :
      grammar -> (string * absyn_postprocessor) list
  val new_absyn_postprocessor :
      string * absyn_postprocessor -> grammar -> grammar
  val remove_absyn_postprocessor :
      string -> grammar -> (grammar * absyn_postprocessor option)

  val preterm_processor :
      grammar -> string * int -> preterm_processor option
  val new_preterm_processor :
      string * int -> preterm_processor -> grammar -> grammar
  val remove_preterm_processor :
      string * int -> grammar -> grammar * preterm_processor option


  type special_info = {type_intro    : string,
                       lambda        : string list,
                       endbinding    : string,
                       restr_binders : (string option * string) list,
                       res_quanop    : string}
  val fupd_lambda    : (string list -> string list) -> special_info ->
                       special_info

  type ruleset
  val rules          : grammar -> (int option * grammar_rule) list
  val ruleset        : grammar -> ruleset
  val grammar_rules  : grammar -> grammar_rule list
  val specials       : grammar -> special_info
  val fupdate_specials : (special_info -> special_info) -> grammar -> grammar
  val numeral_info   : grammar -> (char * string option) list
  val overload_info  : grammar -> overload_info
  val grammar_name   : grammar -> term -> string option

  (*------------------------------------------------------------------------
   * known constants are those strings that the parsing process will
   * attempt to turn into constants.  Known constants are those strings
   * that are in the domain of the overloading map (this map being from
   * strings to non-empty sets of constants.
   *-------------------------------------------------------------------------*)

  val known_constants : grammar -> string list

  val binders          : grammar -> string list
  val is_binder        : grammar -> string -> bool
  val binder_to_string : grammar -> binder -> string

  val resquan_op            : grammar -> string
  val associate_restriction : grammar ->
                              {binder : string option,
                               resbinder : string} -> grammar

  val grammar_tokens : grammar -> string list
  val rule_tokens : grammar -> grammar_rule -> string list

  val add_binder : {term_name:string,tok:string} -> grammar -> grammar
  val add_listform : grammar -> listspec -> grammar
  val listform_to_rule : listspec -> grule

  val fixityToString : fixity -> string
  val add_rule : grule -> grammar -> grammar
  val add_delta : user_delta -> grammar -> grammar
  val add_deltas : user_delta list -> grammar -> grammar

  val add_numeral_form : grammar -> (char * string option) -> grammar
  val give_num_priority : grammar -> char -> grammar
  val remove_numeral_form : grammar -> char -> grammar

  val add_strlit_injector: {ldelim: string, tmnm: string} -> grammar -> grammar
  val remove_strlit_injector : {tmnm:string} -> grammar -> grammar
  val strlit_map : grammar -> {tmnm:string} -> string option

  (*------------------------------------------------------------------------*
   * this removes all those rules which give special status to the          *
   * given string.  If there is a rule saying that COND is written          *
   *     if _ then _ else _                                                 *
   * you could get rid of it with                                           *
   *  remove_standard_form G "COND"                                         *
   *------------------------------------------------------------------------*)

  val remove_standard_form : grammar -> string -> grammar

  (* ----------------------------------------------------------------------
      these two remove rules relating to the term which also include
      a token, or the exact token list of the form given.
      Thus, if you had two rules for COND, and you wanted to get rid of
      the one with the "if" token in it, you would use

         remove_form_with_tok G {term_name = "COND", tok = "if"}
     ---------------------------------------------------------------------- *)

  val remove_form_with_tok : grammar -> {term_name : string, tok: string} ->
                             grammar
  val remove_form_with_toklist : {term_name : string, toklist : string list} ->
                                 grammar -> grammar

  (* this one is the nuclear option, and just removes every rule that uses
     the given token *)
  val remove_rules_with_tok : string -> grammar -> grammar

  val clear_overloads : grammar -> grammar

  (*-----------------------------------------------------------------------*
   * Pretty-printing                                                       *
   *-----------------------------------------------------------------------*)

  val prefer_form_with_tok : {term_name : string, tok : string} -> grammar ->
                             grammar
  val prefer_form_with_toklist : {term_name : string, toklist : string list} ->
                                 grammar -> grammar


  val set_associativity_at_level : grammar -> int * associativity -> grammar
  val get_precedence : grammar -> string -> fixity option
  val rules_for : grammar -> string -> (int * user_delta) list


  val prettyprint_grammar_rules
                          : (grammar -> term -> term_pp_types.uprinter) ->
                            ruleset -> term_pp_types.uprinter
  val prettyprint_grammar : (grammar -> term -> term_pp_types.uprinter) ->
                            grammar -> term_pp_types.uprinter

  val grammar_rule_reader : grammar_rule Coding.reader
  val grammar_rule_encode : grammar_rule -> string
  val user_delta_reader : (string -> term) -> user_delta Coding.reader
  val user_delta_encode : (term -> string) -> user_delta -> string
  val fixity_encode : fixity -> string
  val fixity_reader : fixity Coding.reader
  val grule_encode : grule -> string
  val grule_reader : grule Coding.reader

  val debugprint : grammar -> term -> string

end
