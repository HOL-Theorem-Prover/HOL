
signature term_grammar =
sig

  type ppstream = Portable.ppstream
  type block_info = Portable.break_style * int
  type overload_info = Overload.overload_info
  type associativity = HOLgrammars.associativity

  datatype rule_element
     = TOK of string
     | TM
  val RE_compare : rule_element * rule_element -> order

  datatype pp_element
     = PPBlock of pp_element list * block_info
     | EndInitialBlock of block_info
     | BeginFinalBlock of block_info
     | HardSpace of int
     | BreakSpace of (int * int)
     | RE of rule_element
     | LastTM
     | FirstTM   (* these last two only used internally *)

  datatype PhraseBlockStyle
     = AroundSameName
     | AroundSamePrec
     | AroundEachPhrase
     | NoPhrasing

  datatype ParenStyle
     = Always
     | OnlyIfNecessary
     | NotEvenIfRand
     | ParoundName
     | ParoundPrec

  val rule_elements  : pp_element list -> rule_element list
  val pp_elements_ok : pp_element list -> bool

  val reltoString    : rule_element -> string

  type rule_record = {term_name   : string,
                      elements    : pp_element list,
                      timestamp   : int,
                      block_style : PhraseBlockStyle * block_info,
                      paren_style : ParenStyle}

  datatype binder
     = LAMBDA
     | BinderString of {tok : string, term_name : string, timestamp : int}

  datatype prefix_rule
     = STD_prefix of rule_record list
     | BINDER of binder list

  datatype suffix_rule
     = STD_suffix of rule_record list
     | TYPE_annotation

  datatype infix_rule
     = STD_infix of rule_record list * associativity
     | RESQUAN_OP
     | VSCONS
     | FNAPP of rule_record list

  type listspec =
     {separator  : pp_element list,
      leftdelim  : pp_element list,
      rightdelim : pp_element list,
      block_info : block_info,
      cons       : string,
      nilstr     : string}

  datatype grammar_rule
     = PREFIX of prefix_rule
     | SUFFIX of suffix_rule
     | INFIX of infix_rule
     | CLOSEFIX of rule_record list
     | LISTRULE of listspec list

  type grammar

  datatype rule_fixity
     = Infix of associativity * int
     | Closefix
     | Suffix of int
     | Prefix of int

  datatype user_delta =
           GRULE of {term_name : string,
                     fixity : rule_fixity,
                     pp_elements: pp_element list,
                     paren_style : ParenStyle,
                     block_style : PhraseBlockStyle * block_info}
         | LRULE of listspec
         | BRULE of {tok : string, term_name : string}

  val userdelta_toks : user_delta -> string list
  val userdelta_name : user_delta -> string

  val stdhol         : grammar
  val min_grammar    : grammar
  val merge_grammars : grammar * grammar -> grammar
  val fupdate_overload_info :
    (overload_info -> overload_info) -> grammar -> grammar
  val mfupdate_overload_info :
    (overload_info -> overload_info * 'a) -> grammar -> grammar * 'a


  (* User code additions *)
  (* Users can add special-purpose printers and parsers to grammars *)
  type term = Term.term
  type userprinter = (type_grammar.grammar * grammar) term_pp_types.userprinter
  val add_user_printer :
    (string * term * userprinter) -> grammar ->
    grammar
  val remove_user_printer :
    string -> grammar -> (grammar * (term * userprinter) option)
  val user_printers :
    grammar -> (term * string * userprinter)Net.net

  val absyn_postprocessors : grammar ->
                             (string * (Absyn.absyn -> Absyn.absyn)) list
  val new_absyn_postprocessor : string * (Absyn.absyn -> Absyn.absyn) ->
                                grammar -> grammar
  val remove_absyn_postprocessor :
      string -> grammar ->
      (grammar * (Absyn.absyn -> Absyn.absyn) option)


  type special_info = {type_intro    : string,
                       lambda        : string list,
                       endbinding    : string,
                       restr_binders : (string option * string) list,
                       res_quanop    : string}
  val rules          : grammar -> (int option * grammar_rule) list
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

  val compatible_listrule : grammar
                             -> {separator : string,
                                 leftdelim : string,
                                 rightdelim : string}
                             -> {cons : string, nilstr : string} option

  datatype stack_terminal
     = STD_HOL_TOK of string
     | BOS
     | EOS
     | Id
     | TypeColon
     | TypeTok
     | EndBinding
     | VS_cons
     | ResquanOpTok
  val ST_compare : stack_terminal * stack_terminal -> order

  val STtoString : grammar -> stack_terminal -> string

  val grammar_tokens : grammar -> string list
  val rule_tokens : grammar -> grammar_rule -> string list
  val find_suffix_rhses : grammar -> stack_terminal list
  val find_prefix_lhses : grammar -> stack_terminal list

  val add_binder : {term_name:string,tok:string} -> grammar -> grammar
  val add_listform : grammar -> listspec -> grammar

  val rule_fixityToString : rule_fixity -> string
  val add_rule : grammar
                  -> {term_name : string,
                      fixity : rule_fixity,
                      pp_elements: pp_element list,
                      paren_style : ParenStyle,
                      block_style : PhraseBlockStyle * block_info}
                  -> grammar
  val add_delta : user_delta -> grammar -> grammar

  val add_numeral_form : grammar -> (char * string option) -> grammar
  val give_num_priority : grammar -> char -> grammar
  val remove_numeral_form : grammar -> char -> grammar

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

  (*-----------------------------------------------------------------------*
   * Pretty-printing                                                       *
   *-----------------------------------------------------------------------*)

  val prefer_form_with_tok : {term_name : string, tok : string} -> grammar ->
                             grammar
  val prefer_form_with_toklist : {term_name : string, toklist : string list} ->
                                 grammar -> grammar


  val set_associativity_at_level : grammar -> int * associativity -> grammar
  val get_precedence : grammar -> string -> rule_fixity option
  val rules_for : grammar -> string -> (int * user_delta) list


  val prettyprint_grammar_rules
                          : (grammar -> ppstream -> term -> unit) ->
                            ppstream -> grammar -> unit
  val prettyprint_grammar : (grammar -> ppstream -> term -> unit) ->
                            ppstream -> grammar -> unit

  val grule_reader : grammar_rule Coding.reader
  val grule_encode : grammar_rule -> string
  val user_delta_reader : user_delta Coding.reader
  val user_delta_encode : user_delta -> string
  val fixity_encode : rule_fixity -> string
  val fixity_reader : rule_fixity Coding.reader

end
