local
  open HOLgrammars
in
datatype rule_element = TOK of string | TM

val fnapp_special : string
val bracket_special : string
val vs_cons_special : string
val rec_special : string
val std_binder_precedence : int

val reltoString : rule_element -> string

type rule_record = {term_name : string,
                    elements : rule_element list,
                    preferred : bool}

datatype binder = LAMBDA | BinderString of string
datatype prefix_rule = STD_prefix of rule_record list | BINDER of binder list
datatype suffix_rule = STD_suffix of rule_record list | TYPE_annotation
datatype infix_rule =
  STD_infix of rule_record list * associativity |
  RESQUAN of string list

type listspec =
  {separator : string, leftdelim : string, rightdelim : string,
   cons : string, nilstr : string}

datatype grammar_rule =
  PREFIX of prefix_rule
| SUFFIX of suffix_rule
| INFIX of infix_rule
| CLOSEFIX of rule_record list
| FNAPP | VSCONS
| LISTRULE of listspec list

type grammar

val rules : grammar -> (int option * grammar_rule) list
val grammar_rules : grammar -> grammar_rule list
val specials : grammar -> {type_intro : string,
                           lambda     : string,
                           endbinding : string,
                           restr_binders : (binder * string) list}

val binders : grammar -> string list
val is_binder : grammar -> string -> bool
val binder_to_string : grammar -> binder -> string

val resquans : grammar -> string list
val associate_restriction : grammar -> binder * string -> grammar

val compatible_listrule :
  grammar -> {separator : string, leftdelim : string, rightdelim : string} ->
  {cons : string, nilstr : string} option

datatype stack_terminal =
  STD_HOL_TOK of string | BOS | EOS | Id  | TypeColon | TypeTok | EndBinding |
  VS_cons

val STtoString : grammar -> stack_terminal -> string
val stdhol : grammar

val grammar_tokens : grammar -> string list
val find_suffix_rhses : grammar -> stack_terminal list
val find_prefix_lhses : grammar -> stack_terminal list

val add_listform : grammar -> {separator : string, leftdelim : string,
                               rightdelim : string, cons : string,
                               nilstr : string} -> grammar
(* this removes all those rules which give special status to the
   given string.  If there is a rule saying that COND is written
      if _ then _ else _
   you could get rid of it with
      remove_standard_form G "COND"
*)
val remove_standard_form : grammar -> string -> grammar
val remove_form_with_tok :
  grammar -> {term_name : string, tok: string} -> grammar

val clear_prefs_for : string -> grammar -> grammar
val prefer_form_with_tok :
  grammar -> {term_name : string, tok : string} -> grammar

val add_binder : grammar -> (string * int) -> grammar

datatype rule_fixity =
  Infix of associativity * int | Closefix | Suffix of int | TruePrefix of int
val rule_fixityToString : rule_fixity -> string
val add_rule : grammar -> (string * rule_fixity * rule_element list) -> grammar
val add_grule : grammar -> (int option * grammar_rule) -> grammar

val set_associativity_at_level : grammar -> (int * associativity) -> grammar
val get_precedence : grammar -> string -> rule_fixity option


val Gmerge : (grammar * (int option * grammar_rule) list) -> grammar
end
