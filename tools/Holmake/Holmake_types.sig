datatype pretoken = DEFN of string | RULE of string | EOF

datatype frag = LIT of string | VREF of string
type quotation = frag list

datatype token = HM_defn of string * quotation
               | HM_rule of { targets : quotation, dependencies : quotation,
                              commands : quotation list }

type env = string -> quotation

val to_token : pretoken -> token

val perform_substitution : env -> quotation -> string

val extend_env : token list -> env -> env
val empty_env : env

val tokenize : string -> string list
val dequote : string -> string

val mk_rules : token list -> env ->
               { target : string, dependencies : string list,
                 commands : string list} list