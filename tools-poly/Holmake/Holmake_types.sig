signature Holmake_types =
sig
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

type rule_info = {dependencies : string list, commands : string list}

val mk_rules : (string -> unit) -> token list -> env ->
               (string option * (string, rule_info) Binarymap.dict)

(*
   [mk_rules warn toklist e] returns a pair of a possibly absent first target,
   and a rule "database", mapping target names to dependency and command
   information.  The warn function is used to output warning messages
   about the toklist.
*)
end
