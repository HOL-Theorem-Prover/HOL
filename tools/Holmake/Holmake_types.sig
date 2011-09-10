signature Holmake_types =
sig

datatype pretoken = DEFN of string | RULE of string | EOF

datatype frag = LIT of string | VREF of string
type quotation = frag list

type raw_rule_info = { targets : quotation, dependencies : quotation,
                       commands : quotation list }

datatype token = HM_defn of string * quotation
               | HM_rule of raw_rule_info

type env

val base_environment : env

val env_extend : string * quotation -> env -> env

val to_token : pretoken -> token

val perform_substitution : env -> quotation -> string

val tokenize : string -> string list
val dequote : string -> string
val extract_normal_quotation : Substring.substring -> quotation
val extract_cmd_quotation : Substring.substring -> quotation

type rule_info = {dependencies : string list, commands : string list}

type ruledb
type depdb = (string,string list)Binarymap.dict
val empty_ruledb : ruledb
val extend_ruledb : (string -> unit) -> env -> raw_rule_info ->
                    (ruledb * depdb) -> (ruledb * depdb)
val get_rule_info : ruledb -> env -> string -> rule_info option

(*

   [extend_ruledb warn env rule_info (rdb,ddb)] returns a pair of a
   rule database and dependency database, extending those given as inputs.

   The databases are used to map target names to dependency and
   command information (using the get_rule_info function).  The warn
   function is used to output warning messages about the rule_info.  *)

end
