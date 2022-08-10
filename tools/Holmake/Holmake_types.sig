signature Holmake_types =
sig

datatype pretoken = DEFN of string
                  | DEFN_EXTEND of string
                  | RULE of string | EOF

datatype frag = LIT of string | VREF of string
type quotation = frag list

type raw_rule_info = { targets : quotation, dependencies : quotation,
                       commands : quotation list }

datatype token = HM_defn of {vname : string, rhs : quotation, extendp : bool}
               | HM_rule of raw_rule_info

type env

val base_environment : unit -> env
val lookup : env -> string -> quotation
val env_keys : env -> string list
val env_extend : string * quotation -> env -> env
val env_fold : (string -> quotation -> 'b -> 'b) -> env -> 'b -> 'b

val to_token : env -> pretoken -> token

val perform_substitution : env -> quotation -> string

val tokenize : string -> string list
val dequote : string -> string
val extract_normal_quotation : Substring.substring -> quotation
val extract_cmd_quotation : Substring.substring -> quotation

type rule_info = {dependencies : string list, commands : string list}

type ruledb =
     (string, {dependencies:string list, commands : quotation list})Binarymap.dict
type depdb = (string,string list)Binarymap.dict
val empty_ruledb : ruledb
val extend_ruledb : (string -> unit) -> env -> raw_rule_info ->
                    (ruledb * depdb) -> (ruledb * depdb * string list)
val get_rule_info : ruledb -> env -> string -> rule_info option

(*

   [extend_ruledb warn env rule_info (rdb,ddb)] returns a pair of a
   rule database and dependency database, extending those given as inputs, and
   a list of the targets of the rule.

   The databases are used to map target names to dependency and
   command information (using the get_rule_info function).  The warn
   function is used to output warning messages about the rule_info.  *)

end
