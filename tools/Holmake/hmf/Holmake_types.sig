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

(* A pattern rule has at least one target containing exactly one `%'
   character.  Dependency tokens may also contain a `%' which is
   replaced by the stem matched in the target.  Recipes are stored as
   raw quotations; stem substitution happens at match time. *)
type patrule = {targets : string list, deps : string list,
                commands : quotation list}
type patrules = patrule list
val empty_ruledb : ruledb
val empty_patrules : patrules
val extend_ruledb : (string -> unit) -> env -> raw_rule_info ->
                    (ruledb * depdb * patrules) ->
                    (ruledb * depdb * patrules * string list)
val get_rule_info : ruledb -> env -> string -> rule_info option
val match_pattern_rules :
    (string -> bool) -> env -> patrules -> string -> rule_info option

(*

   [extend_ruledb warn env rule_info (rdb,ddb,prs)] returns a quadruple
   of a rule database, dependency database, list of pattern rules, and
   the non-pattern targets of the rule (used by callers to track the
   first explicit target, which becomes the default goal).

   The rdb/ddb databases map exact-match target names to dependency
   and command information (via get_rule_info).  Pattern rules are
   appended to the patrules list in source order.  The warn function
   is used to output warning messages about the rule_info.

   [match_pattern_rules can_make env prs tgt] walks prs in order,
   returning the rule_info of the first pattern rule that (a) has a
   target pattern matching tgt and (b) whose every substituted
   dependency satisfies can_make.  can_make is the caller's
   "this prereq is either present on disk or has a rule" check;
   without it pattern rules would happily claim targets whose
   declared prereqs don't exist and can't be built (GNU make's
   two-phase implicit-rule search).  Stem substitution is applied
   to the rule's deps; the recipe's quotations are then expanded
   with $@, $<, $* (stem), and $^ (space-joined deps) bound in env.
   Returns NONE if no pattern rule matches.  *)

end
