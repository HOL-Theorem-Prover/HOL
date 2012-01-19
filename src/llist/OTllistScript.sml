open Opentheory HolKernel
val prove = Tactical.prove
val METIS_TAC = bossLib.METIS_TAC
val _ = new_theory "OTllist"
local open set_relationTheory in end
local open OpenTheoryMap bossLib boolTheory in
end
val file = "llist.art"
fun ML_name s = s
val _ = metisTools.limit := {time = SOME 1.0 , infs = NONE}
val reader = {
  const_name=fn n as (ns,Name) => case ns of
    ["llist"] => {Thy="OTllist",Name=Name}
  | ["llist","llist"] => {Thy="OTllist",Name="llist_"^Name}
  | _ => if ns = ["Unwanted"] andalso Name = "id" then {Thy="OTllist",Name="id"}
  else const_name_in_map n,
  tyop_name=fn n as (ns,Tyop) => case ns of
    ["llist"] => {Thy="OTllist",Tyop=Tyop}
  | _ => tyop_name_in_map n,
  define_tyop=define_tyop_in_thy,
  define_const=define_const_in_thy ML_name,
  axiom=fn ths => fn goal => axiom_in_db ths goal
        handle HOL_ERR _ => let
          open arithmeticTheory numeralTheory combinTheory markerTheory
          val ([],goal) = goal
        in
          prove(goal,METIS_TAC[ALT_ZERO,SUC_SUB1,SUC_ONE_ADD,MULT_CLAUSES,NUMERAL_DEF,Abbrev_def,
                               numeral_eq,numeral_distrib,numeral_lte,numeral_suc,numeral_add,
                               LET_FORALL_ELIM])
          handle HOL_ERR e => (Parse.print_backend_term goal; raise HOL_ERR e)
        end
}
val thms = read_article file reader
val thms = Net.listItems thms
val _ = delete_unused_consts thms
val exports = boolLib.LIST_CONJ thms
val _ = save_thm("exports",exports)
val _ = export_theory ()
