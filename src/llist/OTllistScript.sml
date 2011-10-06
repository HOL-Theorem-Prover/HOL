open Opentheory HolKernel
val _ = new_theory "OTllist"
local open set_relationTheory in end
local open OpenTheoryMap bossLib Tactical boolTheory in
val id_def = Define`id x = x`
val _ = OpenTheory_const_name{const={Thy="OTllist",Name="id"},name=(["Unwanted"],"id")}
val id_NUMERAL = prove(``id = NUMERAL``,METIS_TAC[arithmeticTheory.NUMERAL_DEF,id_def])
val id_Abbrev  = prove(``id = Abbrev``,SRW_TAC[][markerTheory.Abbrev_def,id_def,FUN_EQ_THM])
end
val file = "llist.art"
fun ML_name s = s
val reader = {
  const_name=fn n as (ns,Name) => case ns of
    ["llist"] => {Thy="OTllist",Name=Name}
  | ["llist","llist"] => {Thy="OTllist",Name="llist_"^Name}
  | _ => const_name_in_map n,
  tyop_name=fn n as (ns,Tyop) => case ns of
    ["llist"] => {Thy="OTllist",Tyop=Tyop}
  | _ => tyop_name_in_map n,
  define_tyop=define_tyop_in_thy,
  define_const=define_const_in_thy ML_name,
  axiom=fn ths => fn goal => axiom_in_db ths goal
        handle HOL_ERR _ => let
          open bossLib proofManagerLib arithmeticTheory numeralTheory combinTheory
          val _ = set_goal goal
          val _ = expand(METIS_TAC[id_def,id_NUMERAL,id_Abbrev,ALT_ZERO,SUC_SUB1,SUC_ONE_ADD,MULT_CLAUSES,
                                   numeral_eq,numeral_distrib,numeral_lte,numeral_suc,numeral_add,
                                   LET_FORALL_ELIM])
          handle HOL_ERR e => (Parse.print_backend_term(#2 goal); raise HOL_ERR e)
          val t = top_thm()
          val _ = drop()
          in t end
}
val thms = read_article file reader
val thms = Net.listItems thms
val _ = delete_unused_consts thms
val exports = boolLib.LIST_CONJ thms
val _ = save_thm("exports",exports)
val _ = export_theory ()
