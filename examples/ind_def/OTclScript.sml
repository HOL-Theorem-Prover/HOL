open Opentheory HolKernel
val _ = new_theory "OTcl"
val file = "cl.art"
fun ML_name "#" = "APP"
  | ML_name "-->" = "redn"
  | ML_name "-||->" = "predn"
  | ML_name s = s
val reader = {
  const_name=fn n as (ns,Name) => case ns of
    ["cl"] => {Thy="OTcl",Name=Name}
  | ["cl","cl"] => {Thy="OTcl",Name="cl."^Name}
  | _ => const_name_in_map n,
  tyop_name=fn n as (ns,Tyop) => case ns of
    ["cl"] => {Thy="OTcl",Tyop=Tyop}
  | _ => tyop_name_in_map n,
  define_tyop=define_tyop_in_thy,
  define_const=define_const_in_thy ML_name,
  axiom=axiom_in_db
}
val thms = read_article file reader
val thms = Net.listItems thms
val _ = delete_unused_consts thms
val exports = boolLib.LIST_CONJ thms
val _ = save_thm("exports",exports)
val _ = export_theory ()
