open HolKernel boolSyntax Opentheory
val _ = new_theory"OpenTheoryBool"
val file = "bool-1.37.art"

val ERR=mk_HOL_ERR"OpenTheoryBool"

val _ = new_constant("dummy",alpha)
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy="OpenTheoryBool",Name="dummy"},name=([],"bool-1.37")}

val reader = {
  const_name = const_name_in_map,
  tyop_name = tyop_name_in_map,
  define_tyop = define_tyop_in_thy,
  define_const = fn {Name,Thy} => fn tm => mk_thm([],(mk_eq(mk_thy_const {Name=Name,Thy=Thy,Ty=type_of tm},tm))),
  axiom = axiom_in_db
};
val thms = read_article file reader;
val _ = Net.itnet (fn th => fn n => (save_thm("OTbool"^Int.toString(n),th); n+1)) thms 0;

val _ = export_theory()
