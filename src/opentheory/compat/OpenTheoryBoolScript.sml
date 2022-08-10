open HolKernel boolSyntax OpenTheoryReader;

val Thy = "OpenTheoryBool";
val pkg = "bool-1.37";

val _ = new_theory Thy;
val file = pkg^".art"

val ERR = mk_HOL_ERR Thy;

val _ = new_constant("dummy",alpha)
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="dummy"},name=([],pkg)}

fun define_const {Name,Thy} tm =
    mk_thm([],(mk_eq(mk_thy_const {Name=Name,Thy=Thy,Ty=type_of tm},tm)));

val (reader:reader) = {
  const_name = const_name_in_map,
  tyop_name = tyop_name_in_map,
  define_tyop = define_tyop_in_thy,
  define_const = define_const,
  axiom = K mk_thm
};

val thms = read_article file reader;
val _ = Net.itnet (fn th => fn n => (save_thm("th"^Int.toString(n),th); n+1)) thms 0;

val _ = export_theory()
