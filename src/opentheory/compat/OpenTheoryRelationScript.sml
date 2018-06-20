open HolKernel boolSyntax Opentheory
val Thy = "OpenTheoryRelation"
val pkg = "relation-1.61"
val _ = new_theory Thy
val file = pkg^".art"

val ERR=mk_HOL_ERR Thy

val _ = new_constant("dummy",alpha)
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="dummy"},name=([],pkg)}

val num = numSyntax.num
val _ = new_constant("empty",alpha-->beta-->bool)
val _ = new_constant("isSuc",num-->num-->bool)
val _ = new_type("set",1)
val _ = OpenTheoryMap.OpenTheory_tyop_name{tyop={Thy=Thy,Tyop="set"},name=(["Set"],"set")}
val _ = new_constant("fromSet",((pairSyntax.mk_prod(alpha,beta))-->bool)-->alpha-->beta-->bool)
val _ = new_constant("toSet",(alpha-->beta-->bool)-->(pairSyntax.mk_prod(alpha,beta))-->bool)
val _ = new_constant("bigIntersect",((alpha-->beta-->bool)-->bool)-->alpha-->beta-->bool)
val _ = new_constant("bigUnion",((alpha-->beta-->bool)-->bool)-->alpha-->beta-->bool)
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="empty"},name=(["Relation"],"empty")}
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="isSuc"},name=(["Number","Natural"],"isSuc")}
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="fromSet"},name=(["Relation"],"fromSet")}
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="toSet"},name=(["Relation"],"toSet")}
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="bigIntersect"},name=(["Relation"],"bigIntersect")}
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="bigUnion"},name=(["Relation"],"bigUnion")}
val _ = new_definition("fromPredicate_def",``fromPredicate (x:'a -> bool) = x``)
val _ = OpenTheoryMap.OpenTheory_const_name{const={Thy=Thy,Name="fromPredicate"},name=(["Set"],"fromPredicate")}

fun define_const {Name,Thy} tm =
  mk_thm([],(mk_eq(mk_thy_const {Name=Name,Thy=Thy,Ty=type_of tm},tm)))

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
