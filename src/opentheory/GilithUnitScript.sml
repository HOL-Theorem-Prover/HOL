open bossLib boolLib OpenTheoryMap Opentheory HolKernel
val Thy = "GilithUnit"
val _ = new_theory Thy
val tmp = OS.FileSys.tmpName()
val pkg = "unit-1.0"
val cmd = ("opentheory info --article -o "^tmp^" "^pkg)
fun const_def (c,th) = let
  val n = Map.find(const_to_ot_map(),c)
  handle Map.NotFound => raise Fail ("No map for "^(#Thy c)^"$"^(#Name c))
in (n, fn _ => {const=c,def=th}) end
val rv = Systeml.system_ps cmd
val _ = if OS.Process.isSuccess rv then let
val reader = {
  define_tyop=fn _ => let
    val ABS = "one_abs"
    val REP = "one_rep"
    val tyax = REWRITE_RULE[GSYM boolTheory.TYPE_DEFINITION_THM]oneTheory.one_TY_DEF
    val th = define_new_type_bijections {name="one_repfns",ABS=ABS,REP=REP,tyax=tyax}
    val [abs_rep,rep_abs] = CONJUNCTS th
    val abs_rep = SPEC_ALL abs_rep
    val rep_abs = SPEC_ALL rep_abs
    val rep=prim_mk_const{Thy=Thy,Name=REP}
    val abs=prim_mk_const{Thy=Thy,Name=ABS}
  in fn _ => {rep_abs=rep_abs,abs_rep=abs_rep,rep=rep,abs=abs,tyop={Thy="one",Tyop="one"}} end,
  define_const=let
    val (_,r) = const_def({Thy="one",Name="one"},oneTheory.one_DEF)
  in fn _ => r end,
  axiom=let open List Net Thm
    fun f th n = let
      val (th1,th2) = CONJ_PAIR th
    in f th2 (insert(concl th1,th1) n) end
    handle HOL_ERR _ => n
    val n = f GilithBoolTheory.exports empty
    fun f _ (_,c) = hd (index c n)
  in f end }
val thms = read_article tmp reader
in save_thm("exports",LIST_CONJ(Net.listItems thms)) end
else save_thm("exports",boolTheory.TRUTH)
val _ = export_theory ()
