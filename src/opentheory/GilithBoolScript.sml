open boolTheory bossLib boolLib Opentheory OpenTheoryMap HolKernel
val _ = new_theory "GilithBool"
val tmp = OS.FileSys.tmpName()
val pkg = "bool-1.0"
val cmd = ("opentheory info --article -o "^tmp^" "^pkg)
val A = INST_TYPE[alpha|->mk_vartype"A",beta|->mk_vartype"B"]
fun const_def (c,th) = let
  val n = Map.find(const_to_ot_map(),c)
  handle Map.NotFound => raise Fail ("No map for "^(#Thy c)^"$"^(#Name c))
in (n, fn _ => {const=c,def=th}) end
val rv = Systeml.system_ps cmd
val _ = if OS.Process.isSuccess rv then let
val reader = {
  define_tyop=fn _ => raise Fail "wasn't expecting to define any tyops",
  define_const=let val d =
  Redblackmap.fromList String.compare [
    const_def({Thy="bool",Name="!"},A FORALL_DEF),
    const_def({Thy="bool",Name="/\\"},
        prove(``$/\ = \p q. (\f. f p q) = \f:bool->bool->bool. f T T``,
              SRW_TAC [][AND_DEF,FUN_EQ_THM] THEN EQ_TAC THEN SRW_TAC [][])),
    const_def({Thy="min",Name="==>"},
        METIS_PROVE [] ``$==> = \p q. p /\ q <=> p``),
    const_def({Thy="bool",Name="?"},
        A(prove(``$? = \P. !q. (!x. P x ==> q) ==> q``,
              SRW_TAC [][EXISTS_DEF,FUN_EQ_THM,EQ_IMP_THM] THEN
              FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [SELECT_AX]))),
    const_def({Thy="bool",Name="?!"},A EXISTS_UNIQUE_DEF),
    const_def({Thy="bool",Name="\\/"},OR_DEF),
    const_def({Thy="bool",Name="~"},NOT_DEF),
    const_def({Thy="bool",Name="COND"},A COND_DEF),
    const_def({Thy="bool",Name="LET"},A LET_DEF),
    const_def({Thy="bool",Name="F"},F_DEF),
    const_def({Thy="bool",Name="T"},T_DEF)]
  in fn n => Redblackmap.find(d,n) end,
  axiom=let open List Net Thm
    fun ins th = insert(concl th,th)
    val n = ins (A ETA_AX) (ins (A SELECT_AX) empty)
    fun f _ (_,c) = hd (index c n)
  in f end }
val thms = read_article tmp reader
in save_thm("exports",LIST_CONJ(Net.listItems thms)) end
else save_thm("exports",boolTheory.TRUTH)
val _ = export_theory ()
