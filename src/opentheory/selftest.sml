open Opentheory boolTheory boolLib bossLib HolKernel
fun cmd pkg out = ("opentheory info --article -o "^out^" "^pkg)
val pkg = "bool-1.0"
(*
show: "Data.Bool"
input type operators: -> bool
input constants: = select
assumptions:
defined constants: ! /\ ==> ? ?! \/ ~ cond let F T
axioms:
  |- !t. (\x. t x) = t
  |- !P x. P x ==> P ((select) P)

  types=typesFromList
  [("bool",fn [] => Type.bool),
   ("->",fn ls => Type.mk_type("fun",ls))],
  consts=constsFromList
  [("=",fn ty => Term.mk_const("=",ty)),
   ("Data.Bool.select",fn ty => Term.mk_const("@",ty))]
*)
val tmp = OS.FileSys.tmpName()
val _ = if OS.Process.isSuccess(Systeml.system_ps (cmd pkg tmp)) then let
val input = TextIO.openIn tmp
val tyop_from_ot = Redblackmap.fromList String.compare [
  ("bool",{Thy="min",Tyop="bool"}),
  ("->",{Thy="min",Tyop="fun"})]
val const_from_ot = Redblackmap.fromList String.compare [
  ("=",{Thy="min",Name="="}),
  ("Data.Bool.select",{Thy="min",Name="@"})]
val A = INST_TYPE[alpha|->mk_vartype"A",beta|->mk_vartype"B"]
val reader = {
  tyops=Redblackmap.mkDict String.compare,
  consts=
  Redblackmap.fromList String.compare [
      ("Data.Bool.!", fn _ => {const={Thy="bool",Name="!"},def=A FORALL_DEF}),
      ("Data.Bool./\\", let
        val th = prove(``$/\ = \p q. (\f. f p q) = \f:bool->bool->bool. f T T``,
                       SRW_TAC [][AND_DEF,FUN_EQ_THM] THEN EQ_TAC THEN SRW_TAC [][])
        in fn _ => {const={Thy="bool",Name="/\\"},def=th} end),
      ("Data.Bool.==>",let
        val th = METIS_PROVE [] ``$==> = \p q. p /\ q <=> p``
        in fn _ => {const={Thy="min",Name="==>"},def=th} end),
      ("Data.Bool.?", let
         val th = prove(``$? = \P. !q. (!x. P x ==> q) ==> q``,
                        SRW_TAC [][EXISTS_DEF,FUN_EQ_THM,EQ_IMP_THM] THEN
                        FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [SELECT_AX])
        in fn _ => {const={Thy="bool",Name="?"},def=A th} end),
      ("Data.Bool.?!", fn _ => {const={Thy="bool",Name="?!"},def=A EXISTS_UNIQUE_DEF}),
      ("Data.Bool.\\/", fn _ => {const={Thy="bool",Name="\\/"},def=OR_DEF}),
      ("Data.Bool.~", fn _ => {const={Thy="bool",Name="~"},def=NOT_DEF}),
      ("Data.Bool.cond", fn _ => {const={Thy="bool",Name="COND"},def=A COND_DEF}),
      ("Data.Bool.let", fn _ => {const={Thy="bool",Name="LET"},def=A LET_DEF}),
      ("Data.Bool.F", fn _ => {const={Thy="bool",Name="F"},def=F_DEF}),
      ("Data.Bool.T", fn _ => {const={Thy="bool",Name="T"},def=T_DEF})],
  axioms=let open List Net Thm
    fun ins th = insert(concl th,th)
    val n = ins (A ETA_AX) (ins (A SELECT_AX) empty)
    fun f _ (_,c) = hd (index c n)
  in f end }
val thms = raw_read_article {tyop_from_ot=tyop_from_ot, const_from_ot=const_from_ot} input reader
(* TODO: check that thms is the same set that opentheory
         says the package should have produced *)
in () end else ()
