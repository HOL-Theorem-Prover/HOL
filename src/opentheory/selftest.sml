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
*)
val tmp = OS.FileSys.tmpName()
val bool_thms = if OS.Process.isSuccess(Systeml.system_ps (cmd pkg tmp)) then let
val A = INST_TYPE[alpha|->mk_vartype"A",beta|->mk_vartype"B"]
val reader = {
  define_tyop=fn _ => raise Fail "wasn't expecting to define any tyops",
  define_const=let val d =
  Redblackmap.fromList String.compare [
      ("Data.Bool.!", fn _ => {const={Thy="bool",Name="!"},def=A FORALL_DEF}),
      ("Data.Bool./\\\\", let
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
      ("Data.Bool.\\\\/", fn _ => {const={Thy="bool",Name="\\/"},def=OR_DEF}),
      ("Data.Bool.~", fn _ => {const={Thy="bool",Name="~"},def=NOT_DEF}),
      ("Data.Bool.cond", fn _ => {const={Thy="bool",Name="COND"},def=A COND_DEF}),
      ("Data.Bool.let", fn _ => {const={Thy="bool",Name="LET"},def=A LET_DEF}),
      ("Data.Bool.F", fn _ => {const={Thy="bool",Name="F"},def=F_DEF}),
      ("Data.Bool.T", fn _ => {const={Thy="bool",Name="T"},def=T_DEF})]
  in fn n => Redblackmap.find(d,n) end,
  axiom=let open List Net Thm
    fun ins th = insert(concl th,th)
    val n = ins (A ETA_AX) (ins (A SELECT_AX) empty)
    fun f _ (_,c) = hd (index c n)
  in f end }
val thms = read_article tmp reader
(* TODO: check that thms is the same set that opentheory
         says the package should have produced *)
in thms end else Net.empty

val pkg = "list-replicate-1.0"
(*
show: "Data.Bool"
show: "Data.List"
show: "Number.Natural"
show: "Number.Numeral"
input type operators: -> bool list natural
input constants: = ! /\ ==> ? select T :: [] length suc zero
assumptions:
  |- T
  |- (?) = \P. P ((select) P)
  |- !t. (!x. t) <=> t
  |- (!) = \P. P = \x. T
  |- !x. x = x <=> T
  |- (==>) = \p q. p /\ q <=> p
  |- (/\) = \p q. (\f. f p q) = \f. f T T
  |- (?) = \P. !q. (!x. P x ==> q) ==> q
  |- length [] = 0 /\ !h t. length (h :: t) = suc (length t)
  |- !P. P 0 /\ (!n. P n ==> P (suc n)) ==> !n. P n
  |- !e f. ?fn. fn 0 = e /\ !n. fn (suc n) = f (fn n) n
defined constants: replicate
axioms:
*)
val thms = if OS.Process.isSuccess(Systeml.system_ps (cmd pkg tmp)) then let
val A = INST_TYPE[alpha|->mk_vartype"A",beta|->mk_vartype"B"]
val reader = {
  define_tyop=fn _ => raise Fail "wasn't expecting to define any tyops",
  define_const=fn "Data.List.replicate" => (fn t => let
    val n = "replicate"
    val th = new_definition(n^(!Defn.def_suffix),(mk_eq(mk_var(n,type_of t),t)))
  in {const={Thy=current_theory(),Name="replicate"},def=th} end)
  | s => raise Fail ("wasn't expecting to define "^s),
  axiom=let open List Net Thm
    fun ins th = insert(concl th,th)
    val n = ins (A listTheory.LENGTH) (ins numTheory.INDUCTION bool_thms)
    val th = prove(``!e f. ?fn. (fn 0 = e) /\ !n. fn (SUC n) = f (fn n) n``,
                   METIS_TAC [prim_recTheory.PRIM_REC_THM])
    val n = ins (A th) n
    fun f _ (_,c) = hd (index c n)
  in f end }
val thms = read_article tmp reader
(* TODO: check that thms is the same set that opentheory
         says the package should have produced *)
in thms end else Net.empty
