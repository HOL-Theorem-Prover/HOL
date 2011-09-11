open Opentheory OpenTheoryMap OpenTheoryCommon HolKernel boolLib bossLib
val _ = new_theory "OTcl"
val imp_def = METIS_PROVE[]``$==> = (\p q. p /\ q = p)``;
val and_def = prove(``$/\ = (\p q. (\f:bool->bool->bool. f p q) = (\f. f T T))``,
SRW_TAC [][FUN_EQ_THM,EQ_IMP_THM]);
val exists_def = prove(``$? = (λP. ∀q. (∀x. P x ⇒ q) ⇒ q)``,
SRW_TAC [][FUN_EQ_THM] THEN
SUBST_TAC [GSYM (ISPEC ``P:'a->bool`` ETA_THM)] THEN
METIS_TAC [])
val file = "cl.art"
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="confluent"},name="combinatoryLogicExample.confluent"}
val _ = OpenTheory_tyop_name{tyop={Thy="OTcl",Tyop="cl"},name="combinatoryLogicExample.cl"}
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="-->"},name="combinatoryLogicExample.-->"}
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="S"},name="combinatoryLogicExample.S"}
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="K"},name="combinatoryLogicExample.K"}
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="#"},name="combinatoryLogicExample.#"}

val _ = OpenTheory_const_name{const={Thy="OTcl",Name="mk_cl"},name="combinatoryLogicExample.ind_type.mk_cl"}
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="dest_cl"},name="combinatoryLogicExample.ind_type.dest_cl"}

val _ = OpenTheory_const_name{const={Thy="OTcl",Name="junk_rep"},name="combinatoryLogicExample.cl.rep"}
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="junk_abs"},name="combinatoryLogicExample.cl.abs"}
val _ = OpenTheory_const_name{const={Thy="OTcl",Name="junk_2"},name="combinatoryLogicExample.ind_type.junk_2"}
val reader = {
  define_tyop=fn {name={Thy="OTcl",Tyop},ax,args,rep={Thy="OTcl",Name=rep},abs={Thy="OTcl",Name=abs}} => let
    val (P,t) = dest_comb (concl ax)
    val v     = variant (free_vars P) (mk_var ("v",type_of t))
    val th    = new_type_definition(Tyop,EXISTS(mk_exists(v,mk_comb(P,v)),t) ax)
    val bij   = define_new_type_bijections {name=Tyop^"_bij",ABS=abs,REP=rep,tyax=th}
    val [ar,ra] = CONJUNCTS bij
    val _ = Feedback.HOL_MESG("Defined tyop "^Tyop)
    in {rep_abs=SPEC_ALL ra,abs_rep=SPEC_ALL ar} end
    | _ => raise Fail "define_tyop",

  define_const=fn name => raise Fail ("define_const "^(thy_const_to_string name)),

  axiom=let
    open boolTheory
    val l = ref [imp_def,FORALL_DEF,TRUTH,and_def,ETA_AX,EXISTS_DEF,IMP_ANTISYM_AX,OR_DEF,exists_def,
                 MONO_OR,IMP_CLAUSES,MONO_EXISTS,MONO_AND,TYPE_DEFINITION]
    fun a ths (h,c) = let
      val (th,r) = Lib.pluck (fn th => c = concl th) (!l)
      val _ = l := r
    in th end handle HOL_ERR _ => raise Fail("axiom "^Parse.term_to_backend_string c)
  in a end
}
val thms = read_article file reader
val _ = save_thm("exports",LIST_CONJ(Net.listItems thms))
val _ = export_theory ()
