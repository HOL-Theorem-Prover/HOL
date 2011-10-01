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

fun ML_name "#" = "APP"
  | ML_name "-->" = "redn"
  | ML_name "-||->" = "predn"
  | ML_name s = s

val reader = {
  const_name=fn n as (ns,Name) => case ns of
    ["cl"] => {Thy="OTcl",
      Name=if String.isSubstring "ind_type" Name
           then let open Substring in "junk"^(string (taker Char.isDigit (full Name))) end
           else Name}
  | ["cl","cl"] => {Thy="OTcl",Name="cl."^Name}
  | _ => const_name_in_map n,
  tyop_name=fn n as (ns,Tyop) => case ns of
    ["cl"] => {Thy="OTcl",Tyop=Tyop}
  | _ => tyop_name_in_map n,

  define_tyop=fn {name={Thy="OTcl",Tyop},ax,args,rep={Thy="OTcl",Name=rep},abs={Thy="OTcl",Name=abs}} => let
    val (P,t) = dest_comb (concl ax)
    val v     = variant (free_vars P) (mk_var ("v",type_of t))
    val th    = new_type_definition(Tyop,EXISTS(mk_exists(v,mk_comb(P,v)),t) ax)
    val bij   = define_new_type_bijections {name=Tyop^"_bij",ABS=abs,REP=rep,tyax=th}
    val [ar,ra] = CONJUNCTS bij
    val _ = Feedback.HOL_MESG("Defined tyop "^Tyop)
    in {rep_abs=SPEC_ALL ra,abs_rep=SPEC_ALL ar} end
               | _ => raise Fail "define_tyop",

  define_const=fn {Thy="OTcl",Name} => (fn rhs => new_definition ((ML_name Name)^"_def",mk_eq(mk_var(Name,type_of rhs),rhs)))
                | _ => raise Fail "define_const ",

  axiom=let
    open boolTheory
    val l = ref [imp_def,and_def,exists_def]
    fun a ths (h,c) = let
      val (th,r) = Lib.pluck (fn th => c = concl th) (!l)
      val _ = l := r
    in th end handle HOL_ERR _ =>
      fst(snd(Lib.first(fn (_,(th,_)) => aconv (concl th) c) (DB.match ["bool","ind_type","sat","combin"] c)))
    handle _ => raise Fail("axiom "^Parse.term_to_backend_string c)
  in a end
}
val thms = read_article file reader
val _ = save_thm("exports",LIST_CONJ(Net.listItems thms))
val _ = export_theory ()
