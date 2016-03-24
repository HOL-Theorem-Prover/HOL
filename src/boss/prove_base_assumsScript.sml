open HolKernel boolLib Opentheory

val Thy = "prove_base_assums";

val _ = new_theory Thy;

val _ = new_constant("base-1.200",alpha);

fun fix_tyop {abs={Name="_",Thy=athy},rep={Name="_",Thy=rthy},args,ax,name={Thy=tthy,Tyop=tyop}} =
  {abs={Name=(tyop^"_abs"),Thy=athy},
   rep={Name=(tyop^"_rep"),Thy=rthy},
   name={Thy=tthy,Tyop=tyop},
   args=args,
   ax=ax}
| fix_tyop x = x

fun const_name ([],"=") = {Thy="min",Name="="}
  | const_name ([],"select") = {Thy="min",Name="@"}
  | const_name (["Data","Bool"],"==>") = {Thy="min",Name="==>"}
  | const_name (["Data","Bool"],"~") = {Thy="bool",Name="~"}
  | const_name (["Data","Bool"],"!") = {Thy="bool",Name="!"}
  | const_name (["Data","Bool"],"?") = {Thy="bool",Name="?"}
  | const_name (["Data","Bool"],"?!") = {Thy="bool",Name="?!"}
  | const_name (["Data","Bool"],"\\/") = {Thy="bool",Name="\\/"}
  | const_name (["Data","Bool"],"/\\") = {Thy="bool",Name="/\\"}
  | const_name (["Data","Bool"],"T") = {Thy="bool",Name="T"}
  | const_name (["Data","Bool"],"F") = {Thy="bool",Name="F"}
  | const_name (["Data","Bool"],"cond") = {Thy="bool",Name="COND"}
  | const_name (["HOL4","bool"],"TYPE_DEFINITION") = {Thy="bool",Name="TYPE_DEFINITION"}
  | const_name (["HOL4","bool"],"DATATYPE") = {Thy="bool",Name="DATATYPE"}
  | const_name (["HOL4","bool"],"literal_case") = {Thy="bool",Name="literal_case"}
  | const_name (["HOL4","bool"],"IN") = {Thy="bool",Name="IN"}
  | const_name (["Data","Bool"],"let") = {Thy="bool",Name="LET"}
  | const_name (["Data","Unit"],"()") = {Thy=Thy,Name="Data_Unit_unit"}
  | const_name (["Data","Pair"],",") = {Thy=Thy,Name="Data_Pair_comma"}
  | const_name (["Data","List"],"[]") = {Thy=Thy,Name="Data_List_nil"}
  | const_name (["Data","List"],"::") = {Thy=Thy,Name="Data_List_cons"}
  | const_name (["Data","List"],"@") = {Thy=Thy,Name="Data_List_append"}
  | const_name (["Data","List","case","[]"],"::") = {Thy=Thy,Name="Data_List_case"}
  | const_name (["Number","Natural"],"<") = {Thy=Thy,Name="Number_Natural_less"}
  | const_name (["Number","Natural"],">") = {Thy=Thy,Name="Number_Natural_greater"}
  | const_name (["Number","Natural"],"<=") = {Thy=Thy,Name="Number_Natural_lesseq"}
  | const_name (["Number","Natural"],">=") = {Thy=Thy,Name="Number_Natural_greatereq"}
  | const_name (["Number","Natural"],"*") = {Thy=Thy,Name="Number_Natural_times"}
  | const_name (["Number","Natural"],"+") = {Thy=Thy,Name="Number_Natural_plus"}
  | const_name (["Number","Natural"],"-") = {Thy=Thy,Name="Number_Natural_minus"}
  | const_name (["Number","Natural"],"^") = {Thy=Thy,Name="Number_Natural_power"}
  | const_name (["Number","Real"],"<=") = {Thy=Thy,Name="Number_Real_lesseq"}
  | const_name (["Number","Real"],"<") = {Thy=Thy,Name="Number_Real_less"}
  | const_name (["Number","Real"],">") = {Thy=Thy,Name="Number_Real_greater"}
  | const_name (["Number","Real"],">=") = {Thy=Thy,Name="Number_Real_greatereq"}
  | const_name (["Number","Real"],"+") = {Thy=Thy,Name="Number_Real_plus"}
  | const_name (["Number","Real"],"*") = {Thy=Thy,Name="Number_Real_times"}
  | const_name (["Number","Real"],"^") = {Thy=Thy,Name="Number_Real_power"}
  | const_name (["Number","Real"],"~") = {Thy=Thy,Name="Number_Real_negate"}
  | const_name (["Number","Real"],"-") = {Thy=Thy,Name="Number_Real_minus"}
  | const_name (["Number","Real"],"/") = {Thy=Thy,Name="Number_Real_divide"}
  | const_name (["Set"],"{}") = {Thy=Thy,Name="Set_empty"}
  | const_name (["Function"],"^") = {Thy=Thy,Name="Function_pow"}
  | const_name (ns,n) = {Thy=Thy,Name=String.concatWith "_"(ns@[n])}
fun tyop_name ([],"bool") = {Thy="min",Tyop="bool"}
  | tyop_name ([],"->") = {Thy="min",Tyop="fun"}
  | tyop_name ([],"ind") = {Thy="min",Tyop="ind"}
  | tyop_name (["Data","Pair"],"*") = {Thy=Thy,Tyop="Data_Pair_prod"}
  | tyop_name (["Data","Sum"],"+") = {Thy=Thy,Tyop="Data_Sum_sum"}
  | tyop_name (ns,n) = {Thy=Thy,Tyop=String.concatWith "_"(ns@[n])}

val defs = ref ([]:thm list)
fun add_def tm =
  let
    val th = mk_oracle_thm"def" ([],tm)
    val _ = defs := th::(!defs)
  in th end

fun define_const {Thy="bool",Name="~"} tm = add_def(``$~ = ^tm``)
  | define_const {Thy="bool",Name="!"} tm = add_def(``$! = ^tm``)
  | define_const {Thy="bool",Name="?"} tm = add_def(``$? = ^tm``)
  | define_const {Thy="bool",Name="?!"} tm = add_def(``$?! = ^tm``)
  | define_const {Thy="bool",Name="\\/"} tm = add_def(``$\/ = ^tm``)
  | define_const {Thy="bool",Name="/\\"} tm = add_def(``$/\ = ^tm``)
  | define_const {Thy="bool",Name="T"} tm = add_def(``T = ^tm``)
  | define_const {Thy="bool",Name="F"} tm = add_def(``F = ^tm``)
  | define_const {Thy="bool",Name="COND"} tm = add_def(``COND = ^tm``)
  | define_const {Thy="min",Name="==>"} tm = add_def(``$==> = ^tm``)
  | define_const x tm = define_const_in_thy (fn x => x) x tm

val (reader:reader) = {
  define_tyop = define_tyop_in_thy o fix_tyop,
  define_const = define_const,
  axiom = fn _ => mk_thm,
  const_name = const_name,
  tyop_name = tyop_name}

val base_thms = read_article "base-theorems.art" reader;

val _ = Net.itnet (fn th => (Thm.delete_proof th; K ())) base_thms ()

fun itpred P th acc = if P th then th::acc else acc
fun amatch tm = Net.itnet (itpred (DB.matches tm)) base_thms []

val _ = new_constant("unknown",alpha);

(* TODO: copied from Opentheory.sml *)
  fun uneta a t = BETA_CONV(mk_comb(mk_abs(a,t),a))
  fun fix_bij th =
  let
    val (a,eq) = dest_forall(concl th)
    val (l,r) = dest_eq eq
  in
    EXT (GEN a (TRANS (TRANS (uneta a l) (SPEC a th)) (SYM (uneta a r))))
  end
(* -- *)

local
  fun find_tyop {name={Tyop,...},...} =
    let
      val (ar,ra) = definition(Tyop^"_bij") |> CONJ_PAIR
    in
      {rep_abs = fix_bij ra,
       abs_rep = fix_bij ar}
    end
  fun find_const {Name,...} = definition(Name^"_def")
  handle HOL_ERR _ => first (equal Name o #1 o dest_const o lhs o concl) (!defs)
in
  val (reader:reader) = {
    define_tyop = fn x => find_tyop (fix_tyop x),
    define_const = fn x => fn _ => find_const x,
    axiom = fn _ => mk_thm,
    const_name = const_name,
    tyop_name = tyop_name}
end

val goalsNet = read_article "hol4-assums.art" reader;

val goals = Net.listItems goalsNet

val _ = Parse.hide"_"

val not_and = hd (amatch ``¬(t1 ∧ t2) ⇔ _``)
val not_not = hd (amatch ``¬(¬ _)``)
val bool_cases = hd (amatch ``t ∨ ¬ t``)
val disj_comm = hd (amatch ``_ ∨ _ ⇔ _ ∨ _``)
val th1 = store_thm("th1", el 1 goals |> concl, PURE_REWRITE_TAC[not_and,not_not,Once disj_comm,bool_cases])

val cons_11 = hd (amatch ``Data_List_cons  _ _ = Data_List_cons _ _``)
val th10 = store_thm("th10", el 10 goals |> concl, MATCH_ACCEPT_TAC cons_11)

val app_if = hd (amatch ``f (if b then x else y) = if b then f x else f y``)
val th11 = store_thm("th11", el 11 goals |> concl, MATCH_ACCEPT_TAC app_if)

val demorgan = hd (amatch``(b ∨ a) ∧ (c ∨ a)``)
val th12 = store_thm("th12", el 12 goals |> concl, MATCH_ACCEPT_TAC demorgan)

val or_assoc = hd (amatch``(a ∨ b) ∨ c``)
val th13 = store_thm("th13", el 13 goals |> concl, MATCH_ACCEPT_TAC (GSYM or_assoc))

val or_distrib_and = hd (amatch``(b ∨ c) ∧ a ⇔ _``)
val th14 = store_thm("th14", el 14 goals |> concl, MATCH_ACCEPT_TAC or_distrib_and)

val and_assoc = hd (amatch``(a ∧ b) ∧ c``)
val th15 = store_thm("th15", el 15 goals |> concl, MATCH_ACCEPT_TAC (GSYM and_assoc))

val if_T = hd (amatch ``if T then t1 else t2``)
val if_F = hd (amatch ``if F then t1 else t2``)
val th20 = store_thm("th20", el 20 goals |> concl,
  rpt gen_tac \\ MATCH_ACCEPT_TAC (CONJ (SPEC_ALL if_T) (SPEC_ALL if_F)))

val suc_11 =hd(amatch``Number_Natural_suc _ = Number_Natural_suc _``)
val th24 = store_thm("th24", el 24 goals |> concl,
  rpt gen_tac \\ MATCH_ACCEPT_TAC (#1 (EQ_IMP_RULE (SPEC_ALL suc_11))))

val forall_or = el 2 (amatch``_ ⇔ (∀x. P x) ∨ Q``)
val th25 = store_thm("th25", el 25 goals |> concl, MATCH_ACCEPT_TAC forall_or)

val null_eq = hd(amatch``Data_List_null t ⇔ (_ = Data_List_nil)``)
val last_cons = hd(amatch``Data_List_last (Data_List_cons h t) = COND _ _ _``)

val th26 = store_thm("th26", el 26 goals |> concl,
  MATCH_ACCEPT_TAC(PURE_REWRITE_RULE[null_eq]last_cons))

val ext = hd(amatch``(∀x. f x = g x) ⇔ _``)
val th30 = store_thm("th30", el 30 goals |> concl,
  MATCH_ACCEPT_TAC (GSYM ext))

val cons_neq_nil = hd(amatch``_ ≠ Data_List_nil``)
val th34 = store_thm("th34", el 34 goals |> concl, MATCH_ACCEPT_TAC (GSYM cons_neq_nil))

val some_neq_none = hd(amatch``_ ≠ Data_Option_none``)
val th35 = store_thm("th35", el 35 goals |> concl, MATCH_ACCEPT_TAC (GSYM some_neq_none))

val eq_T = hd(amatch``(t ⇔ T) ⇔ _``)
fun EQT_INTRO th = EQ_MP (SPEC (concl th) (GSYM eq_T)) th

val imp_T = hd(amatch``t ⇒ T``)
val T_imp = hd(amatch``T ⇒ t``)
val F_imp = hd(amatch``F ⇒ t``)
val imp_F = hd(amatch``t ⇒ F ⇔ _``)
val imp_i = hd(amatch``t ⇒ t``)
val th36 = store_thm("th36", el 36 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC imp_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL imp_i))
  \\ MATCH_ACCEPT_TAC imp_F);

val _ = List.app (Theory.delete_binding o #1) (axioms"-");
val _ = List.app (Theory.delete_binding o #1) (definitions"-");

val _ = export_theory()
