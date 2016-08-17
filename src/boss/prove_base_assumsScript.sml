open HolKernel boolLib Opentheory bossLib BasicProvers

val Thy = "prove_base_assums";

val _ = new_theory Thy;

val _ = new_constant("base-1.203",alpha);

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
  | const_name (["HOL4","bool"],"LET") = {Thy="bool",Name="LET"}
  | const_name (["HOL4","bool"],"IN") = {Thy="bool",Name="IN"}
  | const_name (["HOL4","bool"],"literal_case") = {Thy="bool",Name="literal_case"}
  | const_name (["HOL4","bool"],"TYPE_DEFINITION") = {Thy="bool",Name="TYPE_DEFINITION"}
  | const_name (["HOL4","bool"],"ARB") = {Thy="bool",Name="ARB"}
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

val _ = new_constant("hol-base-assums-1.0",alpha);

local
  fun find_tyop {name={Tyop,...},...} =
    let
      val (ar,ra) = definition(Tyop^"_bij") |> CONJ_PAIR
    in
      {rep_abs = uneta_type_bijection ra,
       abs_rep = uneta_type_bijection ar}
    end
  fun find_const {Name,...} = definition(Name^"_def")
  handle HOL_ERR _ => first (equal Name o #1 o dest_const o lhs o concl) (!defs)
                      handle HOL_ERR _ => raise(Fail Name)
in
  val (reader:reader) = {
    define_tyop = fn x => find_tyop (fix_tyop x),
    define_const = fn x => fn _ => find_const x,
    axiom = fn _ => mk_thm,
    const_name = const_name,
    tyop_name = tyop_name}
end

val LET_DEF = add_def(concl LET_DEF)
val IN_DEF = add_def(concl IN_DEF)
val literal_case_DEF = add_def(concl literal_case_DEF)
val TYPE_DEFINITION = add_def(concl TYPE_DEFINITION)
val ARB_DEF = add_def(concl (REFL``ARB``))

val goalsNet = read_article "hol4-assums.art" reader;

val goals = Net.listItems goalsNet

val _ = Parse.hide"_"

val bool_cases = hd (amatch ``t \/ ~t``)
val or_def = hd(amatch``$\/ = _``)

val imp_T = hd(amatch``t ==> T``)
val T_imp = hd(amatch``T ==> t``)
val F_imp = hd(amatch``F ==> t``)
val imp_F = hd(amatch``t ==> F <=> _``)
val imp_i = hd(amatch``t ==> t``)

val T_iff = hd(amatch``(T <=> t) <=> _``)
val iff_T = hd(amatch``(t <=> T) <=> _``)
val F_iff = hd(amatch``(F <=> t) <=> _``)
val iff_F = hd(amatch``(t <=> F) <=> _``)

val and_imp_intro = hd(amatch``(a ==> b ==> c) <=> _``)

val eq_T = hd(amatch``(t <=> T) <=> _``)
fun EQT_INTRO th = EQ_MP (SPEC (concl th) (GSYM eq_T)) th

val EQF_INTRO = SYM o (CONV_RULE(REWR_CONV(GSYM F_iff)))

val not_and = hd (amatch ``~(t1 /\ t2) <=> _``)
val not_not = hd (amatch ``~(~ _)``)
val disj_comm = hd (amatch ``_ \/ _ <=> _ \/ _``)

val T_or = hd(amatch``T \/ t``)
val or_T = hd(amatch``t \/ T``)
val F_or = hd(amatch``F \/ t``)
val or_F = hd(amatch``t \/ F``)
val or_i = hd(amatch``t \/ t``)

val truth = hd(amatch``T``);
val not_F = hd(amatch``~F``)

val bool_cases = hd(amatch``(x = T) \/ _``)

val th1 = store_thm("th1", el 1 goals |> concl,
  PURE_REWRITE_TAC[not_and,not_not]
  \\ Q.SPEC_THEN`t`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[or_T,or_F,not_F])

val ex_unique_thm = hd (amatch``(?!x. p x) <=> _ /\ _``)
val list_rec = hd(amatch``fn (Data_List_cons h t) = f h t (fn t)``)
val list_ind = hd(amatch``_ ==> !l:'a Data_List_list. P l``)
val fun_eq_thm = hd(amatch``(!x. f x = g x) <=> (f = g)``)
val th2 = store_thm("th2", el 2 goals |> concl,
  rpt gen_tac
  \\ CONV_TAC(HO_REWR_CONV ex_unique_thm)
  \\ conj_tac >- (
       Q.ISPECL_THEN[`x`,`\h t a. f a h t`]strip_assume_tac list_rec
       \\ qexists_tac`fn`
       \\ first_x_assum (fn th => conj_tac >- MATCH_ACCEPT_TAC th)
       \\ first_x_assum (MATCH_ACCEPT_TAC o BETA_RULE) )
  \\ rpt gen_tac \\ strip_tac
  \\ PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ ho_match_mp_tac list_ind
  \\ rpt VAR_EQ_TAC
  \\ conj_tac >- (first_assum MATCH_ACCEPT_TAC)
  \\ rpt strip_tac
  \\ rpt (last_x_assum(qspecl_then[`h`,`x`]mp_tac))
  \\ pop_assum SUBST_ALL_TAC
  \\ disch_then(SUBST_ALL_TAC o SYM)
  \\ disch_then (MATCH_ACCEPT_TAC));

val o_def = hd(amatch``Function_o = _``)

val sum_cases = hd(amatch``(?a. x = Data_Sum_left a) \/ _``)
val sum_ind = hd(amatch``_ ==> !l:('a,'b) Data_Sum_sum. P l``)

val sum_case_thms = amatch``Data_Sum_case_left_right f g (_ _) = _``

val th3 = store_thm("th3", el 3 goals |> concl,
  rpt gen_tac
  \\ CONV_TAC(HO_REWR_CONV ex_unique_thm)
  \\ PURE_REWRITE_TAC[o_def]
  \\ PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt strip_tac
  >- (
    qexists_tac`Data_Sum_case_left_right f g`
    \\ PURE_REWRITE_TAC sum_case_thms
    \\ PURE_REWRITE_TAC[fun_eq_thm]
    \\ conj_tac \\ REFL_TAC )
  \\ Q.ISPEC_THEN`x`FULL_STRUCT_CASES_TAC sum_cases
  >- (
    rpt(first_x_assum(qspec_then`a`SUBST_ALL_TAC))
    \\ REFL_TAC)
  \\ rpt(first_x_assum(qspec_then`b`SUBST_ALL_TAC))
  \\ REFL_TAC)

val if_T = hd(amatch``(if T then _ else _) = _``)
val if_F = hd(amatch``(if F then _ else _) = _``)

val th4 = store_thm("th4", el 4 goals |> concl,
  rpt gen_tac
  \\ rpt strip_tac
  \\ last_x_assum SUBST_ALL_TAC
  \\ Q.ISPEC_THEN`Q`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[if_T,if_F]
  \\ first_x_assum match_mp_tac
  \\ PURE_REWRITE_TAC[truth,not_F]);

val T_and = hd(amatch``T /\ t``)
val and_T = hd(amatch``t /\ T <=> _``)
val F_and = hd(amatch``F /\ t``)
val and_F = hd(amatch``t /\ F <=> _``)
val and_i = hd(amatch``t /\ t``)

val th5 = store_thm("th5", el 5 goals |> concl,
  rpt strip_tac
  \\ Q.ISPEC_THEN`Q`FULL_STRUCT_CASES_TAC bool_cases
  \\ Q.ISPEC_THEN`P'`FULL_STRUCT_CASES_TAC bool_cases
  \\ rpt (pop_assum mp_tac)
  \\ PURE_REWRITE_TAC[and_T,T_and,and_F,F_and,T_imp,F_imp,T_iff,iff_T,F_iff,iff_F,not_F]
  \\ TRY(disch_then MATCH_ACCEPT_TAC)
  \\ disch_then(SUBST_ALL_TAC o EQT_INTRO)
  \\ disch_then(SUBST_ALL_TAC o EQT_INTRO)
  \\ REFL_TAC);

val th6 = store_thm("th6", el 6 goals |> concl,
  rpt strip_tac
  \\ last_x_assum SUBST_ALL_TAC
  \\ Q.ISPEC_THEN`x'`FULL_STRUCT_CASES_TAC bool_cases
  \\ pop_assum mp_tac
  \\ PURE_REWRITE_TAC[T_imp,F_imp]
  \\ TRY REFL_TAC
  \\ disch_then ACCEPT_TAC);

val cons_11 = hd (amatch ``Data_List_cons  _ _ = Data_List_cons _ _``)
val th7 = store_thm("th7", el 7 goals |> concl, MATCH_ACCEPT_TAC cons_11)

val app_if = hd (amatch ``f (if b then x else y) = if b then f x else f y``)
val th8 = store_thm("th8", el 8 goals |> concl, MATCH_ACCEPT_TAC app_if)

val demorgan = hd (amatch``(b \/ a) /\ (c \/ a)``)
val th9 = store_thm("th9", el 9 goals |> concl, MATCH_ACCEPT_TAC demorgan)

val or_assoc = hd (amatch``(a \/ b) \/ c``)
val th10 = store_thm("th10", el 10 goals |> concl, MATCH_ACCEPT_TAC (GSYM or_assoc))

val or_distrib_and = hd (amatch``(b \/ c) /\ a <=> _``)
val th11 = store_thm("th11", el 11 goals |> concl, MATCH_ACCEPT_TAC or_distrib_and)

val and_assoc = hd (amatch``(a /\ b) /\ c``)
val th12 = store_thm("th12", el 12 goals |> concl, MATCH_ACCEPT_TAC (GSYM and_assoc))

val if_T = hd (amatch ``if T then t1 else t2``)
val if_F = hd (amatch ``if F then t1 else t2``)

val th13 = store_thm("th13", el 13 goals |> concl,
  rpt gen_tac
  \\ qexists_tac`\b. if b then t1 else t2`
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ PURE_REWRITE_TAC[if_T,if_F]
  \\ conj_tac \\ REFL_TAC);

val not_or = hd(amatch``~(_ \/ _)``)

val th14 = store_thm("th14", el 14 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[not_and,not_or]
  \\ conj_tac \\ REFL_TAC);

val and_ex = hd(amatch``p /\ (?x. _) <=> ?x. p /\ _``)
val ex_and = hd(amatch``(?x. _) /\ p <=> ?x. _ /\ p``)
val ex_imp = hd(amatch``((?x. _) ==> _) <=> _``)

val th15 = store_thm("th15", el 15 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[and_ex,ex_and,ex_imp]
  \\ rpt conj_tac \\ REFL_TAC);

val and_all = hd(amatch``p /\ (!x. _) <=> !x. p /\ _``)
val all_and = hd(amatch``(!x. _) /\ p <=> !x. _ /\ p``)
val all_imp = hd(amatch``((!x. _) ==> _) <=> _``)
val imp_all = hd(amatch``(_ ==> (!x. _)) <=> _``)

val th16 = store_thm("th16", el 16 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[and_all,all_and,all_imp,imp_all]
  \\ rpt conj_tac \\ REFL_TAC);

val th17 = store_thm("th17", el 17 goals |> concl,
  rpt gen_tac \\ MATCH_ACCEPT_TAC (CONJ (SPEC_ALL if_T) (SPEC_ALL if_F)))

val forall_eq = hd(amatch``!x. (x = t) ==> _``)
val forall_eq2 = hd(amatch``!x. (t = x) ==> _``)

val ex_def = hd(amatch``$? = _``)
val select_ax = hd(amatch ``p t ==> p ($@ p)``)

val th18 = store_thm("th18", el 18 goals |> concl,
  PURE_REWRITE_TAC[forall_eq,ex_def]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ MATCH_ACCEPT_TAC select_ax);

val eta_ax = hd(amatch``!f. (\x. f x) = f``)

val th19 = store_thm("th19", el 19 goals |> concl,
  PURE_REWRITE_TAC[ex_def]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV (GSYM eta_ax))))
  \\ first_x_assum ACCEPT_TAC);

val th20 = store_thm("th20", el 20 goals |> concl,
  rpt strip_tac
  \\ Q.ISPEC_THEN`t1`mp_tac bool_cases
  \\ PURE_REWRITE_TAC[or_def]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ disch_then(qspec_then`t1 = t2`mp_tac)
  \\ PURE_REWRITE_TAC[iff_T,iff_F,and_imp_intro]
  \\ disch_then match_mp_tac
  \\ conj_tac
  \\ TRY (disch_then(SUBST_ALL_TAC o EQF_INTRO))
  \\ TRY (disch_then(SUBST_ALL_TAC o EQT_INTRO))
  \\ rpt (pop_assum mp_tac)
  \\ PURE_REWRITE_TAC[T_imp,T_iff,imp_T,F_imp,F_iff,imp_F]
  \\ disch_then ACCEPT_TAC);

val suc_11 =hd(amatch``Number_Natural_suc _ = Number_Natural_suc _``)
val th21 = store_thm("th21", el 21 goals |> concl,
  rpt gen_tac \\ MATCH_ACCEPT_TAC (#1 (EQ_IMP_RULE (SPEC_ALL suc_11))))

val forall_or = el 2 (amatch``_ <=> (!x. P x) \/ Q``)
val th22 = store_thm("th22", el 22 goals |> concl, MATCH_ACCEPT_TAC forall_or)

val null_eq = hd(amatch``Data_List_null t <=> (_ = Data_List_nil)``)
val last_cons = hd(amatch``Data_List_last (Data_List_cons h t) = COND _ _ _``)

val th23 = store_thm("th23", el 23 goals |> concl,
  MATCH_ACCEPT_TAC(PURE_REWRITE_RULE[null_eq]last_cons))

val not_T = hd(amatch``~T``)

val th24 = store_thm("th24", el 24 goals |> concl,
  rpt gen_tac
  \\ Q.ISPEC_THEN`t1`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_and,not_T,F_and,or_F,not_F,F_or,F_iff]
  \\ REFL_TAC);

val th25 = store_thm("th25", el 25 goals |> concl,
  rpt gen_tac
  \\ Q.ISPEC_THEN`t1`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,F_iff,T_imp,F_imp,imp_T,imp_F,and_T,T_and]
  \\ REFL_TAC);

val ext = hd(amatch``(!x. f x = g x) <=> _``)
val th26 = store_thm("th26", el 26 goals |> concl,
  MATCH_ACCEPT_TAC (GSYM ext))

val th27 = store_thm("th27", el 27 goals |> concl,
  rpt gen_tac
  \\ Q.ISPEC_THEN`A`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,or_T,F_iff,or_F,imp_T,imp_F]
  \\ REFL_TAC);

val cons_neq_nil = hd(amatch``_ <> Data_List_nil``)
val th28 = store_thm("th28", el 28 goals |> concl, MATCH_ACCEPT_TAC (GSYM cons_neq_nil))

val some_neq_none = hd(amatch``_ <> Data_Option_none``)
val th29 = store_thm("th29", el 29 goals |> concl, MATCH_ACCEPT_TAC (GSYM some_neq_none))

val th30 = store_thm("th30", el 30 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC imp_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL imp_i))
  \\ MATCH_ACCEPT_TAC imp_F);

val th31 = store_thm("th31", el 31 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_or
  \\ conj_tac >- MATCH_ACCEPT_TAC or_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_or
  \\ conj_tac >- MATCH_ACCEPT_TAC or_F
  \\ MATCH_ACCEPT_TAC or_i);

val th32 = store_thm("th32", el 32 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_and
  \\ conj_tac >- MATCH_ACCEPT_TAC and_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_and
  \\ conj_tac >- MATCH_ACCEPT_TAC and_F
  \\ MATCH_ACCEPT_TAC and_i);

val th33 = store_thm("th33", el 33 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_iff
  \\ conj_tac >- MATCH_ACCEPT_TAC iff_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_iff
  \\ MATCH_ACCEPT_TAC iff_F);

val select_eq = hd(amatch``@y. y = x``)
val th34 = store_thm("th34", el 34 goals |> concl,
  CONV_TAC(QUANT_CONV(LAND_CONV(RAND_CONV(ABS_CONV SYM_CONV))))
  \\ MATCH_ACCEPT_TAC select_eq);

val th35 = store_thm("th35", el 35 goals |> concl,
  PURE_REWRITE_TAC[imp_F, iff_F]
  \\ gen_tac \\ REFL_TAC)

val refl = hd(amatch``!x. x = x``)
val th36 = store_thm("th36", el 36 goals |> concl,
  gen_tac \\ MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL refl)))

val eq_trans = hd(amatch``(x = y) /\ (y = z) ==> _``)

val th37 = store_thm("th37", el 37 goals |> concl,
  rpt strip_tac
  \\ first_assum(qspecl_then[`x`,`y`,`z`]SUBST_ALL_TAC)
  \\ last_assum(qspecl_then[`f x y`,`z`]SUBST_ALL_TAC)
  \\ first_assum(qspecl_then[`z`,`x`,`y`]SUBST_ALL_TAC)
  \\ last_assum(qspecl_then[`f z x`,`y`]SUBST_ALL_TAC)
  \\ AP_TERM_TAC
  \\ last_assum(qspecl_then[`z`,`x`]ACCEPT_TAC));

val less_zero = hd(amatch``Number_Natural_less Number_Natural_zero n <=> _ <> _``)
val div_mod = hd(amatch``Number_Natural_times (Number_Natural_div k n) n``)

val less_mod = hd(amatch``Number_Natural_less (Number_Natural_mod _ _)``)

val th38 = store_thm("th38", el 38 goals |> concl,
  PURE_REWRITE_TAC[less_zero]
  \\ gen_tac
  \\ disch_then(fn th => (strip_assume_tac (MATCH_MP less_mod th) >>
       (strip_assume_tac (MATCH_MP div_mod th))))
  \\ gen_tac
  \\ first_x_assum(qspec_then`k`SUBST_ALL_TAC)
  \\ conj_tac >- REFL_TAC
  \\ first_x_assum(qspec_then`k`ACCEPT_TAC));

val list_ind = hd(amatch``_ ==> !(l:'a Data_List_list). P l``)
val th39 = store_thm("th39", el 39 goals |> concl,
  rpt strip_tac
  \\ match_mp_tac list_ind
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rpt strip_tac \\ res_tac
  \\ first_assum MATCH_ACCEPT_TAC);

val th40 = store_thm("th40", el 40 goals |> concl,
  imp_F |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> MATCH_ACCEPT_TAC)

val th41 = store_thm("th41", el 41 goals |> concl,
  imp_F |> SPEC_ALL |> EQ_IMP_RULE |> #2 |> MATCH_ACCEPT_TAC)

val th42 = store_thm("th42", el 42 goals |> concl,
  PURE_REWRITE_TAC[GSYM imp_F]
  \\ gen_tac
  \\ disch_then(fn th => disch_then(ACCEPT_TAC o C MP th)));

val th43 = store_thm("th43", el 43 goals |> concl,
  MATCH_ACCEPT_TAC(EQT_ELIM(SPEC_ALL F_imp)))

val unpair = hd(amatch``Data_Pair_comma (Data_Pair_fst _) _``)

val unzip_nil = hd(amatch``Data_List_unzip Data_List_nil``)
val unzip_cons = hd(amatch``Data_List_unzip (Data_List_cons _ _)``)
val th44 = store_thm("th44", el 44 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC unzip_nil
  \\ PURE_REWRITE_TAC[unzip_cons]
  \\ rpt gen_tac
  \\ conj_tac
  \\ MATCH_ACCEPT_TAC(GSYM unpair));

val reverse_nil = hd(amatch``Data_List_reverse Data_List_nil``)
val reverse_cons = hd(amatch``Data_List_reverse (Data_List_cons _ _)``)
val th45 = store_thm("th45", el 45 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC reverse_nil
  \\ MATCH_ACCEPT_TAC reverse_cons);

val concat_nil = hd(amatch``Data_List_concat Data_List_nil``)
val concat_cons = hd(amatch``Data_List_concat (Data_List_cons _ _)``)
val th46 = store_thm("th46", el 46 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC concat_nil
  \\ MATCH_ACCEPT_TAC concat_cons);

val fact_zero = hd(amatch``Number_Natural_factorial Number_Natural_zero``)
val fact_suc = hd(amatch``Number_Natural_factorial (Number_Natural_suc _)``)

val th47 = store_thm("th47", el 47 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC fact_zero
  \\ MATCH_ACCEPT_TAC fact_suc);

val length_nil = hd(amatch``Data_List_length Data_List_nil``)
val length_cons = hd(amatch``Data_List_length (Data_List_cons _ _)``)
val th48 = store_thm("th48", el 48 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC length_nil
  \\ MATCH_ACCEPT_TAC length_cons);

fun EQT_ELIM th = EQ_MP (SYM th) truth

fun EQF_ELIM th =
   let
      val (lhs, rhs) = dest_eq (concl th)
      val _ = assert (equal boolSyntax.F) rhs
   in
      NOT_INTRO (DISCH lhs (EQ_MP th (ASSUME lhs)))
   end

val null_nil = hd(amatch``Data_List_null Data_List_nil``)
val null_cons = hd(amatch``Data_List_null (Data_List_cons _ _)``)

val th49 = store_thm("th49", el 49 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO null_nil)
  \\ MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL null_cons)));

val odd_nil = hd(amatch``Number_Natural_odd Number_Natural_zero``)
val odd_cons = hd(amatch``Number_Natural_odd (Number_Natural_suc _)``)

val th50 = store_thm("th50", el 50 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO odd_nil)
  \\ MATCH_ACCEPT_TAC odd_cons);

val even_nil = hd(amatch``Number_Natural_even Number_Natural_zero``)
val even_cons = hd(amatch``Number_Natural_even (Number_Natural_suc _)``)

val th51 = store_thm("th51", el 51 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO even_nil)
  \\ MATCH_ACCEPT_TAC even_cons);

val map_none = hd(amatch``Data_Option_map _ Data_Option_none = _``)
val map_some = hd(amatch``Data_Option_map _ (Data_Option_some _) = _``)

val th52 = store_thm("th52", el 52 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC map_some
  \\ MATCH_ACCEPT_TAC map_none);

val filter_nil = hd(amatch``Data_List_filter _ Data_List_nil``)
val filter_cons = hd(amatch``Data_List_filter _ (Data_List_cons _ _)``)

val th53 = store_thm("th53", el 53 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC filter_nil
  \\ MATCH_ACCEPT_TAC filter_cons);

val any_nil = hd(amatch``Data_List_any _ Data_List_nil``)
val any_cons = hd(amatch``Data_List_any _ (Data_List_cons _ _)``)

val th54 = store_thm("th54", el 54 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL any_nil))
  \\ MATCH_ACCEPT_TAC any_cons)

val all_nil = hd(amatch``Data_List_all _ Data_List_nil``)
val all_cons = hd(amatch``Data_List_all _ (Data_List_cons _ _)``)

val th55 = store_thm("th55", el 55 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL all_nil))
  \\ MATCH_ACCEPT_TAC all_cons)

val map_nil = hd(amatch``Data_List_map _ Data_List_nil``)
val map_cons = hd(amatch``Data_List_map _ (Data_List_cons _ _)``)

val th56 = store_thm("th56", el 56 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC map_nil
  \\ MATCH_ACCEPT_TAC map_cons)

val append_nil = hd(amatch``Data_List_append Data_List_nil``)
val append_cons = hd(amatch``Data_List_append (Data_List_cons _ _) _ = Data_List_cons _ (_ _ _)``)

val th57 = store_thm("th57", el 57 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC append_nil
  \\ MATCH_ACCEPT_TAC append_cons)

val power_zero = hd(amatch``Number_Natural_power _ Number_Natural_zero``)
val power_suc = hd(amatch``Number_Natural_power _ (Number_Natural_suc _)``)

val th58  = store_thm("th58", el 58 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC power_zero
  \\ MATCH_ACCEPT_TAC power_suc)

val times_comm = hd(amatch``Number_Natural_times x y = Number_Natural_times y x``)
val plus_comm = hd(amatch``Number_Natural_plus x y = Number_Natural_plus y x``)
val times_zero = hd(amatch``Number_Natural_times _ Number_Natural_zero``)
val times_suc = hd(amatch``Number_Natural_times _ (Number_Natural_suc _)``)
val times_zero_comm = PURE_ONCE_REWRITE_RULE[times_comm]times_zero

val th59  = store_thm("th59", el 59 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC times_zero_comm
  \\ MATCH_ACCEPT_TAC
      (PURE_ONCE_REWRITE_RULE[plus_comm](PURE_ONCE_REWRITE_RULE[times_comm]times_suc)))

val plus_zero = hd(amatch``Number_Natural_plus _ Number_Natural_zero``)
val plus_suc = hd(amatch``Number_Natural_plus _ (Number_Natural_suc _)``)

val th60  = store_thm("th60", el 60 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[plus_comm]plus_zero)
  \\ MATCH_ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[plus_comm]plus_suc))

val th61 = store_thm("th61", el 61 goals |> concl,
  PURE_REWRITE_TAC[not_not,iff_F,iff_T,truth,not_F,and_T]
  \\ gen_tac \\ REFL_TAC)

val isSome_some = hd(amatch``Data_Option_isSome (Data_Option_some _)``)
val isSome_none = hd(amatch``Data_Option_isSome (Data_Option_none)``)

val th62 = store_thm("th62", el 62 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL isSome_some))
  \\ MATCH_ACCEPT_TAC (EQF_INTRO isSome_none))

val isNone_some = hd(amatch``Data_Option_isNone (Data_Option_some _)``)
val isNone_none = hd(amatch``Data_Option_isNone (Data_Option_none)``)

val th63 = store_thm("th63", el 63 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL isNone_some))
  \\ MATCH_ACCEPT_TAC (EQT_INTRO isNone_none))

val isRight_right = hd(amatch``Data_Sum_isRight (Data_Sum_right _)``)
val isRight_left = hd(amatch``Data_Sum_isRight (Data_Sum_left _)``)

val th64 = store_thm("th64", el 64 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC isRight_right
  \\ MATCH_ACCEPT_TAC isRight_left)

val isLeft_right = hd(amatch``Data_Sum_isLeft (Data_Sum_right _)``)
val isLeft_left = hd(amatch``Data_Sum_isLeft (Data_Sum_left _)``)

val th65 = store_thm("th65", el 65 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC isLeft_left
  \\ MATCH_ACCEPT_TAC isLeft_right)

val th66 = store_thm("th66", el 66 goals |> concl,
  rpt strip_tac
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ qexists_tac`x`
  \\ first_assum ACCEPT_TAC);

val th67 = store_thm("th67", el 67 goals |> concl,
  rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ first_x_assum(qspec_then`x`ACCEPT_TAC));

val th68 = store_thm("th68", el 68 goals |> concl,
  rpt strip_tac
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ TRY (disj1_tac >> first_assum ACCEPT_TAC)
  \\ TRY (disj2_tac >> first_assum ACCEPT_TAC))

val th69 = store_thm("th69", el 69 goals |> concl,
   rpt strip_tac
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ first_assum ACCEPT_TAC);

val th70 = store_thm("th70", el 70 goals |> concl,
  PURE_REWRITE_TAC[imp_F]
  \\ disch_then ACCEPT_TAC)

val th71 = store_thm("th71", el 71 goals |> concl,
  PURE_REWRITE_TAC[not_or]
  \\ strip_tac)

val th72 = store_thm("th72", el 72 goals |> concl,
  PURE_REWRITE_TAC[not_or]
  \\ strip_tac)

val not_imp = hd(amatch``~(_ ==> _)``)

val th73 = store_thm("th73", el 73 goals |> concl,
  PURE_REWRITE_TAC[not_imp]
  \\ strip_tac)

val th74 = store_thm("th74", el 74 goals |> concl,
  PURE_REWRITE_TAC[not_imp]
  \\ strip_tac)

val th75 = store_thm("th75", el 75 goals |> concl,
  PURE_REWRITE_TAC[not_not]
  \\ strip_tac)

val tc_def = hd(amatch``!x. Relation_transitiveClosure x = _``)

val bigIntersect_thm = hd(amatch``Relation_bigIntersect a b c <=> _``)

val mem_fromPred = hd(amatch``Set_member r (Set_fromPredicate _)``)

val subrelation_thm = hd(amatch``Relation_subrelation x s <=> !x y. _``)

val transitive_thm = hd(amatch``Relation_transitive s <=> _``)

val th76 = store_thm("th76", el 76 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ PURE_REWRITE_TAC[tc_def,bigIntersect_thm,mem_fromPred]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ Ho_Rewrite.PURE_REWRITE_TAC[ex_imp]
  \\ PURE_REWRITE_TAC[subrelation_thm,transitive_thm]
  \\ PURE_ONCE_REWRITE_TAC[GSYM and_imp_intro]
  \\ Ho_Rewrite.PURE_REWRITE_TAC[forall_eq2]
  \\ rpt gen_tac
  \\ PURE_REWRITE_TAC[GSYM and_imp_intro]
  \\ REFL_TAC)

val wellFounded_thm = hd(amatch``Relation_wellFounded r <=> !p. (?x. _) ==> _``)

val th77 = store_thm("th77", el 77 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ PURE_REWRITE_TAC[wellFounded_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ gen_tac \\ REFL_TAC)

val less_thm = hd(amatch``Number_Natural_less _ _ <=> ?x. _``)
val less_refl = hd(amatch``Number_Natural_less x x``)
val less_zero = hd(amatch``~(Number_Natural_less _ (Number_Natural_zero))``)
val less_suc_suc = hd(amatch``Number_Natural_less (Number_Natural_suc _) b``)

val less_suc = hd(amatch``Number_Natural_less n (Number_Natural_suc n)``)
val less_trans = hd(amatch``Number_Natural_less x y /\ Number_Natural_less y z ==> _``)

val num_cases = hd(amatch``(n = Number_Natural_zero) \/ ?n. _``)

val num_ind = hd(amatch``_ ==> !n. P (n:Number_Natural_natural)``)

val num_less_ind = hd(amatch``(!x. _ ==> _) ==> !n. P (n:Number_Natural_natural)``)

val not_less = hd(amatch``~(Number_Natural_less _ _) <=> _``)

val less_lesseq = hd(amatch``Number_Natural_less m (Number_Natural_suc n) <=>  Number_Natural_lesseq m n``)

val less_or_eq = hd(amatch``Number_Natural_lesseq _ _ <=> (Number_Natural_less _ _) \/ _``)

val trichotomy = hd(amatch``_ \/ _ \/ (_ = _)``)

val th78 = store_thm("th78", el 78 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ qx_genl_tac[`a`,`b`]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ match_mp_tac (PURE_REWRITE_RULE[and_imp_intro]th20)
  \\ conj_tac \\ strip_tac
  >- (
    qexists_tac`\x. Number_Natural_less x b`
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
    \\ reverse conj_tac
    >- (
      conj_tac >- (first_assum ACCEPT_TAC)
      \\ MATCH_ACCEPT_TAC less_refl )
    \\ gen_tac
    \\ Q.ISPEC_THEN`b`FULL_STRUCT_CASES_TAC num_cases
    >- (
      PURE_REWRITE_TAC[EQF_INTRO (SPEC_ALL less_zero)]
      \\ disch_then ACCEPT_TAC)
    \\ PURE_REWRITE_TAC[less_suc_suc]
    \\ strip_tac
    \\ match_mp_tac less_trans
    \\ qexists_tac`n'`
    \\ conj_tac >- (first_assum ACCEPT_TAC)
    \\ MATCH_ACCEPT_TAC less_suc )
  \\ `!n. Number_Natural_less n a ==> P n`
  by (
    qpat_x_assum`P a`mp_tac
    \\ qid_spec_tac`a`
    \\ ho_match_mp_tac num_ind
    \\ conj_tac
    >- (
      PURE_REWRITE_TAC[EQF_INTRO (SPEC_ALL less_zero)]
      \\ ntac 2 strip_tac
      \\ CONV_TAC(REWR_CONV F_imp))
    \\ rpt strip_tac
    \\ `P a` by (first_x_assum(fn th => (first_x_assum match_mp_tac \\ first_assum ACCEPT_TAC)))
    \\ `!n. Number_Natural_less n a ==> P n` by (first_x_assum match_mp_tac \\ first_assum ACCEPT_TAC)
    \\ first_x_assum(assume_tac o CONV_RULE(REWR_CONV less_lesseq))
    \\ first_x_assum(strip_assume_tac o CONV_RULE(REWR_CONV less_or_eq))
    >- (
      first_x_assum match_mp_tac
      \\ first_assum ACCEPT_TAC)
    \\ VAR_EQ_TAC
    \\ first_assum ACCEPT_TAC )
  \\ qspecl_then[`a`,`b`]strip_assume_tac trichotomy
  >- (
    qspec_then`Number_Natural_less a b`(match_mp_tac o EQT_ELIM) F_imp
    \\ qspec_then`~(P b)`(match_mp_tac o UNDISCH) th42
    \\ PURE_REWRITE_TAC[not_not]
    \\ first_x_assum match_mp_tac
    \\ first_assum ACCEPT_TAC )
  \\ VAR_EQ_TAC
  \\ first_x_assum(assume_tac o EQF_INTRO)
  \\ first_x_assum(fn th => (first_x_assum(mp_tac o EQ_MP th)))
  \\ PURE_REWRITE_TAC[F_imp])

val th79 = store_thm("th79", el 79 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,transitive_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ gen_tac \\ REFL_TAC)

val th80 = store_thm("th80", el 80 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,subrelation_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val union_thm = hd(amatch``Relation_union r s = _``)
val fromSet_thm = hd(amatch``Relation_fromSet _ _ _``)
val mem_union = hd(amatch``Set_member _ (Set_union _ _) <=> _``)
val mem_toSet = hd(amatch``Set_member _ (Relation_toSet _)``)

val th81 = store_thm("th81", el 81 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,union_thm,fromSet_thm,mem_union,mem_toSet]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val intersect_thm = hd(amatch``Relation_intersect x y = _``)

val mem_inter = hd(amatch``Set_member _ (Set_intersect _ _)``)

val th82 = store_thm("th82", el 82 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,intersect_thm,fromSet_thm,mem_inter,mem_toSet]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val greatereq_thm = hd(amatch``Number_Natural_greatereq _ _``)
val greater_thm = hd(amatch``Number_Natural_greater _ _ = _``)

val th83 = store_thm("th83", el 83 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,greatereq_thm,less_or_eq,greater_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
  \\ REFL_TAC)

val th84 = store_thm("th84", el 84 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,less_or_eq]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val th85 = store_thm("th85", el 85 goals |> concl,
  MATCH_ACCEPT_TAC ex_unique_thm)

val th86 = store_thm("th86", el 86 goals |> concl,
  Q.ISPEC_THEN`A`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[not_or,imp_F,not_and,not_not,T_or,not_T,F_imp,F_or,T_imp]
  \\ REFL_TAC)

val th87 = store_thm("th87", el 87 goals |> concl,
  Q.ISPEC_THEN`A`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[not_or,imp_F,not_and,not_not,T_or,not_T,F_imp,F_or,T_imp,not_F]
  \\ REFL_TAC)

val th88 = store_thm("th88", el 88 goals |> concl,
  Q.ISPEC_THEN`q`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[if_T,T_or,not_T,or_T,or_F,T_and,F_or,and_T]
  \\ Q.ISPEC_THEN`p`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_or,not_T,or_F,T_and,F_iff,F_or,not_F,if_F,or_T,and_T]
  \\ TRY REFL_TAC
  \\ Q.ISPEC_THEN`r`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[not_T,F_or,F_and,not_F,T_or,T_and,and_T,and_i]
  \\ REFL_TAC)

val th89 = store_thm("th89", el 89 goals |> concl,
  Q.ISPEC_THEN`p`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_or,not_T,or_F,T_and,F_iff,F_or,not_F,or_T,and_T]
  \\ Q.ISPEC_THEN`q`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_or,not_T,or_F,T_and,F_iff,F_or,not_F,or_T,and_T,not_not]
  \\ REFL_TAC)

val th90 = store_thm("th90", el 90 goals |> concl,
  Q.ISPEC_THEN`p`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_or,not_T,or_F,T_and,F_iff,F_or,not_F,or_T,and_T,not_and]
  \\ REFL_TAC)

val th91 = store_thm("th91", el 91 goals |> concl,
  Q.ISPEC_THEN`p`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_or,not_T,or_F,T_and,F_iff,F_or,not_F,or_T,and_T,not_and,not_or]
  \\ REFL_TAC)

val th92 = store_thm("th92", el 92 goals |> concl,
  Q.ISPEC_THEN`p`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_or,not_T,or_F,T_and,F_iff,F_or,not_F,or_T,and_T,not_imp]
  \\ TRY REFL_TAC
  \\ Q.ISPEC_THEN`q`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_imp,not_T,F_imp,not_F,F_or,T_or]
  \\ REFL_TAC)

val th93 = store_thm("th93", el 93 goals |> concl,
  Q.ISPEC_THEN`p`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,T_or,not_T,or_F,T_and,F_iff,F_or,not_F,or_T,and_T,not_not]
  \\ REFL_TAC)

val comma_11 = hd(amatch``Data_Pair_comma _ _ = Data_Pair_comma _ _``)

val th94 = store_thm("th94", el 94 goals |> concl,
  MATCH_ACCEPT_TAC comma_11)

val right_11 = hd(amatch``Data_Sum_right _ = Data_Sum_right _``)

val th95 = store_thm("th95", el 95 goals |> concl,
  MATCH_ACCEPT_TAC right_11)

val left_11 = hd(amatch``Data_Sum_left _ = Data_Sum_left _``)

val th96 = store_thm("th96", el 96 goals |> concl,
  MATCH_ACCEPT_TAC left_11)

val min_thm = hd(amatch``Number_Natural_min _ _ = COND _ _ _``)

val if_id = hd(amatch``if _ then x else x``)

val th97 = store_thm("th97", el 97 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,min_thm,less_or_eq]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ qspec_then`x = x'`strip_assume_tac bool_cases
  \\ first_assum SUBST1_TAC
  \\ PURE_REWRITE_TAC[or_F,or_T,if_T]
  \\ TRY REFL_TAC
  \\ pop_assum(SUBST1_TAC o EQT_ELIM)
  \\ PURE_REWRITE_TAC[if_id]
  \\ REFL_TAC)

val max_thm = hd(amatch``Number_Natural_max _ _ = COND _ _ _``)

val th98 = store_thm("th98", el 98 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,max_thm,less_or_eq]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ qspec_then`x = x'`strip_assume_tac bool_cases
  \\ first_assum SUBST1_TAC
  \\ PURE_REWRITE_TAC[or_F,or_T,if_T]
  \\ TRY REFL_TAC
  \\ pop_assum(SUBST1_TAC o EQT_ELIM)
  \\ PURE_REWRITE_TAC[if_id]
  \\ REFL_TAC)

val bit1_thm = hd(amatch``Number_Natural_bit1 _ = _``)
val bit0_suc = hd(amatch``Number_Natural_bit0 _ = _ _``)
val bit0_zero = hd(amatch``Number_Natural_bit0 Number_Natural_zero``)
val plus_zero = hd(amatch``Number_Natural_plus Number_Natural_zero _``)
val plus_suc = hd(amatch``Number_Natural_plus _ (Number_Natural_suc _)``)
val plus_suc1 = hd(amatch``Number_Natural_plus (Number_Natural_suc _) _``)

val th99 = store_thm("th99", el 99 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,bit1_thm,plus_suc]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ gen_tac
  \\ AP_TERM_TAC
  \\ qid_spec_tac`x`
  \\ ho_match_mp_tac num_ind
  \\ PURE_REWRITE_TAC[bit0_zero,bit0_suc,plus_zero,plus_suc1]
  \\ conj_tac >- REFL_TAC
  \\ gen_tac
  \\ disch_then SUBST_ALL_TAC
  \\ PURE_REWRITE_TAC[plus_suc]
  \\ REFL_TAC)

val irreflexive_thm = hd(amatch``Relation_irreflexive _ = _``)

val th100 = store_thm("th100", el 100 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm, irreflexive_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ REFL_TAC)

val reflexive_thm = hd(amatch``Relation_reflexive _ = _``)

val th101 = store_thm("th101", el 101 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm, reflexive_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val o_thm = hd(amatch``(Function_o _ _) _ = _``)

val th102 = store_thm("th102", el 102 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,o_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val th103 = store_thm("th103", el 103 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,greater_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val skk = hd(amatch``Function_Combinator_s _ _ = Function_id``)

val th104 = store_thm("th104", el 104 goals |> concl,
  PURE_REWRITE_TAC[skk] \\ REFL_TAC)

val one_thm = hd(amatch``_ = Data_Unit_unit``)

val th105 = store_thm("th105", el 105 goals |> concl,
  PURE_ONCE_REWRITE_TAC[one_thm] \\ REFL_TAC)

val universe_thm = hd(amatch``Relation_universe _ _``)

val th106 = store_thm("th106", el 106 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,EQT_INTRO(SPEC_ALL universe_thm)]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val empty_thm = hd(amatch``Relation_empty _ _``)

val th107 = store_thm("th107", el 107 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,EQF_INTRO (SPEC_ALL empty_thm)]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC)

val th108 = store_thm("th108", el 108 goals |> concl,
  REFL_TAC)

(* other theorems from boolTheory *)

val MONO_IMP = store_thm("MONO_IMP", concl boolTheory.MONO_IMP,
  rpt strip_tac
  \\ rpt(first_x_assum match_mp_tac)
  \\ first_x_assum ACCEPT_TAC);

val IMP_DISJ_THM = store_thm("IMP_DISJ_THM", concl boolTheory.IMP_DISJ_THM,
  rpt gen_tac
  \\ qspec_then`A`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_imp,not_T,F_imp,not_F,F_or,T_or]
  \\ REFL_TAC)

val LET_CONG = store_thm("LET_CONG", concl boolTheory.LET_CONG,
  rpt strip_tac
  \\ VAR_EQ_TAC
  \\ PURE_REWRITE_TAC[LET_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ first_x_assum match_mp_tac
  \\ REFL_TAC)

val LET_RAND = store_thm("LET_RAND", concl boolTheory.LET_RAND,
  PURE_REWRITE_TAC[LET_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ REFL_TAC)

val BOOL_EQ_DISTINCT = store_thm("BOOL_EQ_DISTINCT", concl boolTheory.BOOL_EQ_DISTINCT,
  PURE_REWRITE_TAC[iff_F,not_not,iff_T,not_F,and_T]);

val bool_case_thm = store_thm("bool_case_thm", concl boolTheory.bool_case_thm,
  PURE_REWRITE_TAC[th17]
  \\ conj_tac \\ rpt gen_tac \\ REFL_TAC);

val forall_bool = hd(amatch``(!b:bool. P b) <=> _``)
val FORALL_BOOL = store_thm("FORALL_BOOL", concl boolTheory.FORALL_BOOL,
  MATCH_ACCEPT_TAC forall_bool);

val exists_refl = hd(amatch ``?x. x = a``)

val itself_tydef = prim_type_definition({Thy="prove_base_assums",Tyop="itself"},
  SPEC boolSyntax.arb exists_refl |> CONV_RULE(QUANT_CONV SYM_CONV))

val _ = Parse.hide"the_value"
val the_value_def = new_definition("the_value_def",``the_value = (ARB:'a itself)``)

val itself_unique = Q.store_thm("itself_unique",
  `!i. i = the_value`,
  CHOOSE_TAC itself_tydef
  \\ pop_assum mp_tac
  \\ PURE_REWRITE_TAC[TYPE_DEFINITION]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ strip_tac
  \\ gen_tac
  \\ first_assum(qspec_then`rep the_value`(mp_tac o #2 o EQ_IMP_RULE))
  \\ impl_tac >- (qexists_tac`the_value` \\ REFL_TAC)
  \\ first_assum(qspec_then`rep i`(mp_tac o #2 o EQ_IMP_RULE))
  \\ impl_tac >- (qexists_tac`i` \\ REFL_TAC)
  \\ disch_then(fn th => PURE_REWRITE_TAC[th])
  \\ first_x_assum MATCH_ACCEPT_TAC);

val itself_induction = store_thm("itself_induction",
  ``!P. P the_value ==> !i. P i``,
  rpt strip_tac
  \\ PURE_ONCE_REWRITE_TAC[itself_unique]
  \\ first_assum ACCEPT_TAC);

val itself_Axiom = store_thm("itself_Axiom", ``!e. ?f. f the_value = e``,
  gen_tac
  \\ qexists_tac`\x. e`
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ REFL_TAC);

val RES_FORALL_DEF = new_definition("RES_FORALL_DEF",concl boolTheory.RES_FORALL_DEF);
val RES_EXISTS_DEF = new_definition("RES_EXISTS_DEF",concl boolTheory.RES_EXISTS_DEF);
val RES_EXISTS_UNIQUE_DEF = new_definition("RES_EXISTS_UNIQUE_DEF",
  concl boolTheory.RES_EXISTS_UNIQUE_DEF
  |> Term.subst [boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF),
                 boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]);
val RES_SELECT_DEF = new_definition("RES_SELECT_DEF",concl boolTheory.RES_SELECT_DEF);

val RES_FORALL_THM = store_thm("RES_FORALL_THM",
  Term.subst [boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]
    (concl RES_FORALL_THM),
  PURE_REWRITE_TAC[RES_FORALL_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val RES_EXISTS_THM = store_thm("RES_EXISTS_THM",
  Term.subst [boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF)]
    (concl RES_EXISTS_THM),
  PURE_REWRITE_TAC[RES_EXISTS_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val RES_SELECT_THM = store_thm("RES_SELECT_THM",
  Term.subst [boolSyntax.res_select_tm |-> lhs(concl RES_SELECT_DEF)]
    (concl RES_SELECT_THM),
  PURE_REWRITE_TAC[RES_SELECT_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val RES_FORALL_CONG = store_thm("RES_FORALL_CONG",
  Term.subst [boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]
    (concl RES_FORALL_CONG),
  disch_then SUBST_ALL_TAC
  \\ PURE_REWRITE_TAC[RES_FORALL_THM]
  \\ strip_tac
  \\ PURE_REWRITE_TAC[th25]
  \\ conj_tac \\ rpt strip_tac
  \\ rpt (first_x_assum(qspec_then`x`mp_tac))
  \\ PURE_ASM_REWRITE_TAC[T_imp]
  \\ disch_then SUBST_ALL_TAC
  \\ disch_then ACCEPT_TAC);

val RES_EXISTS_CONG = store_thm("RES_EXISTS_CONG",
  Term.subst [boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF)]
    (concl RES_EXISTS_CONG),
  disch_then SUBST_ALL_TAC
  \\ PURE_REWRITE_TAC[RES_EXISTS_THM]
  \\ strip_tac
  \\ PURE_REWRITE_TAC[th25]
  \\ conj_tac \\ rpt strip_tac
  \\ qexists_tac`x`
  \\ rpt (first_x_assum(qspec_then`x`mp_tac))
  \\ PURE_ASM_REWRITE_TAC[T_imp,T_and,iff_T,T_iff]
  \\ disch_then ACCEPT_TAC);

val RES_EXISTS_UNIQUE_THM = store_thm("RES_EXISTS_UNIQUE_THM",
  Term.subst [boolSyntax.res_exists1_tm |-> lhs(concl RES_EXISTS_UNIQUE_DEF),
              boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF),
              boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]
    (concl RES_EXISTS_UNIQUE_THM),
  PURE_REWRITE_TAC[RES_EXISTS_UNIQUE_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val RES_ABSTRACT_EXISTS = prove(
  let
    val fvar = mk_var("f",type_of boolSyntax.res_abstract_tm)
  in
    mk_exists(fvar, Term.subst [boolSyntax.res_abstract_tm|->fvar] (concl RES_ABSTRACT_DEF))
  end,
  qexists_tac`\p m x. if x IN p then m x else ARB x`
  \\ PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ disch_then (SUBST_ALL_TAC o EQT_INTRO)
    \\ PURE_REWRITE_TAC[if_T]
    \\ REFL_TAC)
  \\ rpt gen_tac \\ strip_tac \\ gen_tac
  \\ first_x_assum(qspec_then`x`mp_tac)
  \\ Q.SPEC_THEN`x IN p`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[if_T,if_F,T_imp]
  >- disch_then ACCEPT_TAC
  \\ disch_then kall_tac
  \\ REFL_TAC);

val _ = List.app (Theory.delete_binding o #1) (axioms"-");
val _ = List.app (Theory.delete_binding o #1) (definitions"-");

val RES_ABSTRACT_DEF = new_specification("RES_ABSTRACT_DEF",["RES_ABSTRACT"],RES_ABSTRACT_EXISTS)

val _ = export_theory()
