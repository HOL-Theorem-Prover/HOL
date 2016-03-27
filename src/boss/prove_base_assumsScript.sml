open HolKernel boolLib Opentheory lcsymtacs

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
  | const_name (["Data","Bool"],"arb") = {Thy="bool",Name="ARB"}
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
  | define_const {Thy="bool",Name="LET"} tm = add_def(``LET = ^tm``)
  | define_const {Thy="bool",Name="ARB"} tm = add_def(``ARB = ^tm``)
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

(* 2, 3, 4 are TYPE_DEFINITION *)

val ex_unique_thm = hd (amatch``(?!x. p x) ⇔ _ ∧ _``)
val list_rec = hd(amatch``fn (Data_List_cons h t) = f h t (fn t)``)
val list_ind = hd(amatch``_ ⇒ ∀l:'a Data_List_list. P l``)
val eta_ax = hd(amatch``(∀x. f x = g x) ⇔ (f = g)``)
val th5 = store_thm("th5", el 5 goals |> concl,
  rpt gen_tac
  \\ CONV_TAC(HO_REWR_CONV ex_unique_thm)
  \\ conj_tac >- (
       Q.ISPECL_THEN[`x`,`λh t a. f a h t`]strip_assume_tac list_rec
       \\ qexists_tac`fn`
       \\ first_x_assum (fn th => conj_tac >- MATCH_ACCEPT_TAC th)
       \\ first_x_assum (MATCH_ACCEPT_TAC o BETA_RULE) )
  \\ rpt gen_tac \\ strip_tac
  \\ PURE_REWRITE_TAC[GSYM eta_ax]
  \\ ho_match_mp_tac list_ind
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ conj_tac >- (first_assum MATCH_ACCEPT_TAC)
  \\ rpt strip_tac
  \\ rpt (last_x_assum(qspecl_then[`h`,`x`]mp_tac))
  \\ pop_assum SUBST_ALL_TAC
  \\ disch_then(SUBST_ALL_TAC o SYM)
  \\ disch_then (MATCH_ACCEPT_TAC));

val o_def = hd(amatch``Function_o = _``)

val sum_cases = hd(amatch``(∃a. x = Data_Sum_left a) ∨ _``)
val sum_ind = hd(amatch``_ ⇒ ∀l:('a,'b) Data_Sum_sum. P l``)

val sum_case_thms = amatch``Data_Sum_case_left_right f g (_ _) = _``

val th6 = store_thm("th6", el 6 goals |> concl,
  rpt gen_tac
  \\ CONV_TAC(HO_REWR_CONV ex_unique_thm)
  \\ PURE_REWRITE_TAC[o_def]
  \\ PURE_REWRITE_TAC[GSYM eta_ax]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt strip_tac
  >- (
    qexists_tac`Data_Sum_case_left_right f g`
    \\ PURE_REWRITE_TAC sum_case_thms
    \\ PURE_REWRITE_TAC[eta_ax]
    \\ conj_tac \\ REFL_TAC )
  \\ Q.ISPEC_THEN`x`FULL_STRUCT_CASES_TAC sum_cases
  >- (
    rpt(first_x_assum(qspec_then`a`SUBST_ALL_TAC))
    \\ REFL_TAC)
  \\ rpt(first_x_assum(qspec_then`b`SUBST_ALL_TAC))
  \\ REFL_TAC)

val bool_cases = hd(amatch``(x = T) ∨ _``)

val if_T = hd(amatch``(if T then _ else _) = _``)
val if_F = hd(amatch``(if F then _ else _) = _``)

val truth = hd(amatch``T``);
val not_F = hd(amatch``¬F``)

val th7 = store_thm("th7", el 7 goals |> concl,
  rpt gen_tac
  \\ rpt strip_tac
  \\ last_x_assum SUBST_ALL_TAC
  \\ Q.ISPEC_THEN`Q`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[if_T,if_F]
  \\ first_x_assum match_mp_tac
  \\ PURE_REWRITE_TAC[truth,not_F]);

val T_and = hd(amatch``T ∧ t``)
val and_T = hd(amatch``t ∧ T ⇔ _``)
val F_and = hd(amatch``F ∧ t``)
val and_F = hd(amatch``t ∧ F ⇔ _``)
val and_i = hd(amatch``t ∧ t``)

val imp_T = hd(amatch``t ⇒ T``)
val T_imp = hd(amatch``T ⇒ t``)
val F_imp = hd(amatch``F ⇒ t``)
val imp_F = hd(amatch``t ⇒ F ⇔ _``)
val imp_i = hd(amatch``t ⇒ t``)

val T_iff = hd(amatch``(T ⇔ t) ⇔ _``)
val iff_T = hd(amatch``(t ⇔ T) ⇔ _``)
val F_iff = hd(amatch``(F ⇔ t) ⇔ _``)
val iff_F = hd(amatch``(t ⇔ F) ⇔ _``)

val eq_T = hd(amatch``(t ⇔ T) ⇔ _``)
fun EQT_INTRO th = EQ_MP (SPEC (concl th) (GSYM eq_T)) th

val th8 = store_thm("th8", el 8 goals |> concl,
  rpt strip_tac
  \\ Q.ISPEC_THEN`Q`FULL_STRUCT_CASES_TAC bool_cases
  \\ Q.ISPEC_THEN`P'`FULL_STRUCT_CASES_TAC bool_cases
  \\ rpt (pop_assum mp_tac)
  \\ PURE_REWRITE_TAC[and_T,T_and,and_F,F_and,T_imp,F_imp,T_iff,iff_T,F_iff,iff_F,not_F]
  \\ TRY(disch_then MATCH_ACCEPT_TAC)
  \\ disch_then(SUBST_ALL_TAC o EQT_INTRO)
  \\ disch_then(SUBST_ALL_TAC o EQT_INTRO)
  \\ REFL_TAC);

val th9 = store_thm("th9", el 9 goals |> concl,
  rpt strip_tac
  \\ last_x_assum SUBST_ALL_TAC
  \\ Q.ISPEC_THEN`x'`FULL_STRUCT_CASES_TAC bool_cases
  \\ pop_assum mp_tac
  \\ PURE_REWRITE_TAC[T_imp,F_imp]
  \\ TRY REFL_TAC
  \\ disch_then ACCEPT_TAC);

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

val th16 = store_thm("th16", el 16 goals |> concl,
  rpt gen_tac
  \\ qexists_tac`λb. if b then t1 else t2`
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ PURE_REWRITE_TAC[if_T,if_F]
  \\ conj_tac \\ REFL_TAC);

val not_or = hd(amatch``¬(_ ∨ _)``)

val th17 = store_thm("th17", el 17 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[not_and,not_or]
  \\ conj_tac \\ REFL_TAC);

val and_ex = hd(amatch``p ∧ (∃x. _) ⇔ ∃x. p ∧ _``)
val ex_and = hd(amatch``(∃x. _) ∧ p ⇔ ∃x. _ ∧ p``)
val ex_imp = hd(amatch``((∃x. _) ⇒ _) ⇔ _``)

val th18 = store_thm("th18", el 18 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[and_ex,ex_and,ex_imp]
  \\ rpt conj_tac \\ REFL_TAC);

val and_all = hd(amatch``p ∧ (∀x. _) ⇔ ∀x. p ∧ _``)
val all_and = hd(amatch``(∀x. _) ∧ p ⇔ ∀x. _ ∧ p``)
val all_imp = hd(amatch``((∀x. _) ⇒ _) ⇔ _``)
val imp_all = hd(amatch``(_ ⇒ (∀x. _)) ⇔ _``)

val th19 = store_thm("th19", el 19 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[and_all,all_and,all_imp,imp_all]
  \\ rpt conj_tac \\ REFL_TAC);

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

val th36 = store_thm("th36", el 36 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC imp_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL imp_i))
  \\ MATCH_ACCEPT_TAC imp_F);

val T_or = hd(amatch``T ∨ t``)
val or_T = hd(amatch``t ∨ T``)
val F_or = hd(amatch``F ∨ t``)
val or_F = hd(amatch``t ∨ F``)
val or_i = hd(amatch``t ∨ t``)
val th37 = store_thm("th37", el 37 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_or
  \\ conj_tac >- MATCH_ACCEPT_TAC or_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_or
  \\ conj_tac >- MATCH_ACCEPT_TAC or_F
  \\ MATCH_ACCEPT_TAC or_i);

val th38 = store_thm("th38", el 38 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_and
  \\ conj_tac >- MATCH_ACCEPT_TAC and_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_and
  \\ conj_tac >- MATCH_ACCEPT_TAC and_F
  \\ MATCH_ACCEPT_TAC and_i);

val th39 = store_thm("th39", el 39 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_iff
  \\ conj_tac >- MATCH_ACCEPT_TAC iff_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_iff
  \\ MATCH_ACCEPT_TAC iff_F);

val select_eq = hd(amatch``@y. y = x``)
val th40 = store_thm("th40", el 40 goals |> concl,
  CONV_TAC(QUANT_CONV(LAND_CONV(RAND_CONV(ABS_CONV SYM_CONV))))
  \\ MATCH_ACCEPT_TAC select_eq);

val refl = hd(amatch``∀x. x = x``)
val th42 = store_thm("th42", el 42 goals |> concl,
  gen_tac \\ MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL refl)))

val list_ind = hd(amatch``_ ⇒ ∀(l:'a Data_List_list). P l``)
val th47 = store_thm("th47", el 47 goals |> concl,
  rpt strip_tac
  \\ match_mp_tac list_ind
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rpt strip_tac \\ res_tac
  \\ first_assum MATCH_ACCEPT_TAC);

val th48 = store_thm("th48", el 48 goals |> concl,
  imp_F |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> MATCH_ACCEPT_TAC)

val th49 = store_thm("th49", el 49 goals |> concl,
  imp_F |> SPEC_ALL |> EQ_IMP_RULE |> #2 |> MATCH_ACCEPT_TAC)

val th51 = store_thm("th51", el 51 goals |> concl,
  MATCH_ACCEPT_TAC(EQT_ELIM(SPEC_ALL F_imp)))

val reverse_nil = hd(amatch``Data_List_reverse Data_List_nil``)
val reverse_cons = hd(amatch``Data_List_reverse (Data_List_cons _ _)``)
val th52 = store_thm("th52", el 52 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC reverse_nil
  \\ MATCH_ACCEPT_TAC reverse_cons);

val concat_nil = hd(amatch``Data_List_concat Data_List_nil``)
val concat_cons = hd(amatch``Data_List_concat (Data_List_cons _ _)``)
val th53 = store_thm("th53", el 53 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC concat_nil
  \\ MATCH_ACCEPT_TAC concat_cons);

val length_nil = hd(amatch``Data_List_length Data_List_nil``)
val length_cons = hd(amatch``Data_List_length (Data_List_cons _ _)``)
val th55 = store_thm("th55", el 55 goals |> concl,
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

val falsity = th51

fun CONTR tm th = MP (SPEC tm falsity) th

local
   val Fth = ASSUME F
in
   fun EQF_INTRO th =
      IMP_ANTISYM_RULE (NOT_ELIM th)
                       (DISCH F (CONTR (dest_neg (concl th)) Fth))
end

val null_nil = hd(amatch``Data_List_null Data_List_nil``)
val null_cons = hd(amatch``Data_List_null (Data_List_cons _ _)``)
val th56 = store_thm("th56", el 56 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO null_nil)
  \\ MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL null_cons)));

val odd_nil = hd(amatch``Number_Natural_odd Number_Natural_zero``)
val odd_cons = hd(amatch``Number_Natural_odd (Number_Natural_suc _)``)
val th57 = store_thm("th57", el 57 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO odd_nil)
  \\ MATCH_ACCEPT_TAC odd_cons);

val even_nil = hd(amatch``Number_Natural_even Number_Natural_zero``)
val even_cons = hd(amatch``Number_Natural_even (Number_Natural_suc _)``)
val th58 = store_thm("th58", el 58 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO even_nil)
  \\ MATCH_ACCEPT_TAC even_cons);

val map_none = hd(amatch``Data_Option_map _ Data_Option_none = _``)
val map_some = hd(amatch``Data_Option_map _ (Data_Option_some _) = _``)
val th59 = store_thm("th59", el 59 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC map_some
  \\ MATCH_ACCEPT_TAC map_none);

val filter_nil = hd(amatch``Data_List_filter _ Data_List_nil``)
val filter_cons = hd(amatch``Data_List_filter _ (Data_List_cons _ _)``)
val th60 = store_thm("th60", el 60 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC filter_nil
  \\ MATCH_ACCEPT_TAC filter_cons);

val any_nil = hd(amatch``Data_List_any _ Data_List_nil``)
val any_cons = hd(amatch``Data_List_any _ (Data_List_cons _ _)``)
val th62 = store_thm("th62", el 62 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL any_nil))
  \\ MATCH_ACCEPT_TAC any_cons)

val all_nil = hd(amatch``Data_List_all _ Data_List_nil``)
val all_cons = hd(amatch``Data_List_all _ (Data_List_cons _ _)``)
val th63 = store_thm("th63", el 63 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL all_nil))
  \\ MATCH_ACCEPT_TAC all_cons)

val map_nil = hd(amatch``Data_List_map _ Data_List_nil``)
val map_cons = hd(amatch``Data_List_map _ (Data_List_cons _ _)``)
val th64 = store_thm("th64", el 64 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC map_nil
  \\ MATCH_ACCEPT_TAC map_cons)

val append_nil = hd(amatch``Data_List_append Data_List_nil``)
val append_cons = hd(amatch``Data_List_append (Data_List_cons _ _) _ = Data_List_cons _ (_ _ _)``)
val th65 = store_thm("th65", el 65 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC append_nil
  \\ MATCH_ACCEPT_TAC append_cons)

val power_zero = hd(amatch``Number_Natural_power _ Number_Natural_zero``)
val power_suc = hd(amatch``Number_Natural_power _ (Number_Natural_suc _)``)
val th66  = store_thm("th66", el 66 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC power_zero
  \\ MATCH_ACCEPT_TAC power_suc)

val times_comm = hd(amatch``Number_Natural_times x y = Number_Natural_times y x``)
val plus_comm = hd(amatch``Number_Natural_plus x y = Number_Natural_plus y x``)
val times_zero = hd(amatch``Number_Natural_times _ Number_Natural_zero``)
val times_suc = hd(amatch``Number_Natural_times _ (Number_Natural_suc _)``)
val times_zero_comm = PURE_ONCE_REWRITE_RULE[times_comm]times_zero
val th67  = store_thm("th67", el 67 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC times_zero_comm
  \\ MATCH_ACCEPT_TAC
      (PURE_ONCE_REWRITE_RULE[plus_comm](PURE_ONCE_REWRITE_RULE[times_comm]times_suc)))

val plus_zero = hd(amatch``Number_Natural_plus _ Number_Natural_zero``)
val plus_suc = hd(amatch``Number_Natural_plus _ (Number_Natural_suc _)``)
val th68  = store_thm("th68", el 68 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[plus_comm]plus_zero)
  \\ MATCH_ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[plus_comm]plus_suc))

val isSome_some = hd(amatch``Data_Option_isSome (Data_Option_some _)``)
val isSome_none = hd(amatch``Data_Option_isSome (Data_Option_none)``)
val th70 = store_thm("th70", el 70 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL isSome_some))
  \\ MATCH_ACCEPT_TAC (EQF_INTRO isSome_none))

val isNone_some = hd(amatch``Data_Option_isNone (Data_Option_some _)``)
val isNone_none = hd(amatch``Data_Option_isNone (Data_Option_none)``)
val th71 = store_thm("th71", el 71 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL isNone_some))
  \\ MATCH_ACCEPT_TAC (EQT_INTRO isNone_none))

val isRight_right = hd(amatch``Data_Sum_isRight (Data_Sum_right _)``)
val isRight_left = hd(amatch``Data_Sum_isRight (Data_Sum_left _)``)
val th72 = store_thm("th72", el 72 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC isRight_right
  \\ MATCH_ACCEPT_TAC isRight_left)

val isLeft_right = hd(amatch``Data_Sum_isLeft (Data_Sum_right _)``)
val isLeft_left = hd(amatch``Data_Sum_isLeft (Data_Sum_left _)``)
val th73 = store_thm("th73", el 73 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC isLeft_left
  \\ MATCH_ACCEPT_TAC isLeft_right)

val comma_11 = hd(amatch``Data_Pair_comma _ _ = Data_Pair_comma _ _``)
val th104 = store_thm("th104", el 104 goals |> concl,
  MATCH_ACCEPT_TAC comma_11)

val right_11 = hd(amatch``Data_Sum_right _ = Data_Sum_right _``)
val th105 = store_thm("th105", el 105 goals |> concl,
  MATCH_ACCEPT_TAC right_11)

val left_11 = hd(amatch``Data_Sum_left _ = Data_Sum_left _``)
val th106 = store_thm("th106", el 106 goals |> concl,
  MATCH_ACCEPT_TAC left_11)

val th120 = store_thm("th120", el 120 goals |> concl,
  REFL_TAC)

val _ = List.app (Theory.delete_binding o #1) (axioms"-");
val _ = List.app (Theory.delete_binding o #1) (definitions"-");

val _ = export_theory()
