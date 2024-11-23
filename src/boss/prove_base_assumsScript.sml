(* ===================================================================== *)
(* FILE          : prove_base_assumsScript.sml                           *)
(* DESCRIPTION   : Bridge theorems betwen OpenTheory (base) and HOL4     *)
(*                                                                       *)
(* AUTHORS       : (c) Ramana Kumar, Chun Tian                           *)
(* ===================================================================== *)
(* NOTE: To replay this script, use "hol.bare" *)

open HolKernel boolLib bossLib BasicProvers;
open OpenTheoryReader;

(* NOTE: currently there are 96 "assumptions" (stored in the variable 'goals'),
   each represents a theorem defined in boolTheory and used by theories in hol-
   base package (see hol4-base-unint.thy for the list of these HOL4 theories).
   These "assumptions" must be proved by theorems from OpenTheory base package,
   accessible by 'amatch' on 'base_thms'.

   Extra assumptions are those theorems defined in boolTheory but were used in
   subsequent OpenTheory packages beyond hol-base such as hol-res-quan. If any
   necessary assumption is missing here, it will show up later appear as extra
   assumptions in $(HOLDIR)src/real/prove_real_assumsScript.sml, beyond the 22
   assumptions connecting OT and HOL4 reals.
 *)

val Thy = "prove_base_assums";

val _ = new_theory Thy;

val ERR = mk_HOL_ERR Thy;

val _ = new_constant("base-1.221",alpha);

fun fix_tyop {abs={Name="_",Thy=athy},
              rep={Name="_",Thy=rthy},args,ax,name={Thy=tthy,Tyop=tyop}} =
   {abs  = {Name=(tyop^"_abs"),Thy=athy},
    rep  = {Name=(tyop^"_rep"),Thy=rthy},
    name = {Thy=tthy,Tyop=tyop},
    args = args,
    ax   = ax}
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
  | const_name (["HOL4","bool"],"RES_ABSTRACT") = {Thy="bool",Name="RES_ABSTRACT"}
  | const_name (["HOL4","bool"],"RES_EXISTS") = {Thy="bool",Name="RES_EXISTS"}
  | const_name (["HOL4","bool"],"RES_EXISTS_UNIQUE") = {Thy="bool",Name="RES_EXISTS_UNIQUE"}
  | const_name (["HOL4","bool"],"RES_FORALL") = {Thy="bool",Name="RES_FORALL"}
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
  | const_name (ns,n) = {Thy=Thy,Name=String.concatWith "_"(ns@[n])};

fun tyop_name ([],"bool") = {Thy="min",Tyop="bool"}
  | tyop_name ([],"->") = {Thy="min",Tyop="fun"}
  | tyop_name ([],"ind") = {Thy="min",Tyop="ind"}
  | tyop_name (["Data","Pair"],"*") = {Thy=Thy,Tyop="Data_Pair_prod"}
  | tyop_name (["Data","Sum"],"+") = {Thy=Thy,Tyop="Data_Sum_sum"}
  | tyop_name (ns,n) = {Thy=Thy,Tyop=String.concatWith "_"(ns@[n])};

val defs = ref ([]:thm list);
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
  | define_const x tm = define_const_in_thy (fn x => x) x tm;

val (reader:reader) = {
  define_tyop = define_tyop_in_thy o fix_tyop,
  define_const = define_const,
  axiom = fn _ => mk_thm,
  const_name = const_name,
  tyop_name = tyop_name};

val base_thms = read_article "base-theorems.art" reader;

val _ = Net.itnet (fn th => (Thm.delete_proof th; K ())) base_thms ();

fun itpred P th acc = if P th then th::acc else acc;
fun amatch tm = Net.itnet (itpred (DB.matches tm)) base_thms [];

(* NOTE: perhaps the change of constant names here is due to OpenTheory updates *)
val _ = new_constant("hol-base-assums-1.0",alpha);
val _ = new_constant("hol-base-unsat-1.0",alpha);

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
val goals = Net.listItems goalsNet;

val _ = Parse.hide "_";

(* val bool_cases = hd(amatch ``t \/ ~t``); *)
val bool_cases = hd(amatch``(x = T) \/ _``);
val BOOL_CASES_AX = bool_cases;

val or_def = hd(amatch``$\/ = _``);

val imp_T = hd(amatch``t ==> T``);
val T_imp = hd(amatch``T ==> t``);
val F_imp = hd(amatch``F ==> t``);
val imp_F = hd(amatch``t ==> F <=> _``);
val IMP_F = imp_F;
val imp_i = hd(amatch``t ==> t``);

val T_iff = hd(amatch``(T <=> t) <=> _``);
val iff_T = hd(amatch``(t <=> T) <=> _``);
val F_iff = hd(amatch``(F <=> t) <=> _``);
val iff_F = hd(amatch``(t <=> F) <=> _``);

val and_imp_intro = hd(amatch``(a ==> b ==> c) <=> _``);

val eq_T = hd(amatch``(t <=> T) <=> _``);
fun EQT_INTRO th = EQ_MP (SPEC (concl th) (GSYM eq_T)) th;

val EQF_INTRO = SYM o (CONV_RULE(REWR_CONV(GSYM F_iff)));

val not_and = hd (amatch ``~(t1 /\ t2) <=> _``);
val not_not = hd (amatch ``~(~ _)``);
val disj_comm = hd (amatch ``_ \/ _ <=> _ \/ _``);

val T_or = hd(amatch``T \/ t``);
val or_T = hd(amatch``t \/ T``);
val F_or = hd(amatch``F \/ t``);
val or_F = hd(amatch``t \/ F``);
val or_i = hd(amatch``t \/ t``);

val truth = hd(amatch``T``);
val TRUTH = truth;
val not_F = hd(amatch``~F``);

(* |- ~(t /\ ~t) *)
val th1 = store_thm("th1", el 1 goals |> concl,
  PURE_REWRITE_TAC[not_and,not_not]
  \\ Q.SPEC_THEN`t`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[or_T,or_F,not_F]);

val ex_unique_thm = hd (amatch``(?!x. p x) <=> _ /\ _``);
val list_rec = hd(amatch``fn (Data_List_cons h t) = f h t (fn t)``);
val list_ind = hd(amatch``_ ==> !l:'a Data_List_list. P l``);
val fun_eq_thm = hd(amatch``(!x. f x = g x) <=> (f = g)``);

(* |- !x f.
          ?!fn1.
              fn1 Data_List_nil = x /\
              !h t. fn1 (Data_List_cons h t) = f (fn1 t) h t
 *)
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

val o_def = hd(amatch``Function_o = _``);

val sum_cases = hd(amatch``(?a. x = Data_Sum_left a) \/ _``);
val sum_ind = hd(amatch``_ ==> !l:('a,'b) Data_Sum_sum. P l``);

val sum_case_thms = amatch``Data_Sum_case_left_right f g (_ _) = _``;

(* |- !f g.
          ?!h.
              Function_o h Data_Sum_left = f /\
              Function_o h Data_Sum_right = g: thm
 *)
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
  \\ REFL_TAC);

val if_T = hd(amatch``(if T then _ else _) = _``);
val if_F = hd(amatch``(if F then _ else _) = _``);

(* |- !P Q x x' y y'.
          (P <=> Q) /\ (Q ==> x = x') /\ (~Q ==> y = y') ==>
          (if P then x else y) = if Q then x' else y'
 *)
val th4 = store_thm("th4", el 4 goals |> concl,
  rpt gen_tac
  \\ rpt strip_tac
  \\ last_x_assum SUBST_ALL_TAC
  \\ Q.ISPEC_THEN`Q`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[if_T,if_F]
  \\ first_x_assum match_mp_tac
  \\ PURE_REWRITE_TAC[truth,not_F]);

val T_and = hd(amatch``T /\ t``);
val and_T = hd(amatch``t /\ T <=> _``);
val F_and = hd(amatch``F /\ t``);
val and_F = hd(amatch``t /\ F <=> _``);
val and_i = hd(amatch``t /\ t``);

(* |- !P P' Q Q'.
          (Q ==> (P <=> P')) /\ (P' ==> (Q <=> Q')) ==> (P /\ Q <=> P' /\ Q')
 *)
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

(* |- !f g M N. M = N /\ (!x. x = N ==> f x = g x) ==> LET f M = LET g N *)
val th6 = store_thm (* was: LET_CONG *)
  ("th6", el 6 goals |> concl,
  rpt strip_tac
  \\ VAR_EQ_TAC
  \\ PURE_REWRITE_TAC[LET_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ first_x_assum match_mp_tac
  \\ REFL_TAC);

(* |- !x x' y y'.
          (x <=> x') /\ (x' ==> (y <=> y')) ==> (x ==> y <=> x' ==> y')
 *)
val th7 = store_thm
  ("th7", el 7 goals |> concl,
  rpt strip_tac
  \\ last_x_assum SUBST_ALL_TAC
  \\ Q.ISPEC_THEN`x'`FULL_STRUCT_CASES_TAC bool_cases
  \\ pop_assum mp_tac
  \\ PURE_REWRITE_TAC[T_imp,F_imp]
  \\ TRY REFL_TAC
  \\ disch_then ACCEPT_TAC);

val cons_11 = hd (amatch ``Data_List_cons  _ _ = Data_List_cons _ _``);

(* |- !a0 a1 a0' a1'.
          Data_List_cons a0 a1 = Data_List_cons a0' a1' <=>
          a0 = a0' /\ a1 = a1'
 *)
val th8 = store_thm
  ("th8", el 8 goals |> concl, MATCH_ACCEPT_TAC cons_11);

val app_if = hd (amatch ``f (if b then x else y) = if b then f x else f y``);

(* |- !f b x y. f (if b then x else y) = if b then f x else f y *)
val th9 = store_thm
  ("th9", el 9 goals |> concl, MATCH_ACCEPT_TAC app_if);

val demorgan = hd (amatch``(b \/ a) /\ (c \/ a)``);

(* |- !A B C. B /\ C \/ A <=> (B \/ A) /\ (C \/ A) *)
val th10 = store_thm
  ("th10", el 10 goals |> concl, MATCH_ACCEPT_TAC demorgan);

val or_assoc = hd (amatch``(a \/ b) \/ c``);

(* |- !A B C. A \/ B \/ C <=> (A \/ B) \/ C *)
val th11 = store_thm
  ("th11", el 11 goals |> concl, MATCH_ACCEPT_TAC (GSYM or_assoc));

val or_distrib_and = hd (amatch``(b \/ c) /\ a <=> _``);

(* |- !A B C. (B \/ C) /\ A <=> B /\ A \/ C /\ A *)
val th12 = store_thm
  ("th12", el 12 goals |> concl, MATCH_ACCEPT_TAC or_distrib_and);

val and_assoc = hd (amatch``(a /\ b) /\ c``);

(* |- !t1 t2 t3. t1 /\ t2 /\ t3 <=> (t1 /\ t2) /\ t3 *)
val th13 = store_thm
  ("th13", el 13 goals |> concl, MATCH_ACCEPT_TAC (GSYM and_assoc));

val if_T = hd (amatch ``if T then t1 else t2``);
val if_F = hd (amatch ``if F then t1 else t2``);

(* |- !t1 t2. ?fn. fn T = t1 /\ fn F = t2 *)
val th14 = store_thm
  ("th14", el 14 goals |> concl,
  rpt gen_tac
  \\ qexists_tac`\b. if b then t1 else t2`
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ PURE_REWRITE_TAC[if_T,if_F]
  \\ conj_tac \\ REFL_TAC);

val not_or = hd(amatch``~(_ \/ _)``);

(* |- !A B. (~(A /\ B) <=> ~A \/ ~B) /\ (~(A \/ B) <=> ~A /\ ~B) *)
val th15 = store_thm
  ("th15", el 15 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[not_and,not_or]
  \\ conj_tac \\ REFL_TAC);

val and_ex = hd(amatch``p /\ (?x. _) <=> ?x. p /\ _``);
val ex_and = hd(amatch``(?x. _) /\ p <=> ?x. _ /\ p``);
val ex_imp = hd(amatch``((?x. _) ==> _) <=> _``);

(* |- !P Q.
          ((?x. P x) ==> Q <=> !x. P x ==> Q) /\
          ((?x. P x) /\ Q <=> ?x. P x /\ Q) /\
          (Q /\ (?x. P x) <=> ?y. Q /\ P y)
 *)
val th16 = store_thm
  ("th16", el 16 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[and_ex,ex_and,ex_imp]
  \\ rpt conj_tac \\ REFL_TAC);

val and_all = hd(amatch``p /\ (!x. _) <=> !x. p /\ _``);
val all_and = hd(amatch``(!x. _) /\ p <=> !x. _ /\ p``);
val all_imp = hd(amatch``((!x. _) ==> _) <=> _``);
val imp_all = hd(amatch``(_ ==> (!x. _)) <=> _``);

(* |- !P Q.
          (Q ==> (!x. P x) <=> !x. Q ==> P x) /\
          ((!x. P x) /\ Q <=> !x. P x /\ Q) /\
          (Q /\ (!x. P x) <=> !x. Q /\ P x)
 *)
val th17 = store_thm
  ("th17", el 17 goals |> concl,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[and_all,all_and,all_imp,imp_all]
  \\ rpt conj_tac \\ REFL_TAC);

(* |- !t1 t2. (if T then t1 else t2) = t1 /\ (if F then t1 else t2) = t2
 *)
val th18 = store_thm
  ("th18", el 18 goals |> concl,
  rpt gen_tac \\ MATCH_ACCEPT_TAC (CONJ (SPEC_ALL if_T) (SPEC_ALL if_F)));

val forall_eq = hd(amatch``!x. (x = t) ==> _``);
val forall_eq2 = hd(amatch``!x. (t = x) ==> _``);

val ex_def = hd(amatch``$? = _``);
val select_ax = hd(amatch ``p t ==> p ($@ p)``);

(* |- !P t. (!x. x = t ==> P x) ==> $? P *)
val th19 = store_thm
  ("th19", el 19 goals |> concl,
  PURE_REWRITE_TAC[forall_eq,ex_def]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ MATCH_ACCEPT_TAC select_ax);

val eta_ax = hd(amatch``!f. (\x. f x) = f``);

(* |- !P Q. (?x. P x) /\ (!x. P x ==> Q x) ==> Q ($@ P) *)
val th20 = store_thm
  ("th20", el 20 goals |> concl,
  PURE_REWRITE_TAC[ex_def]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV (GSYM eta_ax))))
  \\ first_x_assum ACCEPT_TAC);

(* |- !t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 <=> t2) *)
val th21 = store_thm
  ("th21", el 21 goals |> concl,
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

val imp_antisym_ax = th21;

val suc_11 = hd(amatch``Number_Natural_suc _ = Number_Natural_suc _``);

(* |- !m n. Number_Natural_suc m = Number_Natural_suc n ==> m = n *)
val th22 = store_thm
  ("th22", el 22 goals |> concl,
  rpt gen_tac \\ MATCH_ACCEPT_TAC (#1 (EQ_IMP_RULE (SPEC_ALL suc_11))));

val null_eq = hd(amatch``Data_List_null t <=> (_ = Data_List_nil)``);
val last_cons = hd(amatch``Data_List_last (Data_List_cons h t) = COND _ _ _``);

(* |- !h t.
          Data_List_last (Data_List_cons h t) =
          if t = Data_List_nil then h else Data_List_last t
 *)
val th23 = store_thm
  ("th23", el 23 goals |> concl,
  MATCH_ACCEPT_TAC(PURE_REWRITE_RULE[null_eq]last_cons));

(* NOTE: The following 3 theorems are proved later under different names.

th24: |- !P f. RES_EXISTS_UNIQUE P f <=> (?x::P. f x) /\ !x y::P. f x /\ f y ==> x = y
th25: |- !P f. RES_FORALL P f <=> !x. x IN P ==> f x
th26: |- !P f. RES_EXISTS P f <=> ?x. x IN P /\ f x

 *)

(* |- !t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1) *)
val th27 = store_thm
  ("th27", el 27 goals |> concl,
  rpt gen_tac
  \\ Q.ISPEC_THEN`t1`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,F_iff,T_imp,F_imp,imp_T,imp_F,and_T,T_and]
  \\ REFL_TAC);

val eq_imp_thm = th27;

val ext = hd(amatch``(!x. f x = g x) <=> _``);

(* |- !f g. f = g <=> !x. f x = g x *)
val th28 = store_thm
  ("th28", el 28 goals |> concl, MATCH_ACCEPT_TAC (GSYM ext));

(* |- !A B. (A <=> B \/ A) <=> B ==> A *)
val th29 = store_thm
  ("th29", el 29 goals |> concl,
  rpt gen_tac
  \\ Q.ISPEC_THEN`A`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_iff,or_T,F_iff,or_F,imp_T,imp_F]
  \\ REFL_TAC);

val not_T = hd(amatch``~T``);

(* |- !A B. A ==> B <=> ~A \/ B *)
val IMP_DISJ_THM = store_thm
  ("IMP_DISJ_THM", concl boolTheory.IMP_DISJ_THM,
  rpt gen_tac
  \\ qspec_then`A`FULL_STRUCT_CASES_TAC bool_cases
  \\ PURE_REWRITE_TAC[T_imp,not_T,F_imp,not_F,F_or,T_or]
  \\ REFL_TAC);

(* |- !A B. A \/ B <=> ~A ==> B (DISJ_EQ_IMP) *)
val th30 = save_thm
  ("th30", (* this proof is from boolScript.sml *)
  let
    val lemma = not_not |> SPEC ``A:bool``
  in
    IMP_DISJ_THM
    |> SPECL [``~A:bool``,``B:bool``]
    |> SYM
    |> CONV_RULE
      ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
         (fn tm => lemma))
    |> GENL [``A:bool``,``B:bool``]
  end);

val _ = if concl th30 ~~ concl (el 30 goals) then ()
        else raise ERR "th30" "assumptions changed";

val cons_neq_nil = hd(amatch``Data_List_cons _ _ <> Data_List_nil``);

(* |- !a1 a0. Data_List_nil <> Data_List_cons a0 a1 *)
val th31 = store_thm
  ("th31", el 31 goals |> concl, MATCH_ACCEPT_TAC (GSYM cons_neq_nil));

val some_neq_none = hd(amatch``_ <> Data_Option_none``);

(* |- !t. (T ==> t <=> t) /\ (t ==> T <=> T) /\ (F ==> t <=> T) /\
          (t ==> t <=> T) /\ (t ==> F <=> ~t)
 *)
val th32 = store_thm
  ("th32", el 32 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC imp_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_imp
  \\ conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL imp_i))
  \\ MATCH_ACCEPT_TAC imp_F);

val IMP_CLAUSES = th32;

(* |- !t. (T \/ t <=> T) /\ (t \/ T <=> T) /\ (F \/ t <=> t) /\
          (t \/ F <=> t) /\ (t \/ t <=> t)
 *)
val th33 = store_thm
  ("th33", el 33 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_or
  \\ conj_tac >- MATCH_ACCEPT_TAC or_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_or
  \\ conj_tac >- MATCH_ACCEPT_TAC or_F
  \\ MATCH_ACCEPT_TAC or_i);

val OR_CLAUSES = th33;

(* |- !t. (T /\ t <=> t) /\ (t /\ T <=> t) /\ (F /\ t <=> F) /\
          (t /\ F <=> F) /\ (t /\ t <=> t)
 *)
val th34 = store_thm
  ("th34", el 34 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_and
  \\ conj_tac >- MATCH_ACCEPT_TAC and_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_and
  \\ conj_tac >- MATCH_ACCEPT_TAC and_F
  \\ MATCH_ACCEPT_TAC and_i);

val AND_CLAUSES = th34;

(* |- !t. ((T <=> t) <=> t) /\ ((t <=> T) <=> t) /\ ((F <=> t) <=> ~t) /\
          ((t <=> F) <=> ~t)   (EQ_CLAUSES)
 *)
val th35 = store_thm
  ("th35", el 35 goals |> concl,
  gen_tac
  \\ conj_tac >- MATCH_ACCEPT_TAC T_iff
  \\ conj_tac >- MATCH_ACCEPT_TAC iff_T
  \\ conj_tac >- MATCH_ACCEPT_TAC F_iff
  \\ MATCH_ACCEPT_TAC iff_F);

val EQ_CLAUSES = th35;

val select_eq = hd(amatch``@y. y = x``)

(* |- !x. (@y. x = y) = x *)
val th36 = store_thm
  ("th36", el 36 goals |> concl,
  CONV_TAC(QUANT_CONV(LAND_CONV(RAND_CONV(ABS_CONV SYM_CONV))))
  \\ MATCH_ACCEPT_TAC select_eq);

(* |- !t. t ==> F <=> (t <=> F) *)
val th37 = store_thm
  ("th37", el 37 goals |> concl,
  PURE_REWRITE_TAC[imp_F, iff_F]
  \\ gen_tac \\ REFL_TAC);

val refl = hd(amatch``!x. x = x``);

(* |- !x. x = x <=> T *)
val th38 = store_thm
  ("th38", el 38 goals |> concl,
  gen_tac \\ MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL refl)));

val eq_trans = hd(amatch``(x = y) /\ (y = z) ==> _``);

(* |- !f.
          (!x y z. f x (f y z) = f (f x y) z) ==>
          (!x y. f x y = f y x) ==>
          !x y z. f x (f y z) = f y (f x z)
 *)
val th39 = store_thm
  ("th39", el 39 goals |> concl,
  rpt strip_tac
  \\ first_assum(qspecl_then[`x`,`y`,`z`]SUBST_ALL_TAC)
  \\ last_assum(qspecl_then[`f x y`,`z`]SUBST_ALL_TAC)
  \\ first_assum(qspecl_then[`z`,`x`,`y`]SUBST_ALL_TAC)
  \\ last_assum(qspecl_then[`f z x`,`y`]SUBST_ALL_TAC)
  \\ AP_TERM_TAC
  \\ last_assum(qspecl_then[`z`,`x`]ACCEPT_TAC));

val less_zero = hd(amatch``Number_Natural_less Number_Natural_zero n <=> _ <> _``);
val div_mod = hd(amatch``Number_Natural_times (Number_Natural_div k n) n``);
val less_mod = hd(amatch``Number_Natural_less (Number_Natural_mod _ _)``);

(* |- !n.
          Number_Natural_less Number_Natural_zero n ==>
          !k. k =
              Number_Natural_plus
                (Number_Natural_times (Number_Natural_div k n) n)
                (Number_Natural_mod k n) /\
              Number_Natural_less (Number_Natural_mod k n) n
 *)
val th40 = store_thm
  ("th40", el 40 goals |> concl,
  PURE_REWRITE_TAC[less_zero]
  \\ gen_tac
  \\ disch_then(fn th => (strip_assume_tac (MATCH_MP less_mod th) >>
       (strip_assume_tac (MATCH_MP div_mod th))))
  \\ gen_tac
  \\ first_x_assum(qspec_then`k`SUBST_ALL_TAC)
  \\ conj_tac >- REFL_TAC
  \\ first_x_assum(qspec_then`k`ACCEPT_TAC));

val list_ind = hd(amatch``_ ==> !(l:'a Data_List_list). P l``);

(* |- !P. P Data_List_nil /\ (!t. P t ==> !h. P (Data_List_cons h t)) ==>
          !l. P l
 *)
val th41 = store_thm
  ("th41", el 41 goals |> concl,
  rpt strip_tac
  \\ match_mp_tac list_ind
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ rpt strip_tac \\ res_tac
  \\ first_assum MATCH_ACCEPT_TAC);

(* |- !t. (t ==> F) ==> ~t *)
val th42 = store_thm
  ("th42", el 42 goals |> concl,
  imp_F |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> MATCH_ACCEPT_TAC);

(* |- !t. ~t ==> t ==> F (boolTheory.F_IMP) *)
val th43 = store_thm
  ("th43", el 43 goals |> concl,
  imp_F |> SPEC_ALL |> EQ_IMP_RULE |> #2 |> MATCH_ACCEPT_TAC);

(* |- !t. F ==> t *)
val th44 = store_thm
  ("th44", el 44 goals |> concl,
  MATCH_ACCEPT_TAC(EQT_ELIM(SPEC_ALL F_imp)));

(* |- (!x. P x ==> Q x) ==> (?x. P x) ==> ?x'. Q x' *)
val th45 = store_thm
  ("th45", el 45 goals |> concl,
  rpt strip_tac
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ qexists_tac`x`
  \\ first_assum ACCEPT_TAC);

(* |- (!x. P x ==> Q x) ==> (!x. P x) ==> !x. Q x
val th43 = store_thm
  ("th43", el 46 goals |> concl,
  rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ first_x_assum(qspec_then`x`ACCEPT_TAC));
 *)

(* |- (x ==> y) /\ (z ==> w) ==> x \/ z ==> y \/ w *)
val th46 = store_thm
  ("th46", el 46 goals |> concl,
  rpt strip_tac
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ TRY (disj1_tac >> first_assum ACCEPT_TAC)
  \\ TRY (disj2_tac >> first_assum ACCEPT_TAC));

(* |- (x ==> y) /\ (z ==> w) ==> x /\ z ==> y /\ w *)
val th47 = store_thm
  ("th47", el 47 goals |> concl,
   rpt strip_tac
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ first_x_assum(fn th => first_x_assum (assume_tac o MATCH_MP th))
  \\ first_assum ACCEPT_TAC);

val unpair = hd(amatch``Data_Pair_comma (Data_Pair_fst _) _``);
val unzip_nil = hd(amatch``Data_List_unzip Data_List_nil``);
val unzip_cons = hd(amatch``Data_List_unzip (Data_List_cons _ _)``);

(* |- Data_List_unzip Data_List_nil =
      Data_Pair_comma Data_List_nil Data_List_nil /\
      !x l.
          Data_List_unzip (Data_List_cons x l) =
          Data_Pair_comma
            (Data_List_cons (Data_Pair_fst x)
               (Data_Pair_fst (Data_List_unzip l)))
            (Data_List_cons (Data_Pair_snd x)
               (Data_Pair_snd (Data_List_unzip l)))
 *)
val th48 = store_thm
  ("th48", el 48 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC unzip_nil
  \\ PURE_REWRITE_TAC[unzip_cons]
  \\ rpt gen_tac
  \\ conj_tac
  \\ MATCH_ACCEPT_TAC(GSYM unpair));

val reverse_nil = hd(amatch``Data_List_reverse Data_List_nil``);
val reverse_cons = hd(amatch``Data_List_reverse (Data_List_cons _ _)``);

(* |- Data_List_reverse Data_List_nil = Data_List_nil /\
      !h t.
          Data_List_reverse (Data_List_cons h t) =
          Data_List_append (Data_List_reverse t)
            (Data_List_cons h Data_List_nil)
 *)
val th49 = store_thm
  ("th49", el 49 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC reverse_nil
  \\ MATCH_ACCEPT_TAC reverse_cons);

val concat_nil = hd(amatch``Data_List_concat Data_List_nil``);
val concat_cons = hd(amatch``Data_List_concat (Data_List_cons _ _)``);

(* |- Data_List_concat Data_List_nil = Data_List_nil /\
      !h t.
          Data_List_concat (Data_List_cons h t) =
          Data_List_append h (Data_List_concat t)
 *)
val th50 = store_thm
  ("th50", el 50 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC concat_nil
  \\ MATCH_ACCEPT_TAC concat_cons);

val fact_zero = hd(amatch``Number_Natural_factorial Number_Natural_zero``);
val fact_suc = hd(amatch``Number_Natural_factorial (Number_Natural_suc _)``);

(* |- Number_Natural_factorial Number_Natural_zero =
      Number_Natural_bit1 Number_Natural_zero /\
      !n.
          Number_Natural_factorial (Number_Natural_suc n) =
          Number_Natural_times (Number_Natural_suc n)
            (Number_Natural_factorial n)
 *)
val th51 = store_thm
  ("th51", el 51 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC fact_zero
  \\ MATCH_ACCEPT_TAC fact_suc);

val length_nil = hd(amatch``Data_List_length Data_List_nil``);
val length_cons = hd(amatch``Data_List_length (Data_List_cons _ _)``);

(* |- Data_List_length Data_List_nil = Number_Natural_zero /\
      !h t.
          Data_List_length (Data_List_cons h t) =
          Number_Natural_suc (Data_List_length t)
 *)
val th52 = store_thm
  ("th52", el 52 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC length_nil
  \\ MATCH_ACCEPT_TAC length_cons);

fun EQT_ELIM th = EQ_MP (SYM th) truth;

fun EQF_ELIM th =
   let
      val (lhs, rhs) = dest_eq (concl th)
      val _ = assert Feq rhs
   in
      NOT_INTRO (DISCH lhs (EQ_MP th (ASSUME lhs)))
   end;

val null_nil = hd(amatch``Data_List_null Data_List_nil``);
val null_cons = hd(amatch``Data_List_null (Data_List_cons _ _)``);

(* |- (Data_List_null Data_List_nil <=> T) /\
      !h t. Data_List_null (Data_List_cons h t) <=> F
 *)
val th53 = store_thm
  ("th53", el 53 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO null_nil)
  \\ MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL null_cons)));

val odd_nil = hd(amatch``Number_Natural_odd Number_Natural_zero``);
val odd_cons = hd(amatch``Number_Natural_odd (Number_Natural_suc _)``);

(* |- (Number_Natural_odd Number_Natural_zero <=> F) /\
      !n. Number_Natural_odd (Number_Natural_suc n) <=> ~Number_Natural_odd n
 *)
val th54 = store_thm
  ("th54", el 54 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO odd_nil)
  \\ MATCH_ACCEPT_TAC odd_cons);

val even_nil = hd(amatch``Number_Natural_even Number_Natural_zero``);
val even_cons = hd(amatch``Number_Natural_even (Number_Natural_suc _)``);

(* |- (Number_Natural_even Number_Natural_zero <=> T) /\
      !n. Number_Natural_even (Number_Natural_suc n) <=> ~Number_Natural_even n
 *)
val th55 = store_thm
  ("th55", el 55 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO even_nil)
  \\ MATCH_ACCEPT_TAC even_cons);

val left_11 = hd(amatch``Data_Sum_left _ = Data_Sum_left _``);
val right_11 = hd(amatch``Data_Sum_right _ = Data_Sum_right _``);

(* NOTE:

th56 |- (!p m x. x IN p ==> RES_ABSTRACT p m x = m x) /\
         !p m1 m2. (!x. x IN p ==> m1 x = m2 x) ==> RES_ABSTRACT p m1 = RES_ABSTRACT p m2
 *)

(* |- (!x x'. Data_Sum_left x = Data_Sum_left x' <=> x = x') /\
      !y y'. Data_Sum_right y = Data_Sum_right y' <=> y = y'
 *)
val th57 = store_thm
  ("th57", el 57 goals |> concl,
    conj_tac
 >| [ MATCH_ACCEPT_TAC left_11,
      MATCH_ACCEPT_TAC right_11 ]);

val map_none = hd(amatch``Data_Option_map _ Data_Option_none = _``)
val map_some = hd(amatch``Data_Option_map _ (Data_Option_some _) = _``)

(* |- (!f x. Data_Option_map f (Data_Option_some x) = Data_Option_some (f x)) /\
      !f. Data_Option_map f Data_Option_none = Data_Option_none
 *)
val th58 = store_thm
  ("th58", el 58 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC map_some
  \\ MATCH_ACCEPT_TAC map_none);

val filter_nil = hd(amatch``Data_List_filter _ Data_List_nil``);
val filter_cons = hd(amatch``Data_List_filter _ (Data_List_cons _ _)``);

(* |- (!P. Data_List_filter P Data_List_nil = Data_List_nil) /\
      !P h t.
          Data_List_filter P (Data_List_cons h t) =
          if P h then Data_List_cons h (Data_List_filter P t)
          else Data_List_filter P t
 *)
val th59 = store_thm
  ("th59", el 59 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC filter_nil
  \\ MATCH_ACCEPT_TAC filter_cons);

val map_nil = hd(amatch``Data_List_map _ Data_List_nil``);
val map_cons = hd(amatch``Data_List_map _ (Data_List_cons _ _)``);

(* |- (!f. Data_List_map f Data_List_nil = Data_List_nil) /\
      !f h t.
          Data_List_map f (Data_List_cons h t) =
          Data_List_cons (f h) (Data_List_map f t)
 *)
val th60 = store_thm
  ("th60", el 60 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC map_nil
  \\ MATCH_ACCEPT_TAC map_cons);

val any_nil = hd(amatch``Data_List_any _ Data_List_nil``);
val any_cons = hd(amatch``Data_List_any _ (Data_List_cons _ _)``);

(* |- (!P. Data_List_any P Data_List_nil <=> F) /\
      !P h t.
          Data_List_any P (Data_List_cons h t) <=> P h \/ Data_List_any P t
 *)
val th61 = store_thm
  ("th61", el 61 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL any_nil))
  \\ MATCH_ACCEPT_TAC any_cons);

val all_nil = hd(amatch``Data_List_all _ Data_List_nil``);
val all_cons = hd(amatch``Data_List_all _ (Data_List_cons _ _)``);

(* |- (!P. Data_List_all P Data_List_nil <=> T) /\
      !P h t.
          Data_List_all P (Data_List_cons h t) <=> P h /\ Data_List_all P t
 *)
val th62 = store_thm
  ("th62", el 62 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL all_nil))
  \\ MATCH_ACCEPT_TAC all_cons);

val append_nil = hd(amatch``Data_List_append Data_List_nil``);
val append_cons =
    hd(amatch ``Data_List_append (Data_List_cons _ _) _ =
                Data_List_cons _ (_ _ _)``);

(* |- (!l. Data_List_append Data_List_nil l = l) /\
      !l1 l2 h.
          Data_List_append (Data_List_cons h l1) l2 =
          Data_List_cons h (Data_List_append l1 l2)
 *)
val th63 = store_thm
  ("th63", el 63 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC append_nil
  \\ MATCH_ACCEPT_TAC append_cons);

val power_zero = hd(amatch``Number_Natural_power _ Number_Natural_zero``);
val power_suc = hd(amatch``Number_Natural_power _ (Number_Natural_suc _)``);

(* |- (!m.
           Number_Natural_power m Number_Natural_zero =
           Number_Natural_bit1 Number_Natural_zero) /\
      !m n.
          Number_Natural_power m (Number_Natural_suc n) =
          Number_Natural_times m (Number_Natural_power m n)
 *)
val th64 = store_thm
  ("th64", el 64 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC power_zero
  \\ MATCH_ACCEPT_TAC power_suc);

val times_comm = hd(amatch``Number_Natural_times x y = Number_Natural_times y x``);
val plus_comm = hd(amatch``Number_Natural_plus x y = Number_Natural_plus y x``);
val times_zero = hd(amatch``Number_Natural_times _ Number_Natural_zero``);
val times_suc = hd(amatch``Number_Natural_times _ (Number_Natural_suc _)``);
val times_zero_comm = PURE_ONCE_REWRITE_RULE [times_comm] times_zero;

(* |- (!n. Number_Natural_times Number_Natural_zero n = Number_Natural_zero) /\
      !m n.
          Number_Natural_times (Number_Natural_suc m) n =
          Number_Natural_plus (Number_Natural_times m n) n
 *)
val th65 = store_thm
  ("th65", el 65 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC times_zero_comm
  \\ MATCH_ACCEPT_TAC
      (PURE_ONCE_REWRITE_RULE[plus_comm](PURE_ONCE_REWRITE_RULE[times_comm]times_suc)));

val plus_zero = hd(amatch``Number_Natural_plus _ Number_Natural_zero``);
val plus_suc = hd(amatch``Number_Natural_plus _ (Number_Natural_suc _)``);

(* |- (!n. Number_Natural_plus Number_Natural_zero n = n) /\
      !m n.
          Number_Natural_plus (Number_Natural_suc m) n =
          Number_Natural_suc (Number_Natural_plus m n)
 *)
val th66 = store_thm
  ("th66", el 66 goals |> concl,
  conj_tac >- MATCH_ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[plus_comm]plus_zero)
  \\ MATCH_ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[plus_comm]plus_suc));

(* |- (!t. ~~t <=> t) /\ (~T <=> F) /\ (~F <=> T) *)
val th67 = store_thm
  ("th67", el 67 goals |> concl,
  PURE_REWRITE_TAC[not_not,iff_F,iff_T,truth,not_F,and_T]
  \\ gen_tac \\ REFL_TAC);

val NOT_CLAUSES = th67;

val isRight_right = hd(amatch``Data_Sum_isRight (Data_Sum_right _)``);
val isRight_left = hd(amatch``Data_Sum_isRight (Data_Sum_left _)``);

(* |- (!x. Data_Sum_isRight (Data_Sum_right x)) /\
      !y. ~Data_Sum_isRight (Data_Sum_left y)
 *)
val th68 = store_thm
  ("th68", el 68 goals |> concl,
    conj_tac
 >| [ PURE_REWRITE_TAC [iff_T] >> MATCH_ACCEPT_TAC isRight_right,
      PURE_REWRITE_TAC [iff_F] >> MATCH_ACCEPT_TAC isRight_left ]);

val isLeft_right = hd(amatch``Data_Sum_isLeft (Data_Sum_right _)``);
val isLeft_left = hd(amatch``Data_Sum_isLeft (Data_Sum_left _)``);

(* |- (!x. Data_Sum_isLeft (Data_Sum_left x) <=> T) /\
      !y. Data_Sum_isLeft (Data_Sum_right y) <=> F
 *)
val th69 = store_thm
  ("th69", el 69 goals |> concl,
    conj_tac
 >| [ PURE_REWRITE_TAC [iff_T] >> MATCH_ACCEPT_TAC isLeft_left,
      PURE_REWRITE_TAC [iff_F] >> MATCH_ACCEPT_TAC isLeft_right ]);

val isSome_some = hd(amatch``Data_Option_isSome (Data_Option_some _)``);
val isSome_none = hd(amatch``Data_Option_isSome (Data_Option_none)``);

(* |- (!x. Data_Option_isSome (Data_Option_some x) <=> T) /\
      (Data_Option_isSome Data_Option_none <=> F)
 *)
val th70 = store_thm
  ("th70", el 70 goals |> concl,
    conj_tac
 >| [ MATCH_ACCEPT_TAC (EQT_INTRO (SPEC_ALL isSome_some)),
      MATCH_ACCEPT_TAC (EQF_INTRO isSome_none) ]);

val isNone_some = hd(amatch``Data_Option_isNone (Data_Option_some _)``);
val isNone_none = hd(amatch``Data_Option_isNone (Data_Option_none)``);

(* |- (!x. Data_Option_isNone (Data_Option_some x) <=> F) /\
      (Data_Option_isNone Data_Option_none <=> T)
 *)
val th71 = store_thm
  ("th71", el 71 goals |> concl,
    conj_tac
 >| [ MATCH_ACCEPT_TAC (EQF_INTRO (SPEC_ALL isNone_some)),
      MATCH_ACCEPT_TAC (EQT_INTRO isNone_none) ]);

val tc_def           = hd(amatch``!x. Relation_transitiveClosure x = _``);
val bigIntersect_thm = hd(amatch``Relation_bigIntersect a b c <=> _``);
val mem_fromPred     = hd(amatch``Set_member r (Set_fromPredicate _)``);
val subrelation_thm  = hd(amatch``Relation_subrelation x s <=> !x y. _``);
val transitive_thm   = hd(amatch``Relation_transitive s <=> _``);

(* |- Relation_transitiveClosure =
      (\R a b.
           !P. (!x y. R x y ==> P x y) /\ (!x y z. P x y /\ P y z ==> P x z) ==>
               P a b)
 *)
val th72 = store_thm
  ("th72", el 72 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ PURE_REWRITE_TAC[tc_def,bigIntersect_thm,mem_fromPred]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ Ho_Rewrite.PURE_REWRITE_TAC[ex_imp]
  \\ PURE_REWRITE_TAC[subrelation_thm,transitive_thm]
  \\ PURE_ONCE_REWRITE_TAC[GSYM and_imp_intro]
  \\ Ho_Rewrite.PURE_REWRITE_TAC[forall_eq2]
  \\ rpt gen_tac
  \\ PURE_REWRITE_TAC[GSYM and_imp_intro]
  \\ REFL_TAC);

val wellFounded_thm = hd(amatch``Relation_wellFounded r <=> !p. (?x. _) ==> _``);

(* |- Relation_wellFounded =
      (\R. !B. (?w. B w) ==> ?min. B min /\ !b. R b min ==> ~B b)
 *)
val th73 = store_thm
  ("th73", el 73 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ PURE_REWRITE_TAC[wellFounded_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ gen_tac \\ REFL_TAC);

(* |- !A. A ==> ~A ==> F *)
val F_IMP2 = store_thm
  ("F_IMP2", “!A. A ==> ~A ==> F”,
  PURE_REWRITE_TAC[GSYM imp_F]
  \\ gen_tac
  \\ disch_then(fn th => disch_then(ACCEPT_TAC o C MP th)));

val less_thm     = hd(amatch``Number_Natural_less _ _ <=> ?x. _``);
val less_refl    = hd(amatch``Number_Natural_less x x``);
val less_zero    = hd(amatch``~(Number_Natural_less _ (Number_Natural_zero))``);
val less_suc_suc = hd(amatch``Number_Natural_less (Number_Natural_suc _) b``);
val less_suc     = hd(amatch``Number_Natural_less n (Number_Natural_suc n)``);
val less_trans   = hd(amatch``Number_Natural_less x y /\ Number_Natural_less y z ==> _``);
val num_cases    = hd(amatch``(n = Number_Natural_zero) \/ ?n. _``);
val num_ind      = hd(amatch``_ ==> !n. P (n:Number_Natural_natural)``);
val num_less_ind = hd(amatch``(!x. _ ==> _) ==> !n. P (n:Number_Natural_natural)``);
val not_less     = hd(amatch``~(Number_Natural_less _ _) <=> _``);
val less_lesseq  = hd(amatch``Number_Natural_less m (Number_Natural_suc n) <=>
                              Number_Natural_lesseq m n``);
val less_or_eq   = hd(amatch``Number_Natural_lesseq _ _ <=> (Number_Natural_less _ _) \/ _``);
val trichotomy   = hd(amatch``_ \/ _ \/ (_ = _)``);

(* |- Number_Natural_less =
      (\m n. ?P. (!n. P (Number_Natural_suc n) ==> P n) /\ P m /\ ~P n)
 *)
val th74 = store_thm
  ("th74", el 74 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm]
  \\ qx_genl_tac[`a`,`b`]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ match_mp_tac (PURE_REWRITE_RULE[and_imp_intro] imp_antisym_ax)
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
    \\ qspec_then`~(P b)`(match_mp_tac o UNDISCH) F_IMP2
    \\ PURE_REWRITE_TAC[not_not]
    \\ first_x_assum match_mp_tac
    \\ first_assum ACCEPT_TAC )
  \\ VAR_EQ_TAC
  \\ first_x_assum(assume_tac o EQF_INTRO)
  \\ first_x_assum(fn th => (first_x_assum(mp_tac o EQ_MP th)))
  \\ PURE_REWRITE_TAC[F_imp]);

(* |- Relation_transitive = (\R. !x y z. R x y /\ R y z ==> R x z) *)
val th75 = store_thm
  ("th75", el 75 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,transitive_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ gen_tac \\ REFL_TAC);

(* |- Relation_subrelation = (\R1 R2. !x y. R1 x y ==> R2 x y) *)
val th76 = store_thm
  ("th76", el 76 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,subrelation_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val union_thm = hd(amatch``Relation_union r s = _``);
val fromSet_thm = hd(amatch``Relation_fromSet _ _ _``);
val mem_union = hd(amatch``Set_member _ (Set_union _ _) <=> _``);
val mem_toSet = hd(amatch``Set_member _ (Relation_toSet _)``);

(* |- Relation_union = (\R1 R2 x y. R1 x y \/ R2 x y) *)
val th77 = store_thm
  ("th77", el 77 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,union_thm,fromSet_thm,mem_union,mem_toSet]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val intersect_thm = hd(amatch``Relation_intersect x y = _``);
val mem_inter     = hd(amatch``Set_member _ (Set_intersect _ _)``);

(* |- Relation_intersect = (\R1 R2 x y. R1 x y /\ R2 x y) *)
val th78 = store_thm
  ("th78", el 78 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,intersect_thm,fromSet_thm,mem_inter,mem_toSet]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val greatereq_thm = hd(amatch``Number_Natural_greatereq _ _``);
val greater_thm   = hd(amatch``Number_Natural_greater _ _ = _``);

(* |- Number_Natural_greatereq = (\m n. Number_Natural_greater m n \/ m = n) *)
val th79 = store_thm
  ("th79", el 79 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,greatereq_thm,less_or_eq,greater_thm]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
  \\ REFL_TAC);

(* |- Number_Natural_lesseq = (\m n. Number_Natural_less m n \/ m = n) *)
val th80 = store_thm
  ("th80", el 80 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,less_or_eq]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val min_thm = hd(amatch``Number_Natural_min _ _ = COND _ _ _``);
val if_id   = hd(amatch``if _ then x else x``);

(* |- Number_Natural_min = (\m n. if Number_Natural_less m n then m else n) *)
val th81 = store_thm
  ("th81", el 81 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,min_thm,less_or_eq]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ qspec_then`x = x'`strip_assume_tac bool_cases
  \\ first_assum SUBST1_TAC
  \\ PURE_REWRITE_TAC[or_F,or_T,if_T]
  \\ TRY REFL_TAC
  \\ pop_assum(SUBST1_TAC o EQT_ELIM)
  \\ PURE_REWRITE_TAC[if_id]
  \\ REFL_TAC);

val max_thm = hd(amatch``Number_Natural_max _ _ = COND _ _ _``);

(* |- Number_Natural_max = (\m n. if Number_Natural_less m n then n else m) *)
val th82 = store_thm
  ("th82", el 82 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,max_thm,less_or_eq]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ qspec_then`x = x'`strip_assume_tac bool_cases
  \\ first_assum SUBST1_TAC
  \\ PURE_REWRITE_TAC[or_F,or_T,if_T]
  \\ TRY REFL_TAC
  \\ pop_assum(SUBST1_TAC o EQT_ELIM)
  \\ PURE_REWRITE_TAC[if_id]
  \\ REFL_TAC);

val bit1_thm = hd(amatch``Number_Natural_bit1 _ = _``);
val bit0_suc = hd(amatch``Number_Natural_bit0 _ = _ _``);
val bit0_zero = hd(amatch``Number_Natural_bit0 Number_Natural_zero``);
val plus_zero = hd(amatch``Number_Natural_plus Number_Natural_zero _``);
val plus_suc = hd(amatch``Number_Natural_plus _ (Number_Natural_suc _)``);
val plus_suc1 = hd(amatch``Number_Natural_plus (Number_Natural_suc _) _``);

(* |- Number_Natural_bit1 =
      (\n.
           Number_Natural_plus n
             (Number_Natural_plus n (Number_Natural_suc Number_Natural_zero)))
 *)
val th83 = store_thm
  ("th83", el 83 goals |> concl,
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
  \\ REFL_TAC);

val irreflexive_thm = hd(amatch``Relation_irreflexive _ = _``);

(* |- Relation_irreflexive = (\R. !x. ~R x x) *)
val th84 = store_thm
  ("th84", el 84 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm, irreflexive_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac
  \\ REFL_TAC);

val reflexive_thm = hd(amatch``Relation_reflexive _ = _``);

(* |- Relation_reflexive = (\R. !x. R x x) *)
val th85 = store_thm
  ("th85", el 85 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm, reflexive_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val o_thm = hd(amatch``(Function_o _ _) _ = _``);

(* |- Function_o = (\f g x. f (g x)) *)
val th86 = store_thm
  ("th86", el 86 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,o_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

(* |- Number_Natural_greater = (\m n. Number_Natural_less n m) *)
val th87 = store_thm
  ("th87", el 87 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,greater_thm]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val skk = hd(amatch``Function_Combinator_s _ _ = Function_id``);

(* |- Function_id = Function_Combinator_s Function_const Function_const *)
val th88 = store_thm
  ("th88", el 88 goals |> concl,
  PURE_REWRITE_TAC[skk] \\ REFL_TAC);

val comma_11 = hd(amatch``Data_Pair_comma _ _ = Data_Pair_comma _ _``);

(* |- Data_Pair_comma x y = Data_Pair_comma a b <=> x = a /\ y = b *)
val th89 = store_thm
  ("th89", el 89 goals |> concl,
  MATCH_ACCEPT_TAC comma_11);

(* |- Data_Sum_right x = Data_Sum_right y <=> x = y *)
val th90 = store_thm
  ("th90", el 90 goals |> concl,
  MATCH_ACCEPT_TAC right_11);

(* |- Data_Sum_left x = Data_Sum_left y <=> x = y *)
val th91 = store_thm
  ("th91", el 91 goals |> concl,
  MATCH_ACCEPT_TAC left_11);

(* |- (?!x. P x) <=> (?x. P x) /\ !x y. P x /\ P y ==> x = y
val th89 = store_thm
  ("th89", el 89 goals |> concl,
  MATCH_ACCEPT_TAC ex_unique_thm);
 *)

val exists_simp = hd(amatch “(?x. t) <=> t”);

(* |- (?!x. F) <=> F *)
val th92 = store_thm
  ("th92", el 92 goals |> concl,
  PURE_REWRITE_TAC [BETA_RULE (SPEC “\x:'a. F” ex_unique_thm)] \\
  PURE_REWRITE_TAC [SPEC “F” exists_simp, F_and] \\
  REFL_TAC);

val one_thm = hd(amatch``_ = Data_Unit_unit``);

(* |- Data_Unit_unit = @x. T *)
val th93 = store_thm
  ("th93", el 93 goals |> concl,
  PURE_ONCE_REWRITE_TAC[one_thm] \\ REFL_TAC);

val universe_thm = hd(amatch``Relation_universe _ _``);

(* |- Relation_universe = (\x y. T) *)
val th94 = store_thm
  ("th94", el 94 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,EQT_INTRO(SPEC_ALL universe_thm)]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val empty_thm = hd(amatch``Relation_empty _ _``);

(* |- Relation_empty = (\x y. F) *)
val th95 = store_thm
  ("th95", el 95 goals |> concl,
  PURE_REWRITE_TAC[GSYM fun_eq_thm,EQF_INTRO (SPEC_ALL empty_thm)]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

(* |- Number_Natural_zero = Number_Natural_zero *)
val th96 = store_thm
  ("th96", el 96 goals |> concl,
  REFL_TAC);

(* Now raise an error if the above th96 is not the last one *)
val _ = if List.length goals <> 96 then
            (raise ERR "-" "assumptions changed")
        else ();

(* Other theorems (from boolTheory, used by other OT packages)

   NOTE: The following extra theorems are defined in boolTheory but are used by
   theories beyond hol-base.
 *)

(* |- (y ==> x) /\ (z ==> w) ==> (x ==> z) ==> y ==> w *)
val MONO_IMP = store_thm("MONO_IMP", concl boolTheory.MONO_IMP,
  rpt strip_tac
  \\ rpt(first_x_assum match_mp_tac)
  \\ first_x_assum ACCEPT_TAC);

val mono_not = hd (amatch “(y ==> x) ==> ~x ==> ~y”);

(* |- (y ==> x) ==> ~x ==> ~y *)
val MONO_NOT = store_thm
  ("MONO_NOT", concl boolTheory.MONO_NOT,
    MATCH_ACCEPT_TAC mono_not);

val mono_not_eq = hd (amatch “~t1 ==> ~t2 <=> t2 ==> t1”);
val eq_sym_eq = hd (amatch “x = y <=> y = x”);

(* |- y ==> x <=> ~x ==> ~y *)
val MONO_NOT_EQ = store_thm
  ("MONO_NOT_EQ", concl boolTheory.MONO_NOT_EQ,
    PURE_ONCE_REWRITE_TAC [eq_sym_eq]
 >> MATCH_ACCEPT_TAC mono_not_eq);

(* |- P (let x = M in N x) <=> (let x = M in P (N x)) *)
val LET_RAND = store_thm("LET_RAND", concl boolTheory.LET_RAND,
  PURE_REWRITE_TAC[LET_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ REFL_TAC)

(* |- (T <=/=> F) /\ (F <=/=> T) *)
val BOOL_EQ_DISTINCT = store_thm("BOOL_EQ_DISTINCT", concl boolTheory.BOOL_EQ_DISTINCT,
  PURE_REWRITE_TAC[iff_F,not_not,iff_T,not_F,and_T]);

(* |- (!t1 t2. (if T then t1 else t2) = t1) /\
      !t1 t2. (if F then t1 else t2) = t2
 *)
val bool_case_thm = store_thm
  ("bool_case_thm", concl boolTheory.bool_case_thm,
  PURE_REWRITE_TAC[th18]
  \\ conj_tac \\ rpt gen_tac \\ REFL_TAC);

val forall_bool = hd(amatch``(!b:bool. P b) <=> _``)

(* |- (!b. P b) <=> P T /\ P F *)
val FORALL_BOOL = store_thm("FORALL_BOOL", concl boolTheory.FORALL_BOOL,
  MATCH_ACCEPT_TAC forall_bool);

val cond_expand = hd(amatch ``(if b then t1 else t2) <=> _``);

(* |- !b t1 t2. (if b then t1 else t2) <=> (b ==> t1) /\ (~b ==> t2)
 *)
val COND_EXPAND_IMP = save_thm
  ("COND_EXPAND_IMP", (* this proof is from boolScript.sml *)
 let val b    = “b:bool”
     val t1   = “t1:bool”
     val t2   = “t2:bool”
     val nb   = mk_neg b;
     val nnb  = mk_neg nb;
     val imp_th1  = SPECL [b, t1] IMP_DISJ_THM;
     val imp_th2a = SPECL [nb, t2] IMP_DISJ_THM
     val imp_th2b = SUBST_CONV [nnb |-> (SPEC b (CONJUNCT1 NOT_CLAUSES))]
                     (mk_disj (nnb, t2)) (mk_disj (nnb, t2))
     val imp_th2  = TRANS imp_th2a imp_th2b
     val new_rhs = “(b ==> t1) /\ (~b ==> t2)”;
     val subst = [mk_imp(b,t1) |-> imp_th1,
                  mk_imp(nb,t2) |-> imp_th2]
     val th1 = SUBST_CONV subst new_rhs new_rhs
     val th2 = TRANS (SPECL [b,t1,t2] cond_expand) (SYM th1)
 in
    GENL [b,t1,t2] th2
 end);

fun IMP_ANTISYM_RULE th1 th2 =
  let val (ant,conseq) = dest_imp(concl th1)
  in
     MP (MP (SPEC conseq (SPEC ant imp_antisym_ax)) th1) th2
  end;

(* |- !P P' Q Q'. (~Q ==> (P <=> P')) /\ (~P' ==> (Q <=> Q')) ==>
                  (P \/ Q <=> P' \/ Q') *)
val OR_CONG = save_thm
  ("OR_CONG", (* this proof is from boolScript.sml *)
 let val P = mk_var("P",Type.bool)
     val P' = mk_var("P'",Type.bool)
     val Q = mk_var("Q",Type.bool)
     val Q' = mk_var("Q'",Type.bool)
     val notQ = mk_neg Q
     val notP' = mk_neg P'
     val PorQ = mk_disj(P,Q)
     val P'orQ' = mk_disj(P',Q')
     val PeqP'= mk_eq(P,P')
     val QeqQ'= mk_eq(Q,Q')
     val ctm1 = mk_imp(notQ,PeqP')
     val ctm2 = mk_imp(notP',QeqQ')
     val th1 = ASSUME PorQ
     val th2 = ASSUME P
     val th3 = ASSUME Q
     val th4 = ASSUME ctm1
     val th5 = ASSUME ctm2
     val th6 = SUBS [SPEC Q (CONJUNCT1 NOT_CLAUSES)]
                    (SUBS [SPECL[notQ, PeqP'] IMP_DISJ_THM] th4)
     val th7 = SUBS [SPEC P' (CONJUNCT1 NOT_CLAUSES)]
                    (SUBS [SPECL[notP', QeqQ'] IMP_DISJ_THM] th5)
     val th8 = ASSUME P'
     val th9 = DISJ1 th8 Q'
     val th10 = ASSUME QeqQ'
     val th11 = SUBS [th10] th3
     val th12 = DISJ2 P' th11
     val th13 = ASSUME PeqP'
     val th14 = MK_COMB(REFL(mk_const("\\/",bool-->bool-->bool)),th13)
     val th15 = EQ_MP (MK_COMB (th14,th10)) th1
     val th16 = DISJ_CASES th6 th12 th15
     val th17 = DISCH PorQ (DISJ_CASES th7 th9 th16)
     val th18 = ASSUME P'orQ'
     val th19 = DISJ2 P th3
     val th20 = DISJ1 (SUBS [SYM th13] th8) Q
     val th21 = EQ_MP (SYM (MK_COMB(th14,th10))) th18
     val th22 = DISJ_CASES th7 th20 th21
     val th23 = DISCH P'orQ' (DISJ_CASES th6 th19 th22)
     val th24 = IMP_ANTISYM_RULE th17 th23
     val th25 = SUBS [SPECL [ctm1,ctm2,concl th24] and_imp_intro]
                     (DISCH ctm1 (DISCH ctm2 th24))
 in
   GENL [P,P',Q,Q'] th25
 end);
(* NOTE: COND_EXPAND_IMP and OR_CONG were reported by hol-bag *)

val exists_refl = hd(amatch ``?x. x = a``)

(* |- ?rep. TYPE_DEFINITION ($= ARB) rep *)
val itself_tydef = prim_type_definition({Thy="prove_base_assums",Tyop="itself"},
  SPEC boolSyntax.arb exists_refl |> CONV_RULE(QUANT_CONV SYM_CONV))

val _ = Parse.hide "the_value";
val the_value_def = new_definition
  ("the_value_def", ``the_value = (ARB:'a prove_base_assums$itself)``);

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

(* |- !(e :'b). ?(f :'a prove_base_assums$itself -> 'b).
        f (the_value :'a prove_base_assums$itself) = e
 *)
val itself_Axiom = store_thm
  ("itself_Axiom", ``!(e :'b). ?f. f the_value = e``,
  gen_tac
  \\ qexists_tac`\x. e`
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ REFL_TAC);

(* |- RES_FORALL = (\p m. !x. x IN p ==> m x) *)
val RES_FORALL_DEF = new_definition("RES_FORALL_DEF",concl boolTheory.RES_FORALL_DEF);

(* |- RES_EXISTS = (\p m. ?x. x IN p /\ m x) *)
val RES_EXISTS_DEF = new_definition("RES_EXISTS_DEF",concl boolTheory.RES_EXISTS_DEF);

(* |- RES_EXISTS_UNIQUE =
      (\p m. (?x::p. m x) /\ !x y::p. m x /\ m y ==> x = y)
 *)
val RES_EXISTS_UNIQUE_DEF = new_definition("RES_EXISTS_UNIQUE_DEF",
  concl boolTheory.RES_EXISTS_UNIQUE_DEF
  |> Term.subst [boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF),
                 boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]);

(* |- RES_SELECT = (\p m. @x. x IN p /\ m x) *)
val RES_SELECT_DEF = new_definition("RES_SELECT_DEF",concl boolTheory.RES_SELECT_DEF);

(* |- !P f. RES_FORALL P f <=> !x. x IN P ==> f x *)
val RES_FORALL_THM = store_thm("RES_FORALL_THM",
  Term.subst [boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]
    (concl boolTheory.RES_FORALL_THM),
  PURE_REWRITE_TAC[RES_FORALL_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

(* |- !P f. RES_EXISTS P f <=> ?x. x IN P /\ f x *)
val RES_EXISTS_THM = store_thm("RES_EXISTS_THM",
  Term.subst [boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF)]
    (concl boolTheory.RES_EXISTS_THM),
  PURE_REWRITE_TAC[RES_EXISTS_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

val not_exists_thm = hd (amatch ``~(?x. p x) <=> _``);
val and_F = hd(amatch``t /\ F <=> _``);

(* |- (?x::P. F) <=> F *)
val RES_EXISTS_FALSE = store_thm
  ("RES_EXISTS_FALSE",
  Term.subst [boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF)]
    (concl boolTheory.RES_EXISTS_FALSE),
    PURE_REWRITE_TAC [RES_EXISTS_DEF]
 >> NTAC 2 (CONV_TAC(DEPTH_CONV BETA_CONV))
 >> PURE_REWRITE_TAC [and_F, iff_F]
 >> PURE_REWRITE_TAC [BETA_RULE (SPEC “\x:'a. F” not_exists_thm)]
 >> GEN_TAC
 >> PURE_REWRITE_TAC [not_F, truth]);

(* |- (!x::P. T) <=> T *)
val RES_FORALL_TRUE = store_thm
  ("RES_FORALL_TRUE",
  Term.subst [boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]
    (concl boolTheory.RES_FORALL_TRUE),
    PURE_REWRITE_TAC [RES_FORALL_DEF]
 >> NTAC 2 (CONV_TAC(DEPTH_CONV BETA_CONV))
 >> PURE_REWRITE_TAC [imp_T, iff_T]
 >> GEN_TAC
 >> PURE_REWRITE_TAC [truth]);
(* NOTE: RES_EXISTS_FALSE and RES_FORALL_TRUE were reported by hol-res-quan *)

(* !P f. RES_SELECT P f = @x. x IN P /\ f x *)
val RES_SELECT_THM = store_thm("RES_SELECT_THM",
  Term.subst [boolSyntax.res_select_tm |-> lhs(concl RES_SELECT_DEF)]
    (concl boolTheory.RES_SELECT_THM),
  PURE_REWRITE_TAC[RES_SELECT_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

(* |- P = Q ==>
     (!x. x IN Q ==> (f x <=> g x)) ==>
     (RES_FORALL P f <=> RES_FORALL Q g)
 *)
val RES_FORALL_CONG = store_thm("RES_FORALL_CONG",
  Term.subst [boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]
    (concl boolTheory.RES_FORALL_CONG),
  disch_then SUBST_ALL_TAC
  \\ PURE_REWRITE_TAC[RES_FORALL_THM]
  \\ strip_tac
  \\ PURE_REWRITE_TAC[eq_imp_thm]
  \\ conj_tac \\ rpt strip_tac
  \\ rpt (first_x_assum(qspec_then`x`mp_tac))
  \\ PURE_ASM_REWRITE_TAC[T_imp]
  \\ disch_then SUBST_ALL_TAC
  \\ disch_then ACCEPT_TAC);

(* |- P = Q ==>
     (!x. x IN Q ==> (f x <=> g x)) ==>
     (RES_EXISTS P f <=> RES_EXISTS Q g)
 *)
val RES_EXISTS_CONG = store_thm("RES_EXISTS_CONG",
  Term.subst [boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF)]
    (concl boolTheory.RES_EXISTS_CONG),
  disch_then SUBST_ALL_TAC
  \\ PURE_REWRITE_TAC[RES_EXISTS_THM]
  \\ strip_tac
  \\ PURE_REWRITE_TAC[eq_imp_thm]
  \\ conj_tac \\ rpt strip_tac
  \\ qexists_tac`x`
  \\ rpt (first_x_assum(qspec_then`x`mp_tac))
  \\ PURE_ASM_REWRITE_TAC[T_imp,T_and,iff_T,T_iff]
  \\ disch_then ACCEPT_TAC);

(* |- !P f.
         RES_EXISTS_UNIQUE P f <=>
         (?x::P. f x) /\ !x y::P. f x /\ f y ==> x = y
 *)
val RES_EXISTS_UNIQUE_THM = store_thm("RES_EXISTS_UNIQUE_THM",
  Term.subst [boolSyntax.res_exists1_tm |-> lhs(concl RES_EXISTS_UNIQUE_DEF),
              boolSyntax.res_exists_tm |-> lhs(concl RES_EXISTS_DEF),
              boolSyntax.res_forall_tm |-> lhs(concl RES_FORALL_DEF)]
    (concl boolTheory.RES_EXISTS_UNIQUE_THM),
  PURE_REWRITE_TAC[RES_EXISTS_UNIQUE_DEF]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ rpt gen_tac \\ REFL_TAC);

(* |- ?f.
         (!p m x. x IN p ==> RES_ABSTRACT p m x = m x) /\
         !p m1 m2.
             (!x. x IN p ==> m1 x = m2 x) ==>
             RES_ABSTRACT p m1 = RES_ABSTRACT p m2
 *)
val RES_ABSTRACT_EXISTS = prove(
  let
    val fvar = mk_var("f",type_of boolSyntax.res_abstract_tm)
  in
    mk_exists(fvar, Term.subst [boolSyntax.res_abstract_tm|->fvar]
                      (concl boolTheory.RES_ABSTRACT_DEF))
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

val _ = List.app (Theory.delete_binding o #1) (axioms "-");
val _ = List.app (Theory.delete_binding o #1) (definitions "-");

(* |- (!p m x. x IN p ==> RES_ABSTRACT p m x = m x) /\
      !p m1 m2.
          (!x. x IN p ==> m1 x = m2 x) ==>
          RES_ABSTRACT p m1 = RES_ABSTRACT p m2
 *)
val RES_ABSTRACT_DEF = new_specification
  ("RES_ABSTRACT_DEF", ["RES_ABSTRACT"], RES_ABSTRACT_EXISTS);

(* |- !t1 t2. (t1 <=> t2) <=> t1 /\ t2 \/ ~t1 /\ ~t2 (EQ_EXPAND)

   reported by src/real/prove_real_assumsScript.sml

   input theorems: NOT_CLAUSES, EQ_CLAUSES, OR_CLAUSES, AND_CLAUSES,
                   BOOL_CASES_AX
 *)
val EQ_EXPAND = save_thm("EQ_EXPAND",
let val t1 = “t1:bool” and t2 = “t2:bool”
    val conj = “$/\”   and disj = “$\/”
    val [NOT1,NOT2] = tl (CONJUNCTS NOT_CLAUSES)
    and [EQ1,EQ2,EQ3,EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
    and [OR1,OR2,OR3,OR4,_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL (CONJUNCTS(SPEC_ALL AND_CLAUSES))
    val thTl = SPEC t2 EQ1
    and thFl = SPEC t2 EQ3
    val thTr = TRANS (MK_COMB (AP_TERM disj (SPEC t2 AND1),
                               TRANS (AP_THM (AP_TERM conj NOT1) (mk_neg t2))
                                     (SPEC (mk_neg t2) AND3)))
                     (SPEC t2 OR4)
    and thFr = TRANS (MK_COMB (AP_TERM disj (SPEC t2 AND3),
                               TRANS (AP_THM (AP_TERM conj NOT2) (mk_neg t2))
                                     (SPEC (mk_neg t2) AND1)))
                     (SPEC (mk_neg t2) OR3)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = “(t1 = t2) <=> (t1 /\ t2) \/ (~t1 /\ ~t2)”
    val thT2 = SUBST_CONV [t1 |-> ASSUME “t1 = T”] tm tm
    and thF2 = SUBST_CONV [t1 |-> ASSUME “t1 = F”] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [t1,t2] (DISJ_CASES (SPEC t1 BOOL_CASES_AX) thT3 thF3)
 end);

val _ = export_theory ();
