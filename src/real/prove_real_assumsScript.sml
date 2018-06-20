open HolKernel boolLib bossLib Opentheory realaxTheory realTheory

val Thy = "prove_real_assums";

val _ = new_theory Thy;

val REAL_0 = new_definition("REAL_0",concl realTheory.REAL_0);
val REAL_1 = new_definition("REAL_1",concl realTheory.REAL_1);
val _ = new_constant("inv",``:real -> real``);
val inv0_def = new_definition("inv0_def",``inv0 x = if x = 0 then 0 else inv x``);
val _ = new_constant("/",``:real -> real -> real``);
val real_div_def = new_definition("real_div_def",``real_div x y = if y = 0 then 0 else prove_real_assums$/ x y``);

val _ = new_constant("hol-real-assums-1.0",alpha);

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
  | const_name (["Number","Real"],"fromNatural") = {Thy="real",Name="real_of_num"}
  | const_name (["Number","Real"],"inv") = {Thy=Thy,Name="inv"}
  | const_name (["Number","Real"],"<") = {Thy="realax",Name="real_lt"}
  | const_name (["Number","Real"],">") = {Thy="real",Name="real_gt"}
  | const_name (["Number","Real"],">=") = {Thy="real",Name="real_ge"}
  | const_name (["Number","Real"],"<=") = {Thy="real",Name="real_lte"}
  | const_name (["Number","Real"],"*") = {Thy="realax",Name="real_mul"}
  | const_name (["Number","Real"],"+") = {Thy="realax",Name="real_add"}
  | const_name (["Number","Real"],"-") = {Thy="real",Name="real_sub"}
  | const_name (["Number","Real"],"~") = {Thy="realax",Name="real_neg"}
  | const_name (["Number","Real"],"/") = {Thy=Thy,Name="/"}
  | const_name (["Number","Real"],"max") = {Thy="real",Name="max"}
  | const_name (["Number","Real"],"min") = {Thy="real",Name="min"}
  | const_name (["Number","Real"],"abs") = {Thy="real",Name="abs"}
  | const_name (["Number","Real"],"^") = {Thy="real",Name="pow"}
  | const_name (["Number","Natural"],"zero") = {Thy="num",Name="0"}
  | const_name (["Number","Natural"],"suc") = {Thy="num",Name="SUC"}
  | const_name (["Number","Natural"],"bit1") = {Thy="arithmetic",Name="BIT1"}
  | const_name (["HOL4","realax"],"real_0") = {Thy=Thy,Name="real_0"}
  | const_name (["HOL4","realax"],"real_1") = {Thy=Thy,Name="real_1"}
  | const_name (["HOL4","realax"],"inv") = {Thy=Thy,Name="inv0"}
  | const_name (["HOL4","real"],"/") = {Thy=Thy,Name="real_div"}
  | const_name (ns,n) = {Thy=Thy,Name=String.concatWith "_"(ns@[n])}
fun tyop_name ([],"bool") = {Thy="min",Tyop="bool"}
  | tyop_name ([],"->") = {Thy="min",Tyop="fun"}
  | tyop_name ([],"ind") = {Thy="min",Tyop="ind"}
  | tyop_name (["Number","Real"],"real") = {Thy="realax",Tyop="real"}
  | tyop_name (["Number","Natural"],"natural") = {Thy="num",Tyop="num"}
  | tyop_name (ns,n) = {Thy=Thy,Tyop=String.concatWith "_"(ns@[n])}

local
  fun mk_rep_abs {name,ax,args,rep,abs} =
    let
      val abs = ``real_ABS``
      val rep = ``real_REP``
      val P = rator(concl ax)
    in
      {abs_rep = mk_thm([],``(\a. ^abs (^rep a)) = (\a. a)``),
       rep_abs = mk_thm([],``(\r. ^rep (^abs r) = r) = (\r. P r)``)}
    end
in
  val (reader:reader) = {
    define_tyop = mk_rep_abs,
    define_const = fn x => fn th => REFL T,
    axiom = fn _ => mk_thm,
    const_name = const_name,
    tyop_name = tyop_name}
end

val goalsNet = read_article "hol4-real-assums.art" reader;
val goals = map concl (Net.listItems goalsNet)

(*
  Theorems in OpenTheory real-1.61 package
  (could be read in via article for more robustness)

  |- !x. x <= x
  |- !x. 0 + x = x
  |- !x. x ^ 0 = 1
  |- !x. ~x + x = 0
  |- !x. 1 * x = x
  |- !x y. x > y <=> y < x
  |- !x y. x >= y <=> y <= x
  |- !x y. x * y = y * x
  |- !x y. x + y = y + x
  |- !x y. x <= y \/ y <= x
  |- !x y. x < y <=> ~(y <= x)
  |- !x y. x - y = x + ~y
  |- !m n. fromNatural m = fromNatural n <=> m = n
  |- !m n. fromNatural m <= fromNatural n <=> m <= n
  |- !x. abs x = if 0 <= x then x else ~x
  |- !m n. fromNatural m * fromNatural n = fromNatural (m * n)
  |- !m n. fromNatural m + fromNatural n = fromNatural (m + n)
  |- !x n. x ^ suc n = x * x ^ n
  |- !m n. max m n = if m <= n then n else m
  |- !m n. min m n = if m <= n then m else n
  |- !x y. x <= y /\ y <= x <=> x = y
  |- !x y z. y <= z ==> x + y <= x + z
  |- !x y z. x * (y * z) = x * y * z
  |- !x y z. x + (y + z) = x + y + z
  |- !x y z. x <= y /\ y <= z ==> x <= z
  |- !x. ~(x = 0) ==> inv x * x = 1
  |- !x y. ~(y = 0) ==> x / y = x * inv y
  |- !x y z. x * (y + z) = x * y + x * z
  |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x * y
  |- !s x.
       ~(s = {}) /\ (?m. !x. member x s ==> x <= m) /\ member x s ==>
       x <= sup s
  |- !s m.
       ~(s = {}) /\ (?m. !x. member x s ==> x <= m) /\
       (!x. member x s ==> x <= m) ==> sup s <= m
  |- !p.
       (?x. p x) /\ (?m. !x. p x ==> x <= m) ==>
       ?s. (!x. p x ==> x <= s) /\ !m. (!x. p x ==> x <= m) ==> s <= m

*)

val real_lt = CONV_RULE SWAP_FORALL_CONV realTheory.real_lt;
val () = Thm.delete_proof real_lt;

val REAL_MUL_LINV = mk_thm([],
  subst[prim_mk_const{Thy="realax",Name="inv"} |-> prim_mk_const{Thy=Thy,Name="inv"}]
  (concl realTheory.REAL_MUL_LINV))

val real_div0 = mk_thm([],
  ``!x y. ~(y = 0) ==> (prove_real_assums$/ x y = x * prove_real_assums$inv y)``);

val th1 = store_thm("th1",el 1 goals,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[real_lt]
  \\ reverse(qspecl_then[`x`,`y`]strip_assume_tac REAL_LE_TOTAL)
  >- asm_simp_tac bool_ss []
  \\ reverse(qspecl_then[`y`,`z`]strip_assume_tac REAL_LE_TOTAL)
  >- asm_simp_tac bool_ss []
  \\ rpt strip_tac
  \\ imp_res_tac REAL_LE_TRANS);

val th2 = store_thm("th2",el 2 goals,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[real_lt]
  \\ reverse(qspecl_then[`y`,`z`]strip_assume_tac REAL_LE_TOTAL)
  >- asm_simp_tac bool_ss []
  \\ rpt strip_tac
  \\ `x + y <= x + z` by metis_tac[REAL_LE_LADD_IMP]
  \\ `x + z = x + y` by metis_tac[REAL_LE_ANTISYM]
  \\ `~x + x + z = ~x + x + y` by metis_tac[REAL_ADD_ASSOC]
  \\ `z = y` by metis_tac[REAL_ADD_LID,REAL_ADD_LINV]
  \\ metis_tac[REAL_LE_ANTISYM]);

val REAL_ADD_LID_UNIQ = prove(
  ``! x y. (x + y = y) = (x = 0)``,
  metis_tac[REAL_ADD_LID,REAL_ADD_SYM,REAL_ADD_LINV,REAL_ADD_ASSOC]);

val REAL_MUL_LZERO = prove(
  ``!x. 0 * x = 0``,
  metis_tac[REAL_ADD_LID_UNIQ,REAL_ADD_LID,REAL_LDISTRIB,REAL_MUL_SYM])

val REAL_ENTIRE = prove(
  ``!x y. (x * y = 0) = (x = 0) \/ (y = 0)``,
  metis_tac[REAL_MUL_LINV,REAL_MUL_LID,REAL_MUL_ASSOC,REAL_MUL_LZERO,REAL_MUL_SYM]);

val th3 = store_thm("th3",el 3 goals,
  rpt gen_tac
  \\ PURE_REWRITE_TAC[real_lt,REAL_0]
  \\ qspecl_then[`x`,`0`]strip_assume_tac REAL_LE_TOTAL >- asm_simp_tac bool_ss []
  \\ qspecl_then[`y`,`0`]strip_assume_tac REAL_LE_TOTAL >- asm_simp_tac bool_ss []
  \\ `0 <= x * y` by imp_res_tac REAL_LE_MUL
  \\ rpt strip_tac
  \\ `x * y = 0` by metis_tac[REAL_LE_ANTISYM]
  \\ metis_tac[REAL_ENTIRE,REAL_LE_REFL]);

val th4 = store_thm("th4",el 4 goals,
  metis_tac[real_lt,REAL_LE_TOTAL,REAL_LE_ANTISYM])

val otax = mk_thm([],
  ``!p. (?(x:real). p x) /\ (?m. !x. p x ==> x <= m) ==>
        ?s. (!x. p x ==> x <= s) /\ !m. (!x. p x ==> x <= m) ==> s <= m``);

val REAL_LE_LT = prove(
  ``!x y. x <= y = x < y \/ (x = y)``,
  metis_tac[real_lt,REAL_LE_TOTAL,REAL_LE_ANTISYM]);

val th5 = store_thm("th5",el 5 goals,
  rpt strip_tac
  \\ qspec_then`P`mp_tac otax
  \\ impl_tac >- metis_tac[REAL_LE_LT]
  \\ strip_tac
  \\ qexists_tac`s`
  \\ gen_tac
  \\ EQ_TAC \\ strip_tac
  >- metis_tac[th1,REAL_LE_LT]
  \\ metis_tac[REAL_LE_TOTAL,REAL_LE_LT,real_lt]);

val th6 = store_thm("th6",el 6 goals,
  metis_tac[REAL_MUL_LINV,REAL_0,REAL_1,inv0_def]);

val th7 = store_thm("th7",el 7 goals,
  metis_tac[realTheory.REAL_ADD_LINV,REAL_0]);

val th8 = store_thm("th8",el 8 goals,
  metis_tac[realTheory.REAL_ADD_LID,REAL_0]);

val th9 = store_thm("th9",el 9 goals,
  metis_tac[realTheory.REAL_MUL_LID,REAL_1]);

val th10 = store_thm("th10",el 10 goals,
  simp_tac bool_ss [real_lt,REAL_LE_REFL]);

val (pow0,powsuc) = CONJ_PAIR realTheory.pow;
val () = Thm.delete_proof pow0
val () = Thm.delete_proof powsuc

val th11 = store_thm("th11",el 11 goals,
  MATCH_ACCEPT_TAC(CONJ pow0 powsuc));

val th12 = store_thm("th12",el 12 goals,
  REWRITE_TAC[REAL_0,REAL_1,REAL_OF_NUM_ADD,arithmeticTheory.ADD1]);

val th13 = store_thm("th13",el 13 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM,abs]);

val th14 = store_thm("th14",el 14 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM,min_def]);

val th15 = store_thm("th15",el 15 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM,max_def]);

val th16 = store_thm("th16",el 16 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM,real_sub]);

val th17 = store_thm("th17",el 17 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM,real_div_def,inv0_def]
  \\ metis_tac[real_div0,REAL_MUL_LZERO,REAL_MUL_SYM]);

val th18 = store_thm("th18",el 18 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM]
  \\ metis_tac[real_lt]);

val th19 = store_thm("th19",el 19 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM,real_ge]);

val th20 = store_thm("th20",el 20 goals,
  SIMP_TAC bool_ss [FUN_EQ_THM,real_gt]);

val th21 = store_thm("th21",el 21 goals,
  metis_tac[inv0_def,REAL_0]);

val th22 = store_thm("th22",el 22 goals,
  PURE_REWRITE_TAC[REAL_0,REAL_1,REAL_OF_NUM_EQ,
    arithmeticTheory.ONE,prim_recTheory.SUC_ID]
  \\ strip_tac);

val _ = export_theory();
