(* ========================================================================= *)
(* FILE          : mleCombinProve.sml                                        *)
(* DESCRIPTION   : Verifying a combinator witness for a head normal form     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleCombinProve :> mleCombinProve =
struct

open HolKernel Abbrev boolLib aiLib mleCombinLib

val ERR = mk_HOL_ERR "mleCombinProve"
val selfdir = HOLDIR ^ "/examples/AI_tasks"

val cS = mk_var ("s",alpha)
val cK = mk_var ("k",alpha)
val cA = mk_var ("a",``:'a -> 'a -> 'a``)
val vx = mk_var ("X",alpha)
val vy = mk_var ("Y",alpha)
val vz = mk_var ("Z",alpha)
val v1 = mk_var ("V1",alpha)
val v2 = mk_var ("V2",alpha)
val v3 = mk_var ("V3",alpha)
val cC = mk_var ("c",alpha);

(* -------------------------------------------------------------------------
   Prove that the combinator witness has the property described by
   the head normal formal
   ------------------------------------------------------------------------- *)

fun COMBIN_PROVE (witness,headnf) =
  let
    val eq = mk_eq (list_mk_cA [cC,v1,v2,v3],headnf)
    val prop = list_mk_forall ([v1,v2,v3],eq)
    val goal = (eq_axl, subst [{redex = cC, residue = witness}] prop)
  in
    TAC_PROOF (goal, ASM_REWRITE_TAC [])
  end

(*
load "aiLib"; open aiLib;
load "mleCombinProve"; open mleCombinProve;
val witness = cK;
val headnf = list_mk_cA [v1,v3];
val thm = COMBIN_PROVE (witness,headnf);
*)

(* -------------------------------------------------------------------------
   Verify the solutions produced during evaluation.
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "mleCombinLib"; open mleCombinLib;
load "mleCombinSynt"; open mleCombinSynt;
load "mleCombinProve"; open mleCombinProve;

val dir2 = HOLDIR ^ "/examples/AI_tasks/combin_results/test_tnn_nolimit";
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val boardl = mapfilter (valOf o #3) (List.tabulate (200,g)); length boardl;
val pairl = map (fn (a,b,_) =>
  (combin_to_cterm (ignore_metavar a), combin_to_cterm b)) boardl;

val (thml,t) = add_time (map COMBIN_PROVE) pairl; length thml;

fun f_charl cl = case cl of
  [] => []
  | [a] => [a]
  | a :: b :: m => if Char.isSpace a andalso Char.isSpace b
                   then f_charl (b :: m)
                   else if Char.isSpace a
                   then #" " :: f_charl (b :: m)
                   else a :: f_charl (b :: m)
val minspace = implode o f_charl o explode;
val _ = writel (dir2 ^ "/theorems")
  (map (minspace o string_of_goal o dest_thm) thml);
*)


end (* struct *)
