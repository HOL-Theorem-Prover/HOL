(*=====================================================================  *)
(* FILE          : quantHeuristicsLibFunRemove.sml                       *)
(* DESCRIPTION   : some auxiliary functionality that allows to get rid   *)
(*                 of certain function applications to quantified        *)
(*                 variables                                             *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : Oct 2012                                              *)
(* ===================================================================== *)


structure quantHeuristicsLibFunRemove :> quantHeuristicsLibFunRemove =
struct

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/src/quantHeuristics"])::
            !loadPath;

map load ["quantHeuristicsTheory"];
load "ConseqConv"
show_assums := true;
quietdec := true;
*)

open HolKernel Parse boolLib Drule ConseqConv simpLib
     quantHeuristicsTheory quantHeuristicsTools


(*
quietdec := false;
*)

val std_ss = numLib.std_ss

(*
val t = ``?n3 n2 n1. P(n3 - 3,  n2) /\ n3 - 3 > c /\ c < n2 + n1``
val thm = prove (``IS_REMOVABLE_QUANT_FUN (\n:num. n - c)``,
  SIMP_TAC std_ss [IS_REMOVABLE_QUANT_FUN_def] THEN GEN_TAC THEN
  Q.EXISTS_TAC `v + c` THEN
  SIMP_TAC std_ss []);

val rws = [HEAP_READ_ENTRY_EARLY_EVAL]

*)

fun postfix_name_fun p s = String.concat [s,"_",p]


fun QUANT_FUN_REMOVE_apply_thm nf rws thm v qb =
let
   val (i, thm') = let 
     val (v', i') = dest_abs (rand (concl thm)) 
     val s = match_term v' v
     val thm' = INST_TY_TERM s thm
     val i = subst (fst s) (inst (snd s) i')
   in 
     (i, thm')
   end;

   val (ic, s) = 
     let 
       val v_set = (HOLset.add(empty_varset,v));
       val mf = match_terml [] v_set i     
       val ic = find_term (can mf) qb
       val s = mf ic
     in (ic, s) end

   val n_v = genvar (type_of ic);
   fun all_removed_check t = not (free_in v (subst [ic |-> n_v] t))

   fun check_removed_conv conv tm =
      if all_removed_check tm then raise UNCHANGED else
      (TRY_CONV conv THENC
       TRY_CONV (CHANGED_CONV (SUB_CONV (check_removed_conv conv)))) tm

   fun check_convs convs t =
     tryfind (fn c => 
        let val thm = (CHANGED_CONV c) t;
        val _ = if (all_removed_check (rhs (concl thm))) then () else fail();
        in thm end) convs
   val qb_thm1 = check_removed_conv (check_convs rws) qb handle HOL_ERR _ => REFL qb
                                                              | UNCHANGED => REFL qb

   val qb' = rhs (concl qb_thm1)
   val _ = if all_removed_check qb' then () else (print_term qb';fail())
   val qb'' = mk_comb (mk_abs(n_v, subst [ic |-> n_v] qb'), ic)

   val qb_thm2 = prove (mk_eq (qb'', qb'), SIMP_TAC std_ss[]);
   val qb_thm = TRANS qb_thm2 (GSYM qb_thm1)
   val thm'' = INST_TY_TERM s thm'
   val v' = mk_var (nf (fst (dest_var v)), type_of ic)
in
  (thm'', qb_thm, v')
end;

(*
val rem_thm = prove (``IS_REMOVABLE_QUANT_FUN (\n:num. n - 3)``,
  SIMP_TAC std_ss [thm])  
val v' = genvar numty
val qb' = subst [[``n3:num - 3``]]

val remove_funL = [QUANT_FUN_REMOVE_apply_thm nf rws thm];
*)

fun QUANT_FUN_REMOVE_CONV_base remove_funL t =
let
   val is_ex = is_exists t
   val _ = if (not is_ex) andalso (not (is_forall t)) then raise UNCHANGED else ();

   val (vs,qb) = (if is_ex then strip_exists else strip_forall) t;
   val v = hd vs

   val (thm', qb_thm, v') = tryfind (fn f => f v qb) remove_funL;

   val f = rand (concl thm')

   val P = rator (lhs (concl qb_thm))
   val inst_thm = if is_ex then IS_REMOVABLE_QUANT_FUN___EXISTS_THM else IS_REMOVABLE_QUANT_FUN___FORALL_THM
   val inst_thm1 = MP (ISPEC P (ISPEC f inst_thm)) thm'
   val inst_thm2 = CONV_RULE 
                     (LHS_CONV (
                        RAND_CONV (RENAME_VARS_CONV [fst (dest_var v)]) THENC
                        QUANT_CONV (
                          (RAND_CONV BETA_CONV) THENC (K qb_thm))
                      ) THENC
                      RHS_CONV (
                        RAND_CONV (RENAME_VARS_CONV [fst (dest_var v')]) THENC
                        QUANT_CONV BETA_CONV)
                      ) inst_thm1
  val move_CONV = if is_ex then SWAP_EXISTS_CONV else SWAP_FORALL_CONV
  val intro_RULE = if is_ex then EQ_EXISTS_INTRO else EQ_FORALL_INTRO
  val dest_q = if is_ex then dest_exists else dest_forall

  fun move_to_end t =
  let
     val thm1 = move_CONV t;
     val (top_var, r_term) = dest_q (rhs (concl thm1));
     val thm2 = move_to_end r_term;
     val thm3 = intro_RULE (top_var, thm2);
  in
     TRANS thm1 thm3
  end handle HOL_ERR _ => inst_thm2;
  val final_thm = move_to_end t
in
  final_thm
end

type quant_fun_remove_arg = thm * (string -> string) * conv list

fun QUANT_FUN_REMOVE_CONV (args:quant_fun_remove_arg list) =
  let
     fun process_arg (thm, rn, convs) = QUANT_FUN_REMOVE_apply_thm rn  convs thm
  in
     (QUANT_FUN_REMOVE_CONV_base (map process_arg args)):conv
  end;

fun QUANT_FUN_REMOVE_ss args =
  std_conv_ss { name = "QAUNT_FUN_REMOVE_CONV",
                pats = [``?x. P x``, ``!x. P x``],
                conv = QUANT_FUN_REMOVE_CONV args}

fun remove_thm_arg thm post rewr =
  (thm, postfix_name_fun post, map REWR_CONV (flatten (map BODY_CONJUNCTS rewr))):quant_fun_remove_arg

end
