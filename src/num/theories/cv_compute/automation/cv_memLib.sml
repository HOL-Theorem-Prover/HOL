(*
  The cv translator's state is handled by this Lib file
*)
structure cv_memLib :> cv_memLib =
struct

open HolKernel Abbrev Parse boolLib bossLib;
open cv_miscLib cv_repTheory cvTheory;

datatype verbosity = Silent | Quiet | Verbose;

fun verbosity_leq Silent _ = true
  | verbosity_leq Quiet Quiet = true
  | verbosity_leq Quiet Verbose = true
  | verbosity_leq Verbose Verbose = true
  | verbosity_leq _ _ = false;

val verbosity_level = ref Quiet;

val use_long_names = ref false;

fun cv_print_aux v f s =
    if verbosity_leq v (!verbosity_level) then Feedback.HOL_INFO (f s) else ();
fun cv_print v s = cv_print_aux v I s;
fun cv_print_term v tm = cv_print_aux v term_to_string tm;
fun cv_print_thm v th = cv_print_aux v thm_to_string th;

(* Custom version of Lib.time *)
local open Time; in
fun cv_time f x =
  let val start = Time.now()
      val res = f x
      val finish = Time.now()
  in
    cv_print Verbose ("Took " ^ Time.fmt 1 (finish - start) ^ " seconds.\n");
    res
  end
end

fun indent_print_aux f verbosity prefix suffix x = let
  val m = !max_print_depth
  fun change #"\n" = "\n  "
    | change c = implode [c]
  fun indent_print s = cv_print verbosity (String.translate change s)
  in (cv_print verbosity (prefix ^ "  ");
      max_print_depth := 15;
      indent_print (f x);
      max_print_depth := m;
      cv_print verbosity suffix)
     handle HOL_ERR _ =>
      max_print_depth := m end;

val indent_print_term = indent_print_aux term_to_string;
val indent_print_thm = indent_print_aux thm_to_string;

(*--------------------------------------------------------------------------*
   Reused function
 *--------------------------------------------------------------------------*)

fun register_ThmSetData_list tag_name uptodate update_fun = let
  fun update_fun_append th ths = update_fun th @ ths
  fun apply_delta (ThmSetData.ADD(_, th)) xs = update_fun_append th xs
    | apply_delta _                       xs = xs;
  val { get_global_value = the_list, update_global_value = updater, ... } =
      ThmSetData.export_with_ancestry {
        settype = tag_name,
        delta_ops = {apply_to_global = apply_delta,
                     uptodate_delta = K true,
                     thy_finaliser = NONE,
                     initial_value = [],
                     apply_delta = apply_delta}
      };
  (* A full revert (delete_const/delete_binding/scrub) leaves stale ADD
     deltas in the live global list, which export_with_ancestry never
     prunes.  Dropping them via prune makes them unmatchable, so a later
     translation over the same datatype cleanly re-derives fresh ones.
     Pruning is the reverter's job; lookups stay O(1). *)
  fun prune () = updater (List.filter uptodate)
  in (the_list, fn th => updater (update_fun_append th), prune) end;

(*--------------------------------------------------------------------------*
   Reformulate in terms of cv_rep (for use by cv_repLib and cv_transLib)
 *--------------------------------------------------------------------------*)

fun formulate_cv_rep th =
  if is_cv_rep (th |> UNDISCH_ALL |> concl) then th else let
  val th0 = (if is_imp (concl th) then th else DISCH T th)
  val th1 = th0 |> CONV_RULE (REWR_CONV (GSYM cv_rep_def))
  val cv_tm = cv_rep_cv_tm (concl th1)
  val cv_vs = cv_tm |> free_vars
  val hol_vs = cv_rep_hol_tm (concl th1) |> free_vars
  val joint = filter (fn v => List.exists (aconv v) hol_vs) cv_vs
  fun lift_each [] th = th
    | lift_each (v::vs) th1 = let
    val name = dest_var v |> fst
    val p = mk_var("p_" ^ name, bool)
    val cv = mk_var("cv_" ^ name, cvSyntax.cv)
    val t = find_term (fn tm => is_comb tm andalso aconv (rand tm) v) cv_tm
    val th2 = th1 |> CONV_RULE (cv_rep_cv_tm_conv (UNBETA_CONV t))
    val th3 = MATCH_MP cv_rep_assum th2 |> SPECL [cv,p] |> UNDISCH
    val th4 = th3 |> CONV_RULE (cv_rep_cv_tm_conv BETA_CONV)
    in lift_each vs th4 end
  val th7 = lift_each joint th1
  val th8 = th7 |> DISCH_ALL
                |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  in th8 end;

fun formulate_cv_reps th = let
  val thms = CONJUNCTS (SPEC_ALL th)
  in map formulate_cv_rep thms end

fun show_cv_rep cv_rep_th = let
  val pat = cv_rep_th |> UNDISCH_ALL |> concl |> rand
  val s = map (fn v => v |-> mk_var("_",type_of v)) (free_vars pat)
  val _ = (cv_print Verbose "Able to translate: ";
           cv_print_term Verbose (subst s pat))
  in (pat, cv_rep_th) end

fun prepare th = let
  val cv_rep_thms = formulate_cv_reps th
  in map show_cv_rep cv_rep_thms end

(*--------------------------------------------------------------------------*
   Database for cv_rep, cv_pre, cv_inline, cv_from_to
 *--------------------------------------------------------------------------*)

fun insert_cv_rep th = prepare th;
val (cv_rep_thms, _, cv_rep_prune) =
    register_ThmSetData_list "cv_rep" (Theory.uptodate_thm o snd)
                             insert_cv_rep;

fun insert_cv_pre th = (
  cv_print Verbose "\ncv_pre:\n\n";
  cv_print_thm Verbose th;
  cv_print Verbose "\n\n"; [th])
val (cv_pre_thms, cv_pre_add, cv_pre_prune) =
    register_ThmSetData_list "cv_pre" Theory.uptodate_thm insert_cv_pre;

fun insert_cv_inline th = (
  cv_print Verbose "\ncv_inline:\n\n";
  cv_print_thm Verbose th;
  cv_print Verbose "\n\n"; [th])
val (cv_inline_thms, cv_inline_add, cv_inline_prune) =
    register_ThmSetData_list "cv_inline" Theory.uptodate_thm
                             insert_cv_inline;

fun insert_cv_from_to th = (
  cv_print Verbose "\ncv_from_to:\n\n";
  cv_print_thm Verbose th;
  cv_print Verbose "\n\n"; [th])
val (cv_from_to_thms, cv_from_to_add, cv_from_to_prune) =
    register_ThmSetData_list "cv_from_to" Theory.uptodate_thm
                             insert_cv_from_to;

(* For callers that delete constants/types from the current theory:
   drop the theorem-set entries the deletion made stale.  Gated on the
   kernel's retire epoch, as in ThmSetData and AncestryData: an entry
   goes out of date only when a constant or type operator it mentions
   is retired, and every retirement stamps the epoch from a monotone
   process-global counter, so an unchanged epoch means no entry can
   have gone stale since the last sweep. *)
val last_prune_epoch : int list ref = ref []
fun prune_stale_entries () =
  let val cur = [Type.type_epoch (), Term.term_epoch ()] in
    if !last_prune_epoch = cur then ()
    else (cv_rep_prune (); cv_pre_prune (); cv_inline_prune ();
          cv_from_to_prune (); last_prune_epoch := cur)
  end;

end
