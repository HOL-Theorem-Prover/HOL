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

(* The check comes first so that f x, which can pretty-print a large
   theorem, is not computed when nothing would be printed. *)
fun indent_print_aux f verbosity prefix suffix x =
  if not (verbosity_leq verbosity (!verbosity_level)) then () else let
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

fun kname_string ({Thy,Name} : KernelSig.kernelname) = Thy ^ "." ^ Name

fun register_ThmSetData tag_name apply_delta =
  ThmSetData.export_with_ancestry {
    settype = tag_name,
    delta_ops = {apply_to_global = apply_delta,
                 uptodate_delta = K true,
                 thy_finaliser = NONE,
                 initial_value = [],
                 apply_delta = apply_delta}
  };

(* The set's entries are paired with the name of the theorem they came
   from, so that REMOVE can drop them *)
fun register_ThmSetData_list tag_name update_fun = let
  fun add name th ths = map (fn x => (name, x)) (update_fun th) @ ths
  fun apply_delta (ThmSetData.ADD(knm, th)) xs = add (kname_string knm) th xs
    | apply_delta (ThmSetData.REMOVE s) xs = filter (fn (n, _) => n <> s) xs
  val { get_global_value = the_list, update_global_value = updater, ... } =
      register_ThmSetData tag_name apply_delta
  in (map #2 o the_list, fn th => updater (add "" th)) end;

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

(* A cv_rep entry: the name of the theorem it came from, the HOL term
   pattern it translates, the cv_rep theorem, and the names of the other
   entries that translate the same pattern with a different theorem.
   Such a clash can only come from two ancestors that each translated the
   pattern; it makes the pattern unusable (see cv_repLib.match_memory)
   until cv_rep_delete removes one of them. *)
type cv_rep_entry =
  {name : string, pat : term, th : thm, clashes : string list}

(* equal up to renaming of term and type variables; the head constants
   are compared first since that rules out almost every entry cheaply *)
fun same_pattern p1 p2 = let
  val h1 = fst (strip_comb p1)
  val h2 = fst (strip_comb p2)
  in
    (not (is_const h1 andalso is_const h2) orelse same_const h1 h2) andalso
    can (match_term p1) p2 andalso can (match_term p2) p1
  end

(* An entry clashes with another that translates the same pattern with a
   different theorem; the same theorem under another name is kept too (so
   that deleting one name leaves the other), but is not a clash.  Only
   the clashing entries are marked: a theorem can translate several
   patterns, and the others stay usable. *)
fun cv_rep_add_entry is_current name ((pat, th), es : cv_rep_entry list) = let
  fun clashes_with (e : cv_rep_entry) =
    same_pattern pat (#pat e) andalso not (aconv (concl (#th e)) (concl th))
  val others = map #name (filter clashes_with es)
  fun add_clash (e : cv_rep_entry) =
    if clashes_with e then
      {name = #name e, pat = #pat e, th = #th e, clashes = name :: #clashes e}
    else e
  val entry = {name = name, pat = pat, th = th, clashes = others}
  in
    if null others then entry :: es
    else if is_current then
      raise mk_HOL_ERR "cv_memLib" "cv_rep"
        (name ^ " translates " ^ term_to_string pat ^
         ", which " ^ String.concatWith " and " others ^
         " already translates; to replace it, first remove it with " ^
         "cv_transLib.cv_rep_delete " ^ Lib.quote (hd others))
    else entry :: map add_clash es
  end

fun cv_rep_remove s (es : cv_rep_entry list) = let
  fun drop_clash (e : cv_rep_entry) =
    {name = #name e, pat = #pat e, th = #th e,
     clashes = filter (fn n => n <> s) (#clashes e)}
  in map drop_clash (filter (fn e => #name e <> s) es) end

(* An entry of the current theory that clashes is an error at once; one
   from a theory being loaded is recorded as a clash instead, since the
   theory that loads it cannot act before its ancestors are loaded. *)
fun apply_cv_rep_delta (ThmSetData.ADD(knm, th)) es = let
      val name = kname_string knm
      val is_current = Thm.getCT() = SOME (#Thy knm)
      in foldr (cv_rep_add_entry is_current name) (cv_rep_remove name es)
               (prepare th)
      end
  | apply_cv_rep_delta (ThmSetData.REMOVE s) es = cv_rep_remove s es

val { get_global_value = cv_rep_entries0,
      update_global_value = cv_rep_update,
      record_delta = cv_rep_record, ... } =
    register_ThmSetData "cv_rep" apply_cv_rep_delta;

fun cv_rep_entries () = let
  fun names {clashes = [], ...} = []
    | names {name, clashes, ...} = name :: clashes
  in map (fn e => (#pat e, #th e, names e)) (cv_rep_entries0 ()) end

fun cv_rep_thms () = map (fn {pat, th, ...} => (pat, th)) (cv_rep_entries0 ())

fun cv_rep_delete s = let
  val name = kname_string (ThmSetData.toKName s)
  val d = ThmSetData.REMOVE name
  in
    if exists (fn e => #name e = name) (cv_rep_entries0 ()) then
      (cv_rep_update (apply_cv_rep_delta d); cv_rep_record d)
    else
      raise mk_HOL_ERR "cv_memLib" "cv_rep_delete"
        ("no cv_rep translation is stored under the name " ^ Lib.quote name)
  end

fun insert_cv_pre th = (
  cv_print Verbose "\ncv_pre:\n\n";
  cv_print_thm Verbose th;
  cv_print Verbose "\n\n"; [th])
val (cv_pre_thms, cv_pre_add) = register_ThmSetData_list "cv_pre" insert_cv_pre;

fun insert_cv_inline th = (
  cv_print Verbose "\ncv_inline:\n\n";
  cv_print_thm Verbose th;
  cv_print Verbose "\n\n"; [th])
val (cv_inline_thms, cv_inline_add) =
    register_ThmSetData_list "cv_inline" insert_cv_inline;

fun insert_cv_from_to th = (
  cv_print Verbose "\ncv_from_to:\n\n";
  cv_print_thm Verbose th;
  cv_print Verbose "\n\n"; [th])
val (cv_from_to_thms, cv_from_to_add) =
    register_ThmSetData_list "cv_from_to" insert_cv_from_to;

end
