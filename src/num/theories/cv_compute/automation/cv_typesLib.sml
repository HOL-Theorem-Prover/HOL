structure cv_typesLib :> cv_typesLib =
struct

open HolKernel Parse boolLib bossLib cvTheory;
open integerTheory wordsTheory cv_typesTheory;

(* --------------------------------------------------- *
    Memory management
 * --------------------------------------------------- *)

(* Updates the set given a delta  *)
fun apply_delta (ThmSetData.ADD(_, th)) thml = th :: thml
  | apply_delta _ _ = failwith "unimplemented case of apply_delta"

(* Defines/Setups the from_to theorem set *)
val {update_global_value = from_to_apply_global_update,
     record_delta = from_to_record_delta,
     get_deltas = from_to_get_deltas,
     get_global_value = from_to_thm_list,
     DB = eval_ruleuction_map_by_theory,...} =
    ThmSetData.export_with_ancestry {
      settype = "from_to",
      delta_ops = {apply_to_global = apply_delta, (* How to update the set (globally) *)
                   uptodate_delta = K true,
                   thy_finaliser = NONE,
                   initial_value = [],            (* The initial value of the set *)
                   apply_delta = apply_delta}
    }

(* Add a theorem to the from_to set *)
fun add_from_to_thm th =
    from_to_apply_global_update (curry (op ::) th)

(* Get a list of all the theorems in the from_to set *)
val from_to_thms = from_to_thm_list

(* --------------------------------------------------- *
    Preliminaries
 * --------------------------------------------------- *)

val ERR = mk_HOL_ERR "cv_typesLib";

fun auto_prove proof_name (goal,tac:tactic) = let
  val (rest,validation) = tac ([],goal)
    handle HOL_ERR r => raise (ERR "auto_prove" "tactic failure")
      | Empty => raise (ERR "auto_prove" "tactic raised Empty")
  in if length rest = 0 then validation [] else let
  in failwith("auto_prove failed for " ^ proof_name) end end

fun dest_fun_type ty = let
  val (name,args) = dest_type ty
  in if name = "fun" then (el 1 args, el 2 args) else failwith("not fun type") end;

fun find_mutrec_types ty = let (* e.g. input ``:v`` gives [``:exp``,``:v``]  *)
  fun is_pair_ty ty = fst (dest_type ty) = "prod"
  val xs = TypeBase.axiom_of ty
           |> SPEC_ALL |> concl |> strip_exists
           |> #1 |> map (#1 o dest_fun_type o type_of)
           |> (fn ls => filter (fn ty => intersect ((#2 o dest_type) ty) ls = []) ls)
  in if is_pair_ty ty then [ty] else if length xs = 0 then [ty] else xs end

fun matching_induction_of typ = let
    val ind = TypeBase.induction_of typ
    val ind_c = concl ind |> strip_forall |> snd |> dest_imp |> snd
    val var_tys = strip_conj ind_c |> map (type_of o fst o dest_forall)
    val matches = mapfilter (fn vty => match_type vty typ) var_tys
  in case matches of
      [] => failwith ("matching_induction_of: " ^ type_to_string typ)
    | _ => INST_TYPE (hd matches) ind
  end

fun mk_funtype arg_tys ret_ty =
  if null arg_tys then ret_ty else
    mk_funtype (butlast arg_tys) (mk_type("fun",[last arg_tys,ret_ty]));

fun make_stem fname args ret_ty = let
  val f_ty = mk_funtype (map type_of args) ret_ty
  in list_mk_comb(mk_var(fname,f_ty),args) end

fun alookup x [] = NONE
  | alookup x ((y,z)::xs) = if x = y then SOME z else alookup x xs;

fun dest_fun_types ty =
  let
    val (x,y) = dest_fun_type ty
    val (xs,z) = dest_fun_types y
  in
    (x::xs,z)
  end handle HOL_ERR _ => ([],ty);

local
  val sum_case = sumTheory.sum_case_def
    |> CONJUNCTS |> hd |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val tys = dest_fun_types (type_of sum_case) |> fst
  val pat_args = mapi (fn i => fn ty => mk_var("v" ^ int_to_string i, ty)) tys
  val pat = list_mk_comb(sum_case,pat_args)
  val thm = REFL pat |> GENL pat_args
in
  val sum_ty = hd tys
  val is_sum_type = can (match_type sum_ty)
  fun mk_sum_case x y z = ISPECL [x,y,z] thm |> concl |> rand
end

fun mk_sum_type l_ty r_ty =
  mk_thy_type {Args = [l_ty, r_ty], Thy = "sum", Tyop = "sum"};

fun mk_pairs [] = cvSyntax.mk_cv_num(numSyntax.term_of_int 0)
  | mk_pairs [x] = x
  | mk_pairs (x::xs) = cvSyntax.mk_cv_pair(x, mk_pairs xs);

fun constructors_of ty = let
  val conses = TypeBase.constructors_of ty
  fun match_ret_type c =
    inst (match_type (repeat (snd o dest_fun_type) (type_of c)) ty) c
  in map match_ret_type conses end

val num_ty = arithmeticTheory.ODD_EVEN |> concl |> dest_forall |> fst |> type_of
val cv_has_shape_tm =
  cv_has_shape_def |> CONJUNCT1 |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator;

fun replicate 0 x = []
  | replicate n x = x :: replicate (n-1) x;

fun list_dest_comb tm =
  if is_comb tm then
    let val (f,xs) = list_dest_comb (rator tm)
    in (f,xs @ [rand tm]) end
  else (tm,[]);

fun term_all_distinct [] = []
  | term_all_distinct (x::xs) = x :: term_all_distinct (filter (fn c => not (aconv c x)) xs)

fun list_dest_conj tm =
  let
    val (x,y) = dest_conj tm
  in x :: list_dest_conj y end
  handle HOL_ERR e => [tm];

(* --------------------------------------------------- *
    Loading from_to theorems
 * --------------------------------------------------- *)

exception Missing_from_to of hol_type;

fun from_to_for_tyvar tyvar = let
  val name = dest_vartype tyvar
  val name = if String.isPrefix "'" name
             then String.substring(name,1,size(name)-1) else name
  val f = mk_var("f_" ^ name,tyvar --> cvSyntax.cv)
  val t = mk_var("t_" ^ name,cvSyntax.cv --> tyvar)
  in ISPECL [f,t] from_to_def |> concl |> dest_eq |> fst |> ASSUME end

fun from_to_for tyvars_alist ty =
  if ty = “:unit” then from_to_unit else
  if ty = “:bool” then from_to_bool else
  if ty = “:num” then from_to_num else
  if ty = “:char” then from_to_char else
  if ty = “:int” then from_to_int else
  if wordsSyntax.is_word_type ty then
    let val ty = wordsSyntax.dest_word_type ty
    in INST_TYPE [alpha|->ty] from_to_word end
  else if can pairSyntax.dest_prod ty then let
    val (a,b) = pairSyntax.dest_prod ty
    val a = from_to_for tyvars_alist a
    val b = from_to_for tyvars_alist b
    in MATCH_MP from_to_pair (CONJ a b) end
  else if can sumSyntax.dest_sum ty then let
    val (a,b) = sumSyntax.dest_sum ty
    val a = from_to_for tyvars_alist a
    val b = from_to_for tyvars_alist b
    in MATCH_MP from_to_sum (CONJ a b) end
  else if can optionSyntax.dest_option ty then let
    val a = from_to_for tyvars_alist (optionSyntax.dest_option ty)
    in MATCH_MP from_to_option a end
  else if listSyntax.is_list_type ty then
    let val a = from_to_for tyvars_alist (listSyntax.dest_list_type ty)
    in MATCH_MP from_to_list a end
  else
    case alookup ty tyvars_alist of
      SOME tyvar_assum => ASSUME tyvar_assum
    | NONE => if is_vartype ty then from_to_for_tyvar ty else
    let
      val thms = from_to_thms ()
      fun match_from_to_thm th =
        let
          val th1 = th |> UNDISCH_ALL
          val ty1 = th1 |> concl |> rand |> type_of |> dest_fun_type |> snd
          val i = match_type ty1 ty
          val th2 = th |> INST_TYPE i |> DISCH_ALL
        in
          if not (is_imp (concl th2)) then th2 else
            let
              val th3 = th2 |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
              val tms = th3 |> concl |> dest_imp |> fst |> list_dest_conj
              fun prove_from_to_thm tm =
                let
                  val ty1 = tm |> rand |> type_of |> dest_fun_type |> snd
                in from_to_for tyvars_alist ty1 end
              val th4 = LIST_CONJ (map prove_from_to_thm tms)
            in MATCH_MP th3 th4 end
        end
      fun find_first f [] = NONE
        | find_first f (x::xs) = SOME (f x) handle HOL_ERR e => find_first f xs
    in
      case find_first match_from_to_thm thms of
        SOME th => th
      | NONE => raise Missing_from_to ty
    end

fun from_for tyvars_alist ty = from_to_for tyvars_alist ty |> concl |> rator |> rand;
fun to_for tyvars_alist ty = from_to_for tyvars_alist ty |> concl |> rand;

(* --------------------------------------------------- *
    Defining new from/to functions for a datatype
 * --------------------------------------------------- *)

exception UnusedTypeVars of hol_type list;

datatype tag_sum = TagNil of int | TagCons of (int * (int option) list);

(*
val ignore_tyvars = [alpha,gamma]
val ignore_tyvars = tl [alpha]
val ty = “:('a,'b,'c) word_tree”
val ty = “:('d, 'c) b”
*)
fun define_from_to_aux ignore_tyvars ty = let
  (* extract target structure from induction theorem *)
  val mutrec_count = length (find_mutrec_types ty)
  val ind = TypeBase.induction_of ty
  val inputs = ind |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCTS |> map (fst o dest_forall o concl)
  val tyvars = dest_type (type_of (hd inputs)) |> snd
               |> filter (fn tyvar => not (mem tyvar ignore_tyvars))
  val first_name = inputs |> hd |> type_of |> dest_type |> fst
  val thy_name = inputs |> hd |> type_of |> dest_thy_type |> #Thy
  val name_prefix = (if thy_name <> current_theory() then thy_name ^ "_" else "")
  val names = inputs |> mapi (fn i => fn v =>
    if i < mutrec_count then
      (name_prefix ^ (v |> type_of |> dest_type |> fst), type_of v)
    else
      (name_prefix ^ first_name ^ "___" ^ int_to_string (i - mutrec_count + 1), type_of v))
  fun should_be_headless pat =
    (* should return true if pat has at least two variables and belongs
       to a type where all other constructors take no arguments *)
    let
      val (cons_tm,args) = list_dest_comb pat
      fun all_other_patterns_are_nil () = let
        val cs = TypeBase.constructors_of (type_of pat)
        val others = filter (fn t => not (can (match_term t) cons_tm)) cs
        val non_nil = filter (fn t => can dest_fun_type (type_of t)) others
        in null non_nil end
    in 1 < length args andalso all_other_patterns_are_nil () end
  (* tyvar assumptions *)
  val tyvar_encoders = mapi (fn i => fn ty =>
    mk_var("f" ^ int_to_string i,mk_type("fun",[ty,cvSyntax.cv]))) tyvars
  val tyvar_decoders = mapi (fn i => fn ty =>
    mk_var("t" ^ int_to_string i,mk_type("fun",[cvSyntax.cv,ty]))) tyvars
  val tyvar_assums =
    map2 (fn f => fn t => ISPECL [f,t] from_to_def |> concl |> dest_eq |> fst)
     (tyvar_encoders) (tyvar_decoders)
  val tyvars_alist = zip tyvars tyvar_assums
  (* define encoding into cv type, i.e. "from function" *)
  val from_names = names |>
    map (fn (fname,ty) =>
      make_stem ("from_" ^ fname) tyvar_encoders (mk_funtype [ty] cvSyntax.cv))
  val lookups =
    map (fn tm => (tm |> type_of |> dest_fun_type |> fst, tm)) (from_names @ tyvar_encoders)
  (*
  val from_f = el 4 from_names
  *)
  fun from_lines from_f = let
    val conses = from_f |> type_of |> dest_type |> snd |> hd |> constructors_of
    (*
      val i = 0
      val cons_tm = el 2 conses
    *)
    fun from_line i cons_tm = let
      val (tys,target_ty) = dest_fun_types (type_of cons_tm)
      val pat_args = mapi (fn i => fn ty => mk_var("v" ^ int_to_string i, ty)) tys
      val pat = list_mk_comb(cons_tm,pat_args)
      val lhs_tm = mk_comb(from_f,pat)
      val tag_num = cvSyntax.mk_cv_num(numSyntax.term_of_int i)
      fun process_arg v =
        case alookup (type_of v) lookups of
          SOME tm => mk_comb(tm,v)
        | NONE => mk_comb(from_for tyvars_alist (type_of v),v)
      val args = map process_arg pat_args
      val special = should_be_headless pat
      val smart_mk_pairs = (if special then mk_pairs o tl else mk_pairs)
      val rhs_tm = smart_mk_pairs (tag_num :: args)
      in mk_eq(lhs_tm,rhs_tm) end
    val lines = mapi from_line conses
    in lines end
  val all_lines = map from_lines from_names |> flatten
  val tm = list_mk_conj all_lines
  val _ = let (* check which tyvar encoders are actually used *)
    val cs = map (rator o fst o dest_eq) all_lines |> term_all_distinct
    val substs = map (fn c => c |-> mk_arb(type_of c)) cs
    val fvs = free_vars (subst substs tm)
    val unused = filter (fn f => not (exists (fn t => aconv t f) fvs)) tyvar_encoders
    in if null ignore_tyvars andalso not (null unused) then
         raise UnusedTypeVars (map (fst o dest_fun_type o type_of) unused)
       else () end
  val from_def = Feedback.trace ("Theory.allow_rebinds", 1) zDefine [ANTIQUOTE tm]
  (* define decoding from cv type, i.e. "to function" *)
  val to_names = names |>
    map (fn (fname,ty) =>
      make_stem ("to_" ^ fname) tyvar_decoders (mk_funtype [cvSyntax.cv] ty))
  val lookups =
    map (fn tm => (tm |> type_of |> dest_fun_type |> snd, tm)) (to_names @ tyvar_decoders)
  val cv_var = mk_var("v",cvSyntax.cv)
  (*
  val to_f = el 2 to_names
  *)
  fun to_lines to_f = let
    val cons_ty = to_f |> type_of |> dest_type |> snd |> el 2
    val conses = cons_ty |> constructors_of
    val lhs_tm = mk_comb(to_f,cv_var)
    (*
      val i = 0
      val cons_tm = el 1 conses
    *)
    fun to_line i cons_tm = let
      val (tys,_) = dest_fun_types (type_of cons_tm)
      val pat_args = mapi (fn i => fn ty => mk_var("v" ^ int_to_string i, ty)) tys
      val pat = list_mk_comb(cons_tm,pat_args)
      fun get_args v [] = []
        | get_args v [x] = [(x,v)]
        | get_args v (x::xs) =
            (x,cvSyntax.mk_cv_fst v) :: get_args (cvSyntax.mk_cv_snd v) xs
      val special = should_be_headless pat
      val init_var = (if special then cv_var else cvSyntax.mk_cv_snd cv_var)
      val args = get_args init_var tys
      fun process_arg (ty,v) =
        case alookup ty lookups of
          SOME tm => mk_comb(tm,v)
        | NONE => mk_comb(to_for tyvars_alist ty,v)
      val xs = map process_arg args
      fun lemmas_for_arg (ty,v) =
        case alookup ty lookups of
          SOME tm => []
        | NONE => [from_to_for tyvars_alist ty]
      val ys = map lemmas_for_arg args |> flatten
      val build = list_mk_comb (cons_tm,xs)
      val test = if null tys then TagNil i else
                   (TagCons (i,(if special then [] else [SOME i])
                      @ replicate (length tys - 1) NONE))
      in (ys,(test,build)) end
    val lemmas_lines = mapi to_line conses
    val lemmas = map fst lemmas_lines |> flatten
    val lines = map snd lemmas_lines
    fun partition p [] = ([],[])
      | partition p (x::xs) =
        let val (xs1,ys1) = partition p xs
        in if p x then (x::xs1,ys1) else (xs1,x::ys1) end
    val common_vars = cv_var :: tyvar_decoders
    fun every p [] = true
      | every p (x::xs) = (p x andalso every p xs)
    fun exists p [] = false
      | exists p (x::xs) = (p x orelse exists p xs)
    fun subset xs ys = every (fn x => exists (aconv x) ys) xs
    val (lines1,lines2) =
      partition (fn (x,tm) => not (subset (free_vars tm) common_vars)) lines
    val lines = lines1 @ lines2
    fun make_last_non_nil_all_none [] = (false,[])
      | make_last_non_nil_all_none ((tag,tm)::rest) = let
      val (has_marked,res) = make_last_non_nil_all_none rest
      in if has_marked then (has_marked,(tag,tm)::res) else
         case tag of
           TagNil i => (has_marked,(tag,tm)::res)
         | TagCons (i,ns) => (true,(TagCons (i,map (K NONE) ns),tm)::res)
      end
    val lines = lines |> make_last_non_nil_all_none |> snd
    val none_num = optionSyntax.mk_none(num_ty)
    fun cv_num_from_int i = cvSyntax.mk_cv_num(numSyntax.term_of_int i)
    fun opt_num_from_opt_int NONE = none_num
      | opt_num_from_opt_int (SOME i) = optionSyntax.mk_some(numSyntax.term_of_int i)
    fun test_to_term (TagNil i,tm) = (mk_eq(cv_var,cv_num_from_int i),tm:term)
      | test_to_term (TagCons (i,ns),tm) =
         (list_mk_comb(cv_has_shape_tm,
            [listSyntax.mk_list(map opt_num_from_opt_int ns,type_of none_num),
             cv_var]),tm)
    val lines = lines |> map test_to_term
    val needs_final_arb = (null lines2 orelse is_sum_type cons_ty)
    fun mk_rhs [] = fail()
      | mk_rhs [(t,x)] = if needs_final_arb then mk_cond(t,x,mk_arb(type_of x)) else x
      | mk_rhs ((t,x)::xs) = mk_cond(t,x,mk_rhs xs)
    in (mk_eq(lhs_tm,mk_rhs lines),lemmas) end
  val (all_lines,lemmas1) = unzip (map to_lines to_names)
  val lemmas = lemmas1 |> flatten |> map DISCH_ALL
  val tm = list_mk_conj all_lines
  val cv_size =
    cv_size_def |> CONJUNCTS |> hd |> SPEC_ALL |> concl |> dest_eq |> fst |> rator
  val args = pairSyntax.list_mk_pair (tyvar_decoders @ [cv_var])
  val size_tm = pairSyntax.mk_pabs(args, mk_comb(cv_size,cv_var))
  fun mk_measure_input_ty [] = type_of args
    | mk_measure_input_ty [x] = type_of args
    | mk_measure_input_ty (x::xs) =
        mk_sum_type (type_of args) (mk_measure_input_ty xs)
  val measure_ty = mk_measure_input_ty all_lines
  val measure_var = mk_var("x",measure_ty)
  fun mk_cases [] = fail()
    | mk_cases [x] = size_tm
    | mk_cases (x::xs) =
       mk_abs (mk_var("x",mk_measure_input_ty (x::xs)),
         (mk_sum_case
           (mk_var("x",mk_measure_input_ty (x::xs)))
           size_tm (mk_cases xs)))
  val measure_tm = mk_cases all_lines
  val full_measure_tm = ISPEC measure_tm prim_recTheory.WF_measure |> concl |> rand
  val to_def_name = (to_names |> hd |> repeat rator |> dest_var |> fst)
  fun make_def () =
    (new_definition(to_def_name,tm),TRUTH) handle HOL_ERR _ =>
    let
      val to_defn = Hol_defn to_def_name [ANTIQUOTE tm]
    in Defn.tprove(to_defn,
                   WF_REL_TAC [ANTIQUOTE full_measure_tm]
                   \\ rewrite_tac [cv_has_shape_expand]
                   \\ rpt strip_tac \\ gvs [cv_size_def])
    end
  val (to_def, to_ind) = Feedback.trace ("Theory.allow_rebinds", 1) make_def ()
  (* from from_to theorems *)
  val assum = if null tyvar_assums then T else list_mk_conj tyvar_assums
  val to_cs = to_def |> CONJUNCTS |> map (rator o fst o dest_eq o concl o SPEC_ALL)
  val from_cs = from_def |> CONJUNCTS |> map (rator o fst o dest_eq o concl o SPEC_ALL)
                                      |> term_all_distinct
  val goals =
    map2 (fn f => fn t =>
      let
        val ty = f |> type_of |> dest_fun_type |> fst
        val v = mk_var("v",ty)
      in mk_abs(v,mk_eq(mk_comb(t,mk_comb(f,v)),v)) end) from_cs to_cs
  val lemma = ISPECL goals ind |> CONV_RULE (DEPTH_CONV BETA_CONV)
  val main_goal = lemma |> concl |> dest_imp |> snd
  val the_goal = mk_imp(assum,main_goal)
  (*
    set_goal([],the_goal)
  *)
  val from_to_thm = auto_prove "from_to_thm" (the_goal,
    strip_tac
    \\ match_mp_tac lemma
    \\ rpt conj_tac
    \\ rpt gen_tac
    \\ rpt disch_tac
    \\ once_rewrite_tac [from_def]
    \\ once_rewrite_tac [to_def]
    \\ rewrite_tac [cv_has_shape_def,cv_fst_def,cv_snd_def]
    \\ EVERY (map assume_tac lemmas)
    \\ gs [from_to_def])
  val from_to_thms =
    from_to_thm |> REWRITE_RULE [GSYM from_to_def]
                |> UNDISCH_ALL |> CONJUNCTS
                |> (fn xs => List.take(xs,mutrec_count))
                |> map DISCH_ALL
  (* simplify from_def *)
  val froms = from_def |> CONJUNCTS |> map SPEC_ALL
  val pick = (rator o fst o dest_eq o concl)
  val from_heads = froms |> map pick |> term_all_distinct
  val from_eqs = map (fn h => LIST_CONJ (filter (fn tm => aconv (pick tm) h) froms))
                     (List.drop(from_heads,mutrec_count))
                   |> map (DefnBase.one_line_ify NONE)
  fun simp_from_eq from_eq = let
    val v = from_eq |> concl |> dest_eq |> fst |> rand
    val tyname = v |> type_of |> dest_type |> fst
    in if tyname = "prod" then
         from_eq |> CONV_RULE (RAND_CONV $ REWR_CONV get_from_pair)
                 |> GEN v |> SIMP_RULE std_ss [GSYM FUN_EQ_THM,SF ETA_ss]
       else if tyname = "option" then
         from_eq |> CONV_RULE (RAND_CONV $ REWR_CONV get_from_option)
                 |> GEN v |> SIMP_RULE std_ss [GSYM FUN_EQ_THM,SF ETA_ss]
       else if tyname = "sum" then
         from_eq |> CONV_RULE (RAND_CONV $ REWR_CONV get_from_sum)
                 |> GEN v |> SIMP_RULE std_ss [GSYM FUN_EQ_THM,SF ETA_ss]
       else if tyname = "list" then
         let
           val tm0 = from_eq |> concl |> dest_eq |> fst |> rator
           val tm1 = from_eq |> concl |> rand |> rand |> dest_abs |> snd
                             |> dest_abs |> snd |> rator |> rand |> rator
           val tm2 = from_list_def |> CONJUNCT1 |> ISPEC tm1 |> concl
                             |> dest_eq |> fst |> rator
           val list_goal = mk_eq(tm0,tm2)
           val res = auto_prove "simp_from_eq_list"
                                (list_goal,
                                 rewrite_tac [FUN_EQ_THM]
                                 \\ Induct
                                 \\ once_rewrite_tac [from_list_def,from_eq] \\ fs [])
         in res end
       else failwith ("simp_from_eq can't do: " ^ tyname) end
  val from_simps = map simp_from_eq from_eqs
  val from_def = map (fn h => LIST_CONJ (filter (fn tm => aconv (pick tm) h) froms))
                     (List.take(from_heads,mutrec_count))
                   |> LIST_CONJ |> REWRITE_RULE from_simps
  (* simplify to_def *)
  val ts = to_def |> CONJUNCTS
  val ts0 = List.take(ts,mutrec_count)
  val ts1 = List.drop(ts,mutrec_count) |> map SPEC_ALL
  (*
  val to_eq = el 1 ts1
  *)
  fun simp_one to_eq = let
    val ty = to_eq |> concl |> dest_eq |> snd |> type_of
    val tyname = dest_type ty |> fst
    in if tyname = "option" then
         to_eq |> CONV_RULE (RAND_CONV $ REWR_CONV get_to_option) |> GEN cv_var
               |> SIMP_RULE std_ss [GSYM FUN_EQ_THM]
               |> CONV_RULE (DEPTH_CONV ETA_CONV)
       else if tyname = "sum" then
         to_eq |> CONV_RULE (RAND_CONV $ REWR_CONV get_to_sum) |> GEN cv_var
               |> SIMP_RULE std_ss [GSYM FUN_EQ_THM]
               |> CONV_RULE (DEPTH_CONV ETA_CONV)
       else if tyname = "prod" then
         to_eq |> CONV_RULE (RAND_CONV $ REWR_CONV get_to_pair) |> GEN cv_var
               |> SIMP_RULE std_ss [GSYM FUN_EQ_THM]
               |> CONV_RULE (DEPTH_CONV ETA_CONV)
       else if tyname = "list" then
         let
           val tm1 = to_eq |> concl |> dest_eq |> fst |> rator
           val tm2 = to_eq |> concl |> dest_eq |> snd |> rator
                           |> rand |> rator |> rand |> rator
           val tm3 = to_list_def |> CONJUNCT1 |> ISPEC tm2 |> SPEC_ALL
                                 |> concl |> dest_eq |> fst |> rator
           val list_goal = mk_eq(tm1,tm3)
           val res = auto_prove "to_list_eq"
                        (list_goal,
                         rewrite_tac [FUN_EQ_THM]
                         \\ Induct
                         \\ once_rewrite_tac [to_eq]
                         \\ asm_rewrite_tac [to_list_def,cv_has_shape_def,
                                             cv_fst_def,cv_snd_def])
         in res end
       else failwith ("don't know: " ^ tyname) end
  val to_simps = map simp_one ts1
  val to_def = ts0 |> map SPEC_ALL |> LIST_CONJ |> REWRITE_RULE to_simps
  (* save all results *)
  val th1 = Feedback.trace ("Theory.allow_rebinds", 1)
            save_thm ("from_" ^ first_name ^ "_def[compute]", from_def)
  val th2 = Feedback.trace ("Theory.allow_rebinds", 1)
            save_thm ("to_" ^ first_name ^ "_def[compute]", to_def)
  fun save_from_to_thms th = let
    val to_name = th |> UNDISCH_ALL |> concl |> rand |> repeat rator |> dest_const |> fst
    val _ = Feedback.trace ("Theory.allow_rebinds", 1)
            save_thm("from_" ^ to_name ^ "_thm", th)
    val _ = add_from_to_thm th
    in () end
  val _ = List.app save_from_to_thms from_to_thms
  in (from_def,to_def,from_to_thms) end
  handle UnusedTypeVars ignore_tyvars => define_from_to_aux ignore_tyvars ty;

fun define_from_to ty = define_from_to_aux [] ty;

(* --------------------------------------------------- *
    Recursively define new from/to functions
 * --------------------------------------------------- *)

fun get_type_name ty = dest_type ty |> fst

fun rec_define_from_to ty = let
  fun loop acc ty =
    let
      val (to_def,from_def,thms) = define_from_to ty
      val _ = print ("Finished to/from for " ^ get_type_name ty ^ "\n\n")
      val _ = print_thm to_def
      val _ = print "\n\n"
    in thms @ acc end
    handle Missing_from_to needs_ty =>
    let
      val _ = print ("Interrupting " ^ get_type_name ty ^
                     " since " ^ get_type_name needs_ty ^ " needed.\n")
      val acc = loop acc needs_ty
      val _ = print ("Continuing " ^ get_type_name ty ^
                     " since " ^ get_type_name needs_ty ^ " exists.\n")
    in loop acc ty end
  in loop [] ty end

(* --------------------------------------------------- *
    Smart functions for retrieving/creating from_to
 * --------------------------------------------------- *)

fun from_to_thm_for ty =
  from_to_for [] ty
  handle Missing_from_to needs_ty =>
  let
    val th = rec_define_from_to needs_ty
  in from_to_thm_for ty end

fun from_term_for ty = from_to_thm_for ty |> concl |> rator |> rand;
fun to_term_for ty = from_to_thm_for ty |> concl |> rand;

end
