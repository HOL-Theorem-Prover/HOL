open HolKernel Parse boolLib bossLib cvTheory;
open integerTheory wordsTheory;

val _ = new_theory "cv_types";

val _ = set_grammar_ancestry ["cv", "one", "option", "list", "sum", "pair", "words"];

Overload c2n[local] = “cv$c2n”
Overload c2b[local] = “cv$c2b”
Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

(* every from/to function must satisfy: *)

Definition from_to_def:
  from_to (f:'a -> cv) (t:cv -> 'a) = !x. t (f x) = x
End

(* unit *)

Definition from_unit_def:
  from_unit (u:unit) = (Num 0):cv
End

Definition to_unit_def:
  to_unit (x:cv) = ()
End

Theorem from_to_unit:
  from_to from_unit to_unit
Proof
  fs [from_to_def]
QED

(* bool *)

Theorem from_to_bool:
  from_to b2c c2b
Proof
  fs [from_to_def] \\ Cases \\ fs [b2c_def]
QED

(* num *)

Theorem from_to_num:
  from_to Num c2n
Proof
  fs [from_to_def]
QED

(* char *)

Definition from_char_def:
  from_char (c:char) = Num (ORD c)
End

Definition to_char_def:
  to_char x = CHR (c2n x)
End

Theorem from_to_char:
  from_to from_char to_char
Proof
  fs [from_to_def] \\ Cases \\ fs [from_char_def,to_char_def]
QED

(* int *)

Definition from_int_def:
  from_int (i:int) =
    if integer$int_lt i (integer$int_of_num 0) then
      Pair (Num (integer$Num i)) (Num 0)
    else Num (integer$Num i)
End

Definition to_int_def:
  to_int (Num n) = integer$int_of_num n /\
  to_int (Pair x y) = integer$int_neg (integer$int_of_num (c2n x))
End

Theorem from_to_int:
  from_to from_int to_int
Proof
  fs [from_to_def] \\ Cases \\ fs [from_int_def,to_int_def]
QED

(* word *)

Definition from_word_def:
  from_word (w:'a words$word) = Num (words$w2n w)
End

Definition to_word_def:
  to_word n = words$n2w (c2n n) :'a words$word
End

Theorem from_to_word:
  from_to from_word to_word
Proof
  fs [from_to_def] \\ Cases \\ fs [from_word_def,to_word_def]
QED

(* option *)

Definition from_option_def:
  from_option f NONE = Num 0 /\
  from_option f (SOME x) = Pair (Num 1) (f x)
End

Definition to_option_def:
  to_option t (Num n) = NONE /\
  to_option t (Pair x y) = if x = Num 1 then SOME (t y) else NONE
End

Theorem from_to_option:
  from_to f t ==>
  from_to (from_option f) (to_option t)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Cases \\ fs [from_option_def,to_option_def]
QED

(* pair *)

Definition from_pair_def:
  from_pair f1 f2 (x,y) = Pair (f1 x) (f2 y)
End

Definition to_pair_def:
  to_pair t1 t2 (Pair x y) = (t1 x, t2 y) /\
  to_pair t1 t2 _ = ARB
End

Theorem from_to_pair:
  from_to f1 t1 /\ from_to f2 t2 ==>
  from_to (from_pair f1 f2) (to_pair t1 t2)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Cases \\ fs [from_pair_def,to_pair_def]
QED

(* sum *)

Definition from_sum_def:
  from_sum f1 f2 (INL x) = Pair (Num 0) (f1 x) /\
  from_sum f1 f2 (INR y) = Pair (Num 1) (f2 y)
End

Definition to_sum_def:
  to_sum t1 t2 (Num n) = ARB /\
  to_sum t1 t2 (Pair x y) =
    if x = Num 0 then INL (t1 y) else
    if x = Num 1 then INR (t2 y) else ARB
End

Theorem from_to_sum:
  from_to f1 t1 /\ from_to f2 t2 ==>
  from_to (from_sum f1 f2) (to_sum t1 t2)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Cases \\ fs [from_sum_def,to_sum_def]
QED

(* list *)

Definition from_list_def:
  from_list f [] = Num 0 /\
  from_list f (x::xs) = Pair (f x) (from_list f xs)
End

Definition to_list_def:
  to_list f (Num n) = [] /\
  to_list f (Pair x y) = f x :: to_list f y
End

Theorem from_to_list:
  from_to f t ==>
  from_to (from_list f) (to_list t)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Induct \\ fs [from_list_def,to_list_def]
QED

(* used in definitions of to-functions of user-defined datatype *)

Definition cv_has_shape_def:
  cv_has_shape (SOME n::xs) (Pair x y) = (x = Num n /\ cv_has_shape xs y) /\
  cv_has_shape (NONE::xs) (Pair x y) = cv_has_shape xs y /\
  cv_has_shape (_::xs) (Num _) = F /\
  cv_has_shape [] c = T
End

Theorem cv_has_shape_expand:
  cv_has_shape [] cv = T /\
  cv_has_shape (NONE::xs) cv = (?x y. cv = Pair x y /\ cv_has_shape xs y) /\
  cv_has_shape (SOME n::xs) cv = (?y. cv = Pair (Num n) y /\ cv_has_shape xs y)
Proof
  Cases_on ‘cv’ \\ fs [cv_has_shape_def]
QED

(* lemmas for automation *)

Theorem get_to_pair:
  (if cv_has_shape [NONE] v then (t1 (cv_fst v),t2 (cv_snd v)) else ARB) =
  to_pair t1 t2 v
Proof
  Cases_on ‘v’
  \\ fs [to_pair_def,cv_has_shape_def]
QED

Theorem get_to_option:
  (if cv_has_shape [SOME 1] v then SOME (t (cv_snd v)) else NONE) = to_option t v
Proof
  Cases_on ‘v’
  \\ fs [to_option_def,cv_has_shape_def]
QED

Theorem get_to_sum:
  (if cv_has_shape [SOME 0] v then INL (t1 (cv_snd v))
   else if cv_has_shape [SOME 1] v then INR (t2 (cv_snd v))
   else ARB) = to_sum t1 t2 v
Proof
  Cases_on ‘v’
  \\ fs [to_sum_def,cv_has_shape_def]
QED

Theorem get_from_sum:
  (case v of INL x => Pair (Num 0) (f0 x) | INR y => Pair (Num 1) (f1 y)) =
  from_sum f0 f1 v
Proof
  Cases_on ‘v’ \\ fs [from_sum_def]
QED

Theorem get_from_option:
  (case v of NONE => Num 0 | SOME x => Pair (Num 1) (f x)) =
  from_option f v
Proof
  Cases_on ‘v’ \\ fs [from_option_def]
QED

Theorem get_from_pair:
  (case v of (v0,v1) => Pair (f0 v0) (f1 v1)) =
  from_pair f0 f1 v
Proof
  Cases_on ‘v’ \\ fs [from_pair_def]
QED

(* ------------- automation ---------------- *)

val ERR = mk_HOL_ERR "cv_typesLib";

fun type_of_cases_const ty = let
  val th = TypeBase.case_def_of ty
  val ty = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
              |> concl |> dest_eq |> fst |> repeat rator |> type_of
  in ty end

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

fun from_to_for ty =
  if ty = “:unit” then from_to_unit else
  if ty = “:bool” then from_to_bool else
  if ty = “:num” then from_to_num else
  if ty = “:int” then from_to_int else
  if wordsSyntax.is_word_type ty then
    let val ty = wordsSyntax.dest_word_type ty
    in INST_TYPE [alpha|->ty] from_to_word end
  else if listSyntax.is_list_type ty then
    let val a = from_to_for (listSyntax.dest_list_type ty)
    in MATCH_MP from_to_list a end
  else failwith ("from_to_for: " ^ type_to_string ty)

fun from_for ty = from_to_for ty |> concl |> rator |> rand;
fun to_for ty = from_to_for ty |> concl |> rand;

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

exception UnusedTypeVars of hol_type list;

(*
val ignore_tyvars = tl [alpha]
val ignore_tyvars = [alpha,gamma]
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
  val names = inputs |> mapi (fn i => fn v =>
    if i < mutrec_count then
      ((v |> type_of |> dest_type |> fst), type_of v)
    else
      (first_name ^ int_to_string (i - mutrec_count + 1), type_of v))
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
  (* define encoding into cv type, i.e. "from function" *)
  val tyvar_encoders = mapi (fn i => fn ty =>
    mk_var("f" ^ int_to_string i,mk_type("fun",[ty,cvSyntax.cv]))) tyvars
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
        | NONE => mk_comb(from_for (type_of v),v)
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
  val from_def = zDefine [ANTIQUOTE tm]
  (* define decoding from cv type, i.e. "to function" *)
  val tyvar_decoders = mapi (fn i => fn ty =>
    mk_var("t" ^ int_to_string i,mk_type("fun",[cvSyntax.cv,ty]))) tyvars
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
        | NONE => mk_comb(to_for ty,v)
      val xs = map process_arg args
      fun lemmas_for_arg (ty,v) =
        case alookup ty lookups of
          SOME tm => []
        | NONE => [from_to_for ty]
      val ys = map lemmas_for_arg args |> flatten
      val build = list_mk_comb (cons_tm,xs)
      val tag_num = cvSyntax.mk_cv_num(numSyntax.term_of_int i)
      val c2b = c2b_def |> SPEC_ALL |> concl |> dest_eq |> fst |> rator
      val none_num = optionSyntax.mk_none(num_ty)
      val test = if null tys then mk_eq(cv_var,tag_num) else
                   list_mk_comb(cv_has_shape_tm,
                     [listSyntax.mk_list(
                       (if special then [] else [optionSyntax.mk_some(tag_num |> rand)])
                      @ replicate (length tys - 1) none_num,
                      type_of none_num),
                      cv_var])
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
    val needs_final_arb = (null lines2 orelse is_sum_type cons_ty)
    fun mk_rhs [] = fail()
      | mk_rhs [(t,x)] = if needs_final_arb then mk_cond(t,x,mk_arb(type_of x)) else x
      | mk_rhs ((t,x)::xs) = mk_cond(t,x,mk_rhs xs)
    in (mk_eq(lhs_tm,mk_rhs lines),lemmas) end
  val (all_lines,lemmas1) = unzip (map to_lines to_names)
  val lemmas = lemmas1 |> flatten
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
  val (to_def, to_ind) =
    let
      val to_defn = Hol_defn to_def_name [ANTIQUOTE tm]
    in Defn.tprove(to_defn,
                   WF_REL_TAC [ANTIQUOTE full_measure_tm]
                   \\ rewrite_tac [cv_has_shape_expand]
                   \\ rpt strip_tac \\ gvs [cv_size_def])
           end
  (* from from_to theorems *)
  val assums =
    map2 (fn f => fn t => ISPECL [f,t] from_to_def |> concl |> dest_eq |> fst)
     (tyvar_encoders) (tyvar_decoders)
  val assum = if null assums then T else list_mk_conj assums
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
    \\ fs [from_to_def])
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
         to_eq |> REWRITE_RULE [get_to_option] |> GEN cv_var
               |> SIMP_RULE std_ss [GSYM FUN_EQ_THM]
               |> CONV_RULE (DEPTH_CONV ETA_CONV)
       else if tyname = "sum" then
         to_eq |> REWRITE_RULE [get_to_sum] |> GEN cv_var
               |> SIMP_RULE std_ss [GSYM FUN_EQ_THM]
               |> CONV_RULE (DEPTH_CONV ETA_CONV)
       else if tyname = "prod" then
         to_eq |> REWRITE_RULE [get_to_pair] |> GEN cv_var
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
  val th1 = save_thm("from_" ^ first_name ^ "_def[compute]", from_def)
  val th2 = save_thm("to_" ^ first_name ^ "_def[compute]", to_def)
  fun save_from_to_thms th = let
    val to_name = th |> UNDISCH_ALL |> concl |> rand |> repeat rator |> dest_const |> fst
    in save_thm("from_" ^ to_name ^ "_thm", th) end
  val thms = List.map save_from_to_thms from_to_thms
  in (from_def,to_def,from_to_thms) end
  handle UnusedTypeVars ignore_tyvars => define_from_to_aux ignore_tyvars ty;

fun define_from_to ty = define_from_to_aux [] ty;

(* tests *)

Datatype:
  a = A1 (num list) (((a # b) list) list)
    | A2 ((a + b) list) ;
  b = B1
    | B2
    | B3 (c option) ;
  c = C1
    | C2 a 'aa 'bb
End

val ty = “:('d, 'c) b”
val res = define_from_to ty

Datatype:
  tree = Leaf
       | Branch ((tree list + bool) option list)
End

val res = define_from_to “:tree”

Datatype:
  t1 = T1 num (t1 list)
End

val res = define_from_to “:t1”

Datatype:
  word_tree =
    | Fork word_tree word_tree
    | Word1 ('a word)
    | Other 'b
    | Word2 ('c word)
End

val ty = “:('a,'b,'c) word_tree”
val res = define_from_to ty
val _ = (type_of “from_word_tree f0 t” = “:cv”) orelse fail()

val _ = export_theory();
