structure automationLib :> automationLib =
struct

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory;
open source_valuesTheory source_syntaxTheory source_semanticsTheory
     source_propertiesTheory parsingTheory printingTheory mp_then
     automation_lemmasTheory;

(* misc *)

fun get_induction_for_def def = let
  fun mk_arg_vars xs = let
    fun aux [] = []
      | aux (x::xs) =
          mk_var("v" ^ (int_to_string (length xs + 1)),type_of x) :: aux xs
    in (rev o aux o rev) xs end
  fun f tm = let
    val (lhs,rhs) = dest_eq tm
    val (const,args) = strip_comb lhs
    val vargs = mk_arg_vars args
    val args = pairSyntax.list_mk_pair args
    in (const,vargs,args,rhs) end
  val cs = def |> CONJUNCTS |> map (f o concl o SPEC_ALL)
  val cnames = map (fn (x,_,_,_) => x) cs |> op_mk_set aconv
  val cs = map (fn c => (c, map (fn (x,y,z,q) => (y,z,q))
                              (filter (fn (x,_,_,_) => aconv c x) cs))) cnames
           |> map (fn (c,x) => (c,hd (map (fn (x,y,z) => x) x),
                                map (fn (x,y,z) => (y,z)) x))
  fun split_at P [] = fail()
    | split_at P (x::xs) = if P x then ([],x,xs) else let
        val (x1,y1,z1) = split_at P xs
        in (x::x1,y1,z1) end
  fun find_pat_match (_,args,pats) = let
    val pat = hd pats |> fst
    val vs = pairSyntax.list_mk_pair args
    val ss = fst (match_term vs pat)
    val xs = map (subst ss) args
    in (split_at (not o is_var) xs) end
  val xs = map find_pat_match cs
  val ty = map (fn (_,x,_) => type_of x) xs |> hd
  val raw_ind = TypeBase.induction_of ty
  fun my_mk_var ty = mk_var("pat_var", ty)
  fun list_mk_fun_type [] = hd []
    | list_mk_fun_type [ty] = ty
    | list_mk_fun_type (t::ts) = mk_type("fun",[t,list_mk_fun_type ts])
  fun goal_step index [] = []
    | goal_step index ((xs,t,ys)::rest) = let
    val v = my_mk_var (type_of t)
    val args = xs @ [v] @ ys
    val P = mk_var("P" ^ (int_to_string index) ,
              list_mk_fun_type ((map type_of args) @ [bool]))
    val prop = list_mk_comb(P,args)
    val goal = list_mk_forall(args,prop)
    val step = mk_abs(v,list_mk_forall(xs @ ys,prop))
    in (P,(goal,step)) :: goal_step (index+1) rest end
  val res = goal_step 0 xs
  fun ISPEC_LIST [] th = th
    | ISPEC_LIST (x::xs) th = ISPEC_LIST xs (ISPEC x th)
  val ind = ISPEC_LIST (map (snd o snd) res) raw_ind
            |> CONV_RULE (DEPTH_CONV BETA_CONV)
  val goal1 = ind |> concl |> dest_imp |> snd
  val goal2 = list_mk_conj (map (fst o snd) res)
  val goal = mk_imp(goal1,goal2)
  val lemma = snd ((REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []) ([],goal)) []
  val ind = MP lemma (ind |> UNDISCH_ALL) |> DISCH_ALL |> GENL (map fst res)
  in ind end handle HOL_ERR _ =>
  failwith "unable to construct induction theorem from TypeBase info"

fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];

fun is_uppercase c = #"A" <= c andalso c <= #"Z"
fun every p [] = true | every p (x::xs) = p x andalso every p xs;
fun lowercase s = String.translate (fn c => implode [chr (ord c + 32)]) s
fun fix_name s = if every is_uppercase (explode s) then lowercase s else s;

fun is_rec def = let
  val eqs = def |> SPEC_ALL |> CONJUNCTS |> map (concl o SPEC_ALL)
  val consts = map (repeat rator o fst o dest_eq) eqs
  val all_rhs = map (REFL o snd o dest_eq) eqs |> LIST_CONJ |> concl
  in can (first (fn c => can (find_term (aconv c)) all_rhs)) consts end;

fun guess_ind_thm def =
  if not (is_rec def) then NONE else let
    val c = def |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                |> dest_eq |> fst |> repeat rator |> dest_thy_const
    in SOME (fetch "-" (#Name c ^ "_ind"))
       handle HOL_ERR _ => SOME (fetch (#Thy c) (#Name c ^ "_ind")) end
    handle HOL_ERR _ => SOME (get_induction_for_def def)

(* build a list of defun declarations *)

local
  val defuns = ref ([]:term list)
  val comments = ref ([]:term list)
  val next_comment = ref “""”
  fun print_defun defun = let
    val str = mk_comb(“v2str”,mk_comb(“dec2v”,defun))
              |> QCONV EVAL |> concl |> rand |> stringSyntax.fromHOLstring
    in print ("\n\n" ^ str ^ "\n\n\n") end
in
  fun attach_comment q = let
    val str = Portable.quote_to_string (fn _ => raise General.Bind) q
    in next_comment := stringSyntax.fromMLstring (str ^ "\n") end
  fun add_defun defun = let
    val _ = print_defun defun
    in (defuns := defun :: (!defuns);
        comments := (!next_comment) :: (!comments);
        next_comment := “""”; defun) end
  fun get_program main = let
    val ds = listSyntax.mk_list(rev(!defuns),“:dec”)
    in list_mk_comb(“Program”,[ds,main]) end
  fun get_comments () = listSyntax.mk_list(rev((!next_comment)::(!comments)),“:string”)
end

(* from types to representation functions *)

val option_ty = “:α option”
val list_ty = “:α list”
val app_list_ty = “:α app_list”
val pair_ty = “:α # β”

val ty_invs = ref [(“:bool”,“bool”),
                   (“:num”,“Num”),
                   (“:char”,“char”),
                   (“:token”,“token”),
                   (“:test”,“test”),
                   (“:op”,“op”),
                   (“:exp”,“exp”),
                   (“:dec”,“dec”),
                   (“:prog”,“prog”),
                   (“:word64”,“word:word64->v”),
                   (“:word4”,“word:word4->v”),
                   (“:reg”,“reg”),
                   (“:cond”,“cond”),
                   (“:inst”,“inst”),
                   (“:v”,“deep”)];

fun add_ty_inv ty tm = (ty_invs := (ty,tm)::(!ty_invs));

fun ty2inv ty =
  if can dest_vartype ty then
    mk_var(dest_vartype ty |> explode |> tl |> implode,
           mk_type("fun",[ty,“:v”]))
  else if can (first (fn (x,_) => x = ty)) (!ty_invs) then
    snd (first (fn (x,_) => x = ty) (!ty_invs))
  else if can (match_type list_ty) ty then let
    val a = ty2inv (listSyntax.dest_list_type ty)
    in map_def |> ISPEC a |> SPEC_ALL |> concl |> dest_eq |> fst |> rator end
  else if can (match_type app_list_ty) ty then let
    val a = ty2inv (dest_type ty |> snd |> hd)
    in app_list_def |> CONJUNCT1 |> ISPEC a |> SPEC_ALL |> concl
                    |> dest_eq |> fst |> rator end
  else if can (match_type option_ty) ty then let
    val a = ty2inv (ty |> dest_type |> snd |> last)
    in option_def |> CONJUNCT1 |> ISPEC a |> concl |> dest_eq |> fst |> rator end
  else if can (match_type pair_ty) ty then
    pair_def |> ISPECL (dest_type ty |> snd |> map ty2inv)
    |> SPEC_ALL |> concl |> dest_eq |> fst |> rator
  else fail()

(* from terms to --> thms *)

val finalised_mem = ref ([]: (term * thm) list)
val in_flight_mem = ref ([]: (term * thm) list)
val trans_thms    = ref (DB.find "auto_"
  |> filter (fn ((thy,_),_) => thy = "automation_lemmas")
  |> map (CONJUNCTS o #1 o #2)
  |> flatten |> (fn xs => xs @ [last_bool_if]));

fun update_mem lemma =
  (finalised_mem :=
     map (fn (pat,th) => (pat,PURE_REWRITE_RULE [lemma] th)) (!finalised_mem));

val name_eq_name_pat = “name _ = name _”;
val goal_pat = “(b0 ⇒ (env, [x1], s0) ---> ([v1], s1))”
val app_pat = “app (n:num) _ _ _”

fun hol2deep_list hol2deep [] = trans_nil
  | hol2deep_list hol2deep [x] = hol2deep x
  | hol2deep_list hol2deep (x::xs) = let
    val th1 = hol2deep (x:term)
    val th2 = hol2deep_list hol2deep xs
    in MATCH_MP trans_cons (CONJ th1 th2) end

(* val tm = “(\a b c. a + b + c) x y z” *)
fun dest_lam_app tm = let
  fun dest_comb_var tm = let
    val (x,y) = dest_comb tm
    val _ = is_var y orelse fail()
    in (x,y) end
  val xs = list_dest dest_comb_var tm
  val vs = butlast (list_dest dest_abs (hd xs))
  val _ = not (null xs) orelse fail()
  val ys = tl xs
  val _ = length ys = length vs orelse fail()
  val _ = length ys <> 0 orelse fail()
  in zip vs ys end

val name_eq_name_pat = “name n = name m”;
fun decide_name_eq_conv tm =
  if can (match_term name_eq_name_pat) tm then EVAL tm else NO_CONV tm

fun prove_goal hol2deep gg = let
  val ss = find_term (can dest_lam_app) gg |> dest_lam_app handle HOL_ERR _ => []
  fun rename_conv s tm = let
    val (v,x) = dest_abs tm
    val (w,_) = first (fn (_,y) => aconv y v) [s]
    in ALPHA_CONV w tm end handle HOL_ERR _ => NO_CONV tm
  fun list_rename_conv [] = ALL_CONV
    | list_rename_conv (s::ss) =
        ONCE_DEPTH_CONV (rename_conv s) THENC list_rename_conv ss
  val t2 = QCONV (DEPTH_CONV BETA_CONV THENC list_rename_conv ss) gg
  val g2 = t2 |> concl |> rand
  val vs = butlast (list_dest dest_forall g2)
  val x = last (list_dest dest_forall g2) |> dest_imp |> snd
  val new_env = x |> rator |> rand |> rator |> rand
  val ups = find_terms combinSyntax.is_update new_env
  fun get_substs up = let
    val (x1,x2) = combinSyntax.dest_update up
    val name = x1 |> rand
    val inv_v = x2 |> rand |> rator
    val vname = x2 |> rand |> rand
    val (s,i) = match_term inv_v (ty2inv (type_of vname))
    val s2 = (name |-> stringSyntax.fromMLstring (dest_var vname |> fst)) :: s
    in s2 end
  val s = flatten (map get_substs ups)
  val t3 = INST s t2
  val lemma = hol2deep (x |> rand |> rator |> rand |> rator |> rand |> rand)
  val x = t3 |> concl |> rand |> list_dest dest_forall |> last
  val new_env = x |> rand |> rator |> rand |> rator |> rand
  fun LIST_UNBETA_CONV [] = ALL_CONV
    | LIST_UNBETA_CONV (x::xs) =
        UNBETA_CONV x THENC RATOR_CONV (LIST_UNBETA_CONV xs)
  in
     lemma |> INST [mk_var("env",type_of new_env)|->new_env]
           |> CONV_RULE ((RATOR_CONV o RAND_CONV)
               (REWRITE_CONV [combinTheory.APPLY_UPDATE_THM] THENC
                DEPTH_CONV decide_name_eq_conv THENC
                REWRITE_CONV [combinTheory.APPLY_UPDATE_THM,
                              optionTheory.SOME_11,v_11] THENC
                LIST_UNBETA_CONV (rev vs)))
          |> GENL vs
          |> CONV_RULE (REWR_CONV (GSYM t3))
  end

fun apply_th hol2deep target th = let
  val pat = th |> UNDISCH_ALL |> concl |> rand |> rator |> rand |> rator |> rand
  val (i,t) = match_term pat target
  val _ = aconv (pat |> inst t |> subst i) target orelse fail()
  val th1 = INST i (INST_TYPE t th)
  val gs = th1 |> SPEC_ALL |> concl |> rator |> rand |> list_dest dest_conj
               |> filter (fn tm => not (aconv tm T))
  val ls = map (prove_goal hol2deep) gs
  in (if length gs = 0 then th1
      else (MATCH_MP th1 (LIST_CONJ ls)
            |> CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV BETA_CONV))))
      |> PURE_REWRITE_RULE [boolTheory.COND_ID] end

fun get_first f [] = NONE
  | get_first f (x::xs) = SOME (f x) handle HOL_ERR _ => get_first f xs;

fun add_inv tm = mk_comb(ty2inv (type_of tm), tm);

fun inst_app_term hol2deep [] tm = NONE
  | inst_app_term hol2deep ((pat,app_th)::rest) tm =
  if not (can (match_term pat) tm) then inst_app_term hol2deep rest tm else let
  val (i,t) = match_term pat tm
  val lemma = app_th |> INST_TYPE t |> INST i |> PURE_REWRITE_RULE [GSYM map_def]
  val args = lemma |> concl |> rand |> rator |> rator |> rand
  val argl = args |> listSyntax.dest_list |> fst
  val args' = listSyntax.mk_list(map (add_inv o rand) argl,“:v”)
  val lemma = INST (fst (match_term args args')) lemma
  val vs = pat |> inst t |> rand |> list_dest dest_comb |> tl
  val th = hol2deep_list hol2deep (map (subst i) vs)
  in SOME (MATCH_MP trans_Call (CONJ th lemma)) handle HOL_ERR _ =>
     SOME (MATCH_MP trans_Call (CONJ th lemma |> PURE_REWRITE_RULE [GSYM map_def])) end

fun genvar_rule th =
  INST (map (fn v => v |-> genvar (type_of v)) (free_vars (concl th))) th

fun add_to_mem r (pat, app_th) = (r := (pat,app_th)::(!r));

val bad_input = ref T;
fun check_res tm target th =
  if can (find_term (aconv target)) (concl th) then th
  else (bad_input := tm; fail())

fun hol2deep tm =
  if is_var tm then let
    val (s,ty) = dest_var tm
    in SPECL [stringSyntax.fromMLstring s,
              mk_comb(ty2inv ty, tm)] trans_Var end
  else let
    val target = mk_comb(ty2inv (type_of tm), tm)
    in case get_first (apply_th hol2deep target) (!trans_thms) of
         SOME th => check_res tm target th | NONE =>
     (case inst_app_term hol2deep (!in_flight_mem) target of
        SOME res => check_res tm target (res |> PURE_REWRITE_RULE [GSYM map_def]) | NONE =>
     (case inst_app_term hol2deep (!finalised_mem) target of
        SOME res => check_res tm target (res |> PURE_REWRITE_RULE [GSYM map_def]) | NONE =>
      let
        val _ = print "\n\nhol2deep failed for input:\n\n"
        val _ = print_term tm
        val _ = print "\n\n"
      in fail() end))
    end

fun ABBREV_CONV fname params name tm = let
  val v = mk_var(name,type_of tm)
  val defun = list_mk_comb(“Defun”,[fname,params,tm])
  val _ = add_defun defun
  in GSYM (Define ‘^v = ^tm’) end

val trans_app = let
  val vs = free_vars (concl trans_app)
  in INST (map (fn v => v |-> genvar(type_of v)) vs) trans_app end

fun apply_at_conv p c tm =
  DEPTH_CONV (fn tm => if p tm then c tm else NO_CONV tm
                       handle HOL_ERR _ => NO_CONV tm) tm;

fun apply_at_pat_conv pat = apply_at_conv (can (match_term pat));

fun process_def def = let
  val def = def |> SPEC_ALL |> PURE_REWRITE_RULE [all_macro_defs]
  val th = hol2deep (def |> concl |> rand)
           |> MATCH_MP inline_let |> UNDISCH |> CONV_RULE (PATH_CONV "rlrrlr" EVAL)
  val parts = def |> concl |> rator |> rand |> list_dest dest_comb
  val c = hd parts
  val vs = tl parts
  fun v_to_str v = let
    val s = v |> dest_var |> fst |> stringSyntax.fromMLstring
            handle HOL_ERR _ =>
            v |> dest_const |> fst |> stringSyntax.fromMLstring
    in mk_comb (“name”, s) end
  val params = listSyntax.mk_list(map v_to_str vs,“:num”)
  val args = listSyntax.mk_list(map add_inv vs,“:v”)
  val lemma = trans_app
    |> SPEC (c |> dest_const |> fst |> fix_name |> stringSyntax.fromMLstring)
    |> SPECL [params,args]
  val new_env = lemma |> concl |> rand
  val env_var = lemma |> concl |> rator |> rand |> dest_abs |> fst
  val lemma1 = lemma |> SIMP_RULE std_ss [LET_THM,LENGTH]
  val th1 = INST [env_var|->new_env] th
  val th2 = MATCH_MP lemma1 th1
  val c_name = c |> dest_const |> fst
  val fname = fix_name c_name |> stringSyntax.fromMLstring
  val th3 = th2 |> CONV_RULE (PATH_CONV "lrrrr"
                     (ABBREV_CONV “name ^fname” params (c_name ^ "_code")))
                |> UNDISCH
  val th4 = th3 |> CONV_RULE (PATH_CONV "rrlrr" (REWR_CONV (GSYM def)))
  val th5 = th4 |> CONV_RULE (PATH_CONV "lr"
     (SIMP_CONV std_ss [make_env_def,combinTheory.APPLY_UPDATE_THM]))
  val tms = find_terms (can (match_term name_eq_name_pat)) (concl th5)
  val th6 = REWRITE_RULE (map EVAL tms) th5
  val th7 = if is_imp (concl th6) then th6 else DISCH T th6
  in th7 end

fun remove_apps tm =
  if can (match_term app_pat) tm then T else
  if is_abs tm then let
    val (v,b) = dest_abs tm
    in mk_abs(v,remove_apps b) end else
  if is_comb tm then let
    val (x,y) = dest_comb tm
    in mk_comb(remove_apps x, remove_apps y) end else tm

fun make_format d = let
  val pat = d |> concl |> dest_eq |> fst
  val parts = pat |> list_dest dest_comb
  val c = hd parts
  val vs = tl parts
  val vs_tm = listSyntax.mk_list(map add_inv vs,“:v”)
  val c_str = c |> dest_const |> fst |> fix_name
  val n = c_str |> stringSyntax.fromMLstring
  val s = trans_nil |> concl |> rand |> rand |> rand
  val cc = list_mk_comb(“app (name ^n)”, [vs_tm,s,pairSyntax.mk_pair(add_inv pat,s)])
  fun mk_type [] ty = ty
    | mk_type (t::ts) ty = t --> (mk_type ts ty)
  val side_tm = mk_var(c_str ^ "_side", mk_type (map type_of vs) bool)
  val s = list_mk_comb(side_tm,vs)
  in (add_inv pat,ASSUME cc |> DISCH_ALL |> DISCH s |> REWRITE_RULE [AND_IMP_INTRO]) end

fun remove_primes s = implode (filter (fn c => c <> #"'") (explode s))
val varnames = explode "xyzstvwabcdefghijklmnopqru" |> map (implode o single)
fun auto_name_bound_vars_conv vs tm =
  if is_comb tm then
    (RATOR_CONV (auto_name_bound_vars_conv vs) THENC
     RAND_CONV (auto_name_bound_vars_conv vs)) tm
  else if is_var tm then ALL_CONV tm
  else if is_const tm then ALL_CONV tm
  else let
    val (v,body) = dest_abs tm
    val (n,ty) = dest_var v
    val n = remove_primes n
    val w = hd (filter (fn s => not (mem s vs)) (n::varnames))
    in (ALPHA_CONV (mk_var(w,ty)) THENC
        ABS_CONV (auto_name_bound_vars_conv (w::vs))) tm end

val list_case = “list_CASE (x:'a list) (nil_f:'b) cons_f”
val pair_case = “pair_CASE x (the_case:'a -> 'b -> 'c)”
val base_name = "variable_"
fun make_some_names_long_conv tm = let
  val next = ref 0
  fun get_var ty = let
    val n = !next
    in (next := n + 1; mk_var(base_name ^ int_to_string n, ty)) end
  fun pass tm = let
    val _ = can (match_term list_case) tm orelse
            can (match_term pair_case) tm orelse fail()
    val (v1,body) = dest_abs (rand tm)
    val (v2,body) = dest_abs body
    val v1 = get_var (type_of v1)
    val v2 = get_var (type_of v2)
    in (RAND_CONV (ALPHA_CONV v1 THENC ABS_CONV (ALPHA_CONV v2))
        THENC RATOR_CONV pass THENC RAND_CONV pass) tm end
    handle HOL_ERR _ =>
    if is_comb tm then (RATOR_CONV pass THENC RAND_CONV pass) tm else
    if is_abs tm then (ABS_CONV pass) tm else ALL_CONV tm
  in pass tm end

fun preprocess_def def = let
  val defs = def |> CONJUNCTS |> map SPEC_ALL
  fun nub [] = [] | nub (x::xs) = x :: nub (filter (not o aconv x) xs)
  fun get_c d = d |> concl |> dest_eq |> fst |> repeat rator
  val cs = nub (map get_c defs)
  in map (fn c => filter (fn th => aconv (get_c th) c) defs |> LIST_CONJ
                  |> DefnBase.one_line_ify NONE |> GEN_ALL
                  |> CONV_RULE (auto_name_bound_vars_conv [])
                  |> CONV_RULE make_some_names_long_conv
                  |> CONV_RULE (auto_name_bound_vars_conv []) |> SPEC_ALL) cs
 end

fun to_deep def = let
  val ind = guess_ind_thm def
  val defs = preprocess_def def
  val formats = map make_format defs
  val _ = app (add_to_mem in_flight_mem) formats
  val thms = map process_def defs
  val ts = map (fn th => th |> concl |> dest_imp |> fst |> remove_apps) thms
  val ss = map (fn (tm,th) => th |> concl |> dest_imp |> fst |> dest_conj |> fst) formats
  val vss = map (tl o list_dest dest_comb) ss
  val ps = map (fn (vs,(t,s)) => list_mk_forall(vs,mk_imp(t,s))) (zip vss (zip ts ss))
  val tm = list_mk_conj ps
  val (_,_,side_def) = Hol_reln ‘^tm’
  val cs = side_def |> CONJUNCTS |> map (repeat rator o fst o dest_eq o concl o SPEC_ALL)
  val gs = map (fn (_,th) => th |> concl |> dest_imp |> fst
                                |> dest_conj |> fst |> repeat rator) formats
  val i = map2 (fn g => fn c => g |-> c) gs cs
  val thms = map (INST i) thms
  val ys = map (fn (vs,(c,(_,th))) =>
             list_mk_abs(vs,mk_imp(list_mk_comb(c,vs),th |> concl |> rand)))
             (zip vss (zip cs formats))
  val thms =
(*
  val SOME ind_thm = ind
*)
    case ind of NONE => map (PURE_REWRITE_RULE [GSYM side_def]) thms
    | SOME ind_thm => let
      val name_pat = “source_values$name _”
      val lemma = ind_thm |> SPECL ys |> CONV_RULE (DEPTH_CONV BETA_CONV)
                          |> PURE_REWRITE_RULE [all_macro_defs]
                          |> PURE_REWRITE_RULE [GSYM map_def]
      val lookup_funs = LIST_CONJ thms |> hyp |> list_mk_conj
      val goal = mk_imp(lookup_funs,concl lemma |> rand)
      val tacs = map
        (fn th => match_mp_tac (DISCH_ALL th |> REWRITE_RULE [AND_IMP_INTRO])) thms
      val std_tac =
        strip_tac
        \\ match_mp_tac lemma
        \\ rpt conj_tac \\ rpt gen_tac
        \\ rpt (disch_then strip_assume_tac)
        \\ rpt conj_tac \\ rpt gen_tac
        \\ rpt (disch_then strip_assume_tac)
        \\ FIRST tacs \\ fs []
        \\ pop_assum mp_tac
        \\ simp [Once side_def] \\ fs [name_def]
        \\ rpt strip_tac \\ res_tac \\ fs []
        \\ TRY (Cases_on ‘t’ \\ Cases_on ‘z’ \\ fs [] \\ NO_TAC)
        \\ metis_tac []
      val careful_tac =
        strip_tac
        \\ match_mp_tac lemma
        \\ rpt conj_tac \\ rpt gen_tac
        \\ rpt (disch_then strip_assume_tac)
        \\ rpt conj_tac \\ rpt gen_tac
        \\ rpt (disch_then strip_assume_tac)
        \\ FIRST tacs \\ full_simp_tac std_ss []
        \\ pop_assum mp_tac
        \\ simp_tac std_ss [Once side_def]
        \\ rpt (pop_assum mp_tac)
        \\ CONV_TAC (apply_at_conv (can (match_term name_pat)) EVAL)
        \\ rpt strip_tac
        \\ full_simp_tac std_ss []
        \\ rpt strip_tac
        \\ full_simp_tac std_ss []
        \\ rpt (pop_assum mp_tac)
        \\ CONV_TAC (apply_at_conv (can (match_term name_pat)) EVAL)
        \\ rpt strip_tac
        \\ full_simp_tac std_ss []
     (* \\ fs [] *)
        \\ TRY (Cases_on ‘t’ \\ Cases_on ‘z’ \\ fs [] \\ NO_TAC)
        \\ metis_tac []
      val careful = “v2exp”
      val thA = prove(goal,
        if can (find_term (aconv careful)) (def |> CONJUNCTS |> hd |> SPEC_ALL |> concl |> dest_eq |> fst)
        then careful_tac else std_tac)
      val thms = thA |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL |> CONJUNCTS
      val thms = map2 (fn th => fn vs => SPECL vs th) thms vss
      in thms end
  val _ = (in_flight_mem := [])
  val side_def =
    case ind of
      NONE => let
        val vs = list_dest dest_forall (concl side_def) |> butlast
        in side_def |> SPEC_ALL
                    |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [name_def]))
                    |> GENL vs end
    | SOME i => let
      val n = side_def |> SPEC_ALL |> concl |> dest_eq |> fst
      val vs = list_dest dest_comb n
      val t = ISPEC (list_mk_abs (tl vs, mk_eq(n,T))) i
              |> CONV_RULE (DEPTH_CONV BETA_CONV)
      val goal = concl t |> rand
      val tac = match_mp_tac t \\ rw [] \\ once_rewrite_tac [side_def]
                \\ fs [name_def] \\ CCONTR_TAC \\ fs [] \\ fs [] \\ fs [name_def]
      val lemma = snd (tac ([],goal)) []
      in lemma end handle HOL_ERR _ => side_def
  val side_is_true =
    aconv (side_def |> SPEC_ALL |> concl |> rand) T handle HOL_ERR _ => false
  val rr = if side_is_true then PURE_REWRITE_RULE [side_def] else I
  val results = map2 (fn (pat,_) => fn th => (pat,rr th)) formats thms
  val _ = app (add_to_mem finalised_mem) results
  val sides = map2 (fn th => fn vs => SPECL vs th) (CONJUNCTS side_def) vss
  val c_name = defs |> hd |> SPEC_ALL |> concl |> dest_eq
                    |> fst |> repeat rator |> dest_const |> fst
  val thms = map snd results
  val _ = print "\n"
  val _ = print_thm (LIST_CONJ thms)
  val _ = print "\n\n"
  val _ = save_thm(c_name ^ "_app", LIST_CONJ thms)
  in LIST_CONJ sides end

(* functions for inputing concrete syntax directly *)

local
  fun parse_any f q = let
    val str = Portable.quote_to_string (fn _ => raise General.Bind) q
    val tm = stringSyntax.fromMLstring str
    val th = EVAL ``^f (head (parse (lexer ^tm) (Num 0) []))``
    fun get_name tm = let
      val t = EVAL ``ascii_name ^tm`` |> concl |> rand
      val t1 = optionSyntax.dest_some t
      val name_tm = name_def |> CONJUNCT1 |> concl |> dest_eq |> fst |> repeat rator
      in mk_comb(name_tm,t1) end
    fun fix_names tm =
      if numSyntax.is_numeral tm then
        (get_name tm handle HOL_ERR _ => tm)
      else if is_comb tm then
        mk_comb(fix_names (rator tm),fix_names (rand tm))
      else tm
    in th |> concl |> rand |> fix_names end
in
  val parse_exp = parse_any ``v2exp``
  val parse_dec = parse_any ``v2dec``
end

fun define_code q = let
  val dec = add_defun (parse_dec q)
  val c = dec |> rator |> rator |> rand |> rand |> stringSyntax.fromHOLstring
  val v = mk_var(c ^ "_code", dec |> rand |> type_of)
  in new_definition(c ^ "_code_def", mk_eq(v, dec |> rand)) end

fun write_hol_string_to_file filename tm = let
  val f = TextIO.openOut filename
  val s = tm |> stringSyntax.fromHOLstring
  val _ = TextIO.output (f,s)
  val _ = TextIO.closeOut f
  in () end

end
