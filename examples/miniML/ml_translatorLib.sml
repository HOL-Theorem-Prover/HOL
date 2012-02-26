structure ml_translatorLib :> ml_translatorLib =
struct

open HolKernel boolLib bossLib;
open MiniMLTheory miniMLProofsTheory determTheory ml_translatorTheory;
open arithmeticTheory listTheory combinTheory pairTheory;

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* mapping HOL types into corresponding invariants *)

fun dest_fun_type ty = let
  val (name,args) = dest_type ty
  in if name = "fun" then (el 1 args, el 2 args) else failwith("not fun type") end

local
  val other_types = ref (fn (ty:hol_type) => (fail()):term)
in
  fun get_type_inv ty =
    if is_vartype ty then let
      val name = dest_vartype ty |> explode |> tl |> implode
      in mk_var(name,mk_type("fun",[ty,``:v->bool``])) end else
    if can dest_fun_type ty then let
      val (t1,t2) = dest_fun_type ty
      in ``Arrow (^(get_type_inv t1)) (^(get_type_inv t2))`` end else
    if ty = ``:bool`` then ``BOOL`` else
    if ty = ``:num`` then ``NUM`` else
      (!other_types) ty handle HOL_ERR _ =>
      failwith("Unsupported type " ^ type_to_string ty)
  fun new_type_inv f = let
    val old = (!other_types)
    in (other_types := (fn y => (f y handle HOL_ERR _ => old y))) end
end


(* support for user-defined data-types *)

fun type_of_cases_const ty = let
  val th = TypeBase.case_def_of ty
  val ty = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
              |> concl |> dest_eq |> fst |> rator |> type_of
  in ty end

fun name_of_type ty = let
  val th = TypeBase.case_def_of ty
  val case_const = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                      |> concl |> dest_eq |> fst |> repeat rator
  val name = case_const |> dest_const |> fst |> explode |> rev
                        |> funpow 5 tl |> rev |> implode
  in name end;

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else fail()
  fun foo [] ys i = i
    | foo (x::xs) ys i = let
      val name = (fst o dest_var) x
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

fun append_lists [] = []
  | append_lists (x::xs) = x @ append_lists xs

fun get_nchotomy_of ty = let (* ensures that good variables names are used *)
  val case_th = TypeBase.nchotomy_of ty
  val ty0 = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
  val case_th = INST_TYPE (match_type ty0 ty) case_th
  val xs = map rand (find_terms is_eq (concl case_th))
  val x_var = mk_var("x",ty)
  fun mk_lines [] = []
    | mk_lines (x::xs) = let
    val k = length xs + 1
    fun rename [] = []
      | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                     int_to_string (length xs + 1)
                          in (x,mk_var("x" ^ n, type_of x),
                                mk_var("v" ^ n,``:v``)) end :: rename xs
    val vars = rev (rename (free_vars x))
    val new_x = subst (map (fn (x,y,z) => x |-> y) vars) x
    val tm = list_mk_exists(rev (free_vars new_x), mk_eq(x_var,new_x))
    in tm :: mk_lines xs end
  val goal = mk_forall(x_var,list_mk_disj (rev (mk_lines xs)))
  val lemma = prove(goal,
    STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
    \\ FULL_SIMP_TAC (srw_ss()) []);
  in lemma end

(*
val ty = ``:'a list``
*)

fun derive_thms_for_type ty = let
  val (ty,ret_ty) = dest_fun_type (type_of_cases_const ty)
  val case_of_th = TypeBase.case_def_of ty
  val name = name_of_type ty
  val _ = print ("Adding type " ^ type_to_string ty ^ "\n")
  (* derive case theorem *)
  val case_th = get_nchotomy_of ty
  (* define coupling invariant for data refinement *)
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  fun define_abs name ty case_th = let
    val xs = map rand (find_terms is_eq (concl case_th))
    val ty = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
    val vars = type_vars ty
    val ss = map get_type_inv vars
    val input = mk_var("input",ty)
    val def_name = mk_var(name,list_mk_type (ss @ [input]) ``:v -> bool``)
    val lhs = foldl (fn (x,y) => mk_comb(y,x)) def_name (ss @ [input,``v:v``])
    fun mk_lines [] = []
      | mk_lines (x::xs) = let
      val k = length xs + 1
      val tag = name ^ "." ^ (repeat rator x |> dest_const |> fst)
      fun rename [] = []
        | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                       int_to_string (length xs + 1)
                           in (x,mk_var("v" ^ n,``:v``)) end :: rename xs
      val vars = rev (rename (free_vars x))
      fun find_inv tm =
        if type_of tm = ty then (subst [input|->tm] (rator lhs)) else
          (mk_comb(get_type_inv (type_of tm),tm))
      val ys = map (fn (y,z) => mk_comb(find_inv y,z)) vars
      val tm = if ys = [] then T else list_mk_conj ys
      val str = stringLib.fromMLstring tag
      val vs = listSyntax.mk_list(map (fn (_,z) => z) vars,``:v``)
      val tm = mk_conj(``v = Conv (SOME ^str) ^vs``,tm)
      val tm = list_mk_exists (map (fn (_,z) => z) vars, tm)
      val tm = subst [input |-> x] (mk_eq(lhs,tm))
      val vs = filter (fn x => x <> def_name) (free_vars tm)
      in tm :: mk_lines xs end
    val inv_def = Define [ANTIQUOTE (list_mk_conj (rev (mk_lines xs)))]
    in inv_def end
  val inv_def = define_abs name ty case_th
  val inv_lhs = inv_def |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                        |> dest_eq |> fst
  (* make new inv_def part of get_type_inv *)
  val inv = rator (rator inv_lhs)
  fun extension_to_get_inv_type ty0 = let
    val i = match_type ty ty0
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in subst ss (inst i inv) end
  val _ = new_type_inv extension_to_get_inv_type
  (* prove lemma for case_of *)
  val (case_lemma,ts) = let
    val cases_th = case_of_th
    val cases_tm =
      cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
               |> dest_eq |> fst |> rator
    fun rename [] = []
      | rename (x::xs) = let val k = "f" ^ int_to_string (length xs + 1)
                         in (x,mk_var(k,type_of x)) :: rename xs end
    val vs = rev (rename (free_vars cases_tm))
    val cases_tm = subst (map (fn (x,y) => x |-> y) vs) cases_tm
    val input_var = mk_var("x",ty)
    val exp = mk_comb(cases_tm,input_var)
    val ret_ty = type_of exp
    val xs = rev (map rand (find_terms is_eq (concl case_th)))
    fun add_nums [] = []
      | add_nums (x::xs) = (x,length xs+1) :: add_nums xs
    val ys = rev (add_nums (rev (zip (map snd vs) xs)))
    fun str_tl s = implode (tl (explode s))
    fun list_app x [] = x
      | list_app x (y::ys) = list_app (mk_comb(x,y)) ys
    fun mk_vars ((f,tm),n) = let
      val xs = rev (free_vars tm)
      val fxs = list_app f xs
      val pxs = list_app (mk_var("b" ^ int_to_string n,list_mk_type xs ``:bool``)) xs
      val xs = map (fn x => let val s = str_tl (fst (dest_var x)) in
                            (x,mk_var("n" ^ s,``:string``),
                               mk_var("v" ^ s,``:v``)) end) xs
      val exp = mk_var("exp" ^ int_to_string n, ``:exp``)
      in (n,f,fxs,pxs,tm,exp,xs) end
    val ts = map mk_vars ys
    (* patterns *)
    val patterns = map (fn (n,f,fxs,pxs,tm,exp,xs) => let
      val str = name ^ "." ^ (repeat rator tm |> dest_const |> fst)
      val str = stringSyntax.fromMLstring str
      val vars = map (fn (x,n,v) => ``Pvar ^n``) xs
      val vars = listSyntax.mk_list(vars,``:pat``)
      in ``(Pcon (SOME ^str) ^vars, ^exp)`` end) ts
    val patterns = listSyntax.mk_list(patterns,``:pat # exp``)
    val ret_inv = get_type_inv ret_ty
    val result = mk_comb(ret_inv,exp)
    val result = ``Eval env (Mat exp ^patterns) ^result``
    (* assums *)
    val vs = map (fn (n,f,fxs,pxs,tm,exp,xs) => map (fn (x,_,_) => x) xs) ts |> append_lists
    val b0 = mk_var("b0",``:bool``)
    fun mk_container tm = mk_comb(``CONTAINER:bool->bool``,tm)
    val tm = b0::map (fn (n,f,fxs,pxs,tm,exp,xs) => mk_imp(mk_container(mk_eq(input_var,tm)),pxs)) ts
             |> list_mk_conj
    val tm = list_mk_forall(vs,tm)
    val result = mk_imp(``TAG () ^tm``,result)
    (* tags *)
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    fun mk_hyp (n,f,fxs,pxs,tm,exp,xs) = let
      val env = mk_var("env",``:envE``)
      val env = foldr (fn ((x,n,v),y) =>
        listSyntax.mk_cons(pairSyntax.mk_pair(n,v),y)) env (rev xs)
      val tm = map (fn (x,n,v) => mk_comb(find_inv x,v)) xs @ [pxs]
      val tm = if tm = [] then T else list_mk_conj tm
      val tm = mk_imp(tm,``Eval ^env ^exp (^ret_inv ^fxs)``)
      val vs = map (fn (x,_,_) => x) xs @ map (fn (_,_,v) => v) xs
      val tm = list_mk_forall(vs,tm)
      val n = numSyntax.term_of_int n
      val tm = ``TAG ^n ^tm``
      in tm end;
    val hyps = map mk_hyp ts
    val x = mk_comb(rator (rator inv_lhs),input_var)
    val hyp0 = ``TAG 0 (b0 ==> Eval env exp ^x)``
    val hyps = list_mk_conj(hyp0::hyps)
    val goal = mk_imp(hyps,result)
    val init_tac =
          PURE_REWRITE_TAC [CONTAINER_def]
          \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
    fun case_tac n =
          Q.PAT_ASSUM `TAG 0 bbb` (MP_TAC o REWRITE_RULE [TAG_def,inv_def,Eval_def])
          \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
          \\ Q.PAT_ASSUM `TAG () bbb` (STRIP_ASSUME_TAC o remove_primes o
               SPEC_ALL o REWRITE_RULE [TAG_def,inv_def,Eval_def])
          \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [inv_def]
          \\ Q.PAT_ASSUM `TAG ^(numSyntax.term_of_int n) bbb`
               (STRIP_ASSUME_TAC o REWRITE_RULE [TAG_def])
          \\ REPEAT (Q.PAT_ASSUM `TAG xxx yyy` (K ALL_TAC))
          \\ POP_ASSUM (MP_TAC o remove_primes o SPEC_ALL o REWRITE_RULE [Eval_def])
          \\ FULL_SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
          \\ Q.EXISTS_TAC `res'` \\ FULL_SIMP_TAC std_ss []
          \\ ASM_SIMP_TAC (srw_ss()) []
          \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
          \\ Q.EXISTS_TAC `res` \\ FULL_SIMP_TAC std_ss []
          \\ NTAC 10 (ASM_SIMP_TAC (srw_ss())
               [Once evaluate'_cases,pmatch'_def,bind_def])
    val tac = init_tac THENL (map (fn (n,f,fxs,pxs,tm,exp,xs) => case_tac n) ts)
    val case_lemma = prove(goal,tac)
    val case_lemma = case_lemma |> REWRITE_RULE [TAG_def]
    in (case_lemma,ts) end;
  (* prove lemmas for constructors *)
  fun derive_cons (n,f,fxs,pxs,tm,exp,xs) = let
    val pat = tm
    fun str_tl s = implode (tl (explode s))
    val exps = map (fn (x,_,_) => (x,mk_var("exp" ^ str_tl (fst (dest_var x)), ``:exp``))) xs
    val tag = name ^ "." ^ (repeat rator tm |> dest_const |> fst)
    val str = stringLib.fromMLstring tag
    val exps_tm = listSyntax.mk_list(map snd exps,``:exp``)
    val inv = inv_lhs |> rator |> rator
    val result = ``Eval env (Con (SOME ^str) ^exps_tm) (^inv ^tm)``
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    val tms = map (fn (x,exp) => ``Eval env ^exp ^(find_inv x)``) exps
    val tm = if tms = [] then T else list_mk_conj tms
    val goal = mk_imp(tm,result)
    fun add_primes str 0 = []
      | add_primes str n = mk_var(str,``:v``) :: add_primes (str ^ "'") (n-1)
    val witness = listSyntax.mk_list(add_primes "res" (length xs),``:v``)
    val lemma = prove(goal,
      SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
      \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) [PULL_EXISTS]
      \\ EXISTS_TAC witness \\ ASM_SIMP_TAC (srw_ss()) [inv_def,evaluate_list_SIMP])
    in (pat,lemma) end;
  val conses = map derive_cons ts
  in (ty,ret_ty,inv_def,conses,case_lemma,ts) end

local
  val memory = ref []
  fun add_type ty = let
    val res = derive_thms_for_type ty
    val _ = (memory := res :: (!memory))
    in res end
  fun lookup ty = first (fn (ty1,_,_,_,_,_) => can (match_type ty1) ty) (!memory)
  fun lookup_type ty = lookup ty handle HOL_ERR _ => add_type ty
  fun conses_of ty = let
    val (ty,ret_ty,inv_def,conses,case_lemma,ts) = lookup ty
    in conses end
in
  fun register_type ty = (lookup_type ty; ())
  fun cons_for tm = let
    val ty = type_of tm
    val conses = conses_of ty
    val (pat,th) = first (fn (x,th) => can (match_term x) tm) conses
    val i = snd (match_term pat tm)
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in INST ss (INST_TYPE i th) end
    handle HOL_ERR _ => failwith("Not a constructor for a registered type.")
  fun case_of ty = let
    val (ty,ret_ty,inv_def,conses,case_lemma,ts) = lookup ty
    in (case_lemma,ts) end
end

fun register_term_types tm = let
  fun every_term f tm = (f tm ;
    if is_abs tm then every_term f (snd (dest_abs tm)) else
    if is_comb tm then (every_term f (rand tm); every_term f (rator tm)) else ())
  val special_types = [``:num``,``:bool``]
  fun ignore_type ty =
    if mem ty special_types then true else
    if not (can dest_type ty) then true else
    if can (dest_fun_type) ty then true else false
  fun register_term_type tm = let
    val ty = type_of tm
    in if ignore_type ty then () else register_type ty
    end
  in every_term register_term_type tm end;


(* tests:
register_type ``:'a list``;
register_type ``:'a + num``;
register_type ``:num option``;
register_type ``:unit``;
*)

fun inst_cons_thm tm hol2deep = let
  val th = cons_for tm |> UNDISCH_ALL
  val res = th |> concl |> rand |> rand
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val xs = args res
  val ss = fst (match_term res tm)
  val ys = map (fn x => hol2deep (subst ss x)) xs
  val th1 = if length ys = 0 then TRUTH else LIST_CONJ ys
  in MATCH_MP (D th) th1 end

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val (th,ts) = case_of (type_of (rand tm))
  val pat = th |> UNDISCH_ALL |> concl |> rand |> rand
  val (ss,i) = match_term pat tm
  val th = INST ss (INST_TYPE i th)
  val ii = map (fn {redex = x, residue = y} => (x,y)) i
  val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
  val th = INST ss th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val ns = map (fn n => (n,args n)) names
  val ns = map (fn (n,f,fxs,pxs,tm,exp,xs) => let
      val aa = snd (first (fn (pat,_) => can (match_term tm) pat) ns)
      in zip aa xs end) ts |> append_lists
  val ms = map (fn (b,(x,n,v)) => n |-> stringSyntax.fromMLstring (fst (dest_var b))) ns
  val th = INST ms th
  val ks = map (fn (b,(x,n,v)) => (fst (dest_var x), fst (dest_var b))) ns @
           map (fn (b,(x,n,v)) => (fst (dest_var v), fst (dest_var b) ^ "::value")) ns
  fun rename_bound_conv tm = let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
    val new_s = snd (first (fn (z,_) => z = s) ks)
    in ALPHA_CONV (mk_var(new_s,ty)) tm end handle HOL_ERR _ => NO_CONV tm
  val th = CONV_RULE (DEPTH_CONV rename_bound_conv) th
  in th end;

(*
val tm = ``case g 5 of [] => T | (b::bs) => b``
*)

val sat_hyp_lemma = prove(
  ``(b1 ==> (x1 = x2)) /\ (x1 ==> y) ==> b1 /\ x2 ==> y``,
  Cases_on `b1` \\ Cases_on `x1` \\ Cases_on `x2` \\ Cases_on `y` \\ EVAL_TAC);

fun inst_case_thm tm hol2deep = let
  val th = inst_case_thm_for tm
  val th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th
  val (hyps,rest) = dest_imp (concl th)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun take 0 xs = [] | take n xs = hd xs :: take (n-1) (tl xs)
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = y |> rand |> rand
    val lemma = hol2deep z
    val lemma = D lemma
    val new_env = y |> rator |> rator |> rand
    val env = mk_var("env",``:envE``)
    val lemma = INST [env|->new_env] lemma
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP] THENC
             DEPTH_CONV stringLib.string_EQ_CONV THENC
             SIMP_CONV std_ss []) z1 |> DISCH x1
    val lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma)
    val bs = take (length vs div 2) vs
    fun LIST_UNBETA_CONV [] = ALL_CONV
      | LIST_UNBETA_CONV (x::xs) =
          UNBETA_CONV x THENC RATOR_CONV (LIST_UNBETA_CONV xs)
    val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                  (LIST_UNBETA_CONV (rev bs))) lemma
    val lemma = GENL vs lemma
    val _ = can (match_term tm) (concl lemma) orelse failwith("sat_hyp failed")
    in lemma end handle HOL_ERR _ => (print_term tm; fail())
  fun sat_hyps tm = if is_conj tm then let
    val (x,y) = dest_conj tm
    in CONJ (sat_hyps x) (sat_hyps y) end else sat_hyp tm
  val lemma = sat_hyps hyps
  val th = MATCH_MP th lemma
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                  REWRITE_CONV [])) th
  in th end;


(* the preprocessor *)

fun single_line_def def = let
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val lhs = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                |> concl |> dest_eq |> fst
  in if filter (not o is_var) (args lhs) = [] then def else let
  val const = lhs |> repeat rator
  val name = const |> dest_const |> fst
  val rw = fetch "-" (name ^ "_curried_def")
           handle HOL_ERR _ => let
           val arg = mk_var("x",const |> type_of |> dest_type |> snd |> hd)
           in REFL (mk_comb(const,arg)) end
  val tpc = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rator
  val args = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rand
  val tp = fetch "-" (name ^ "_tupled_primitive_def")
           handle HOL_ERR _ =>
           fetch "-" (name ^ "_primitive_def")
  val (v,tm) = tp |> concl |> rand |> rand |> dest_abs
  val goal = mk_eq(tpc,subst [v|->tpc] tm)
  val lemma = prove(goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,GSYM rw]
    THEN SRW_TAC [] []
    THEN REPEAT BasicProvers.FULL_CASE_TAC
    THEN CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def]))
    THEN SRW_TAC [] [])
  val new_def =
    rw |> SPEC_ALL |> CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [lemma]))
       |> CONV_RULE (RAND_CONV BETA_CONV)
       |> REWRITE_RULE [I_THM]
       |> ONCE_REWRITE_RULE [GSYM rw]
  in new_def end end handle HOL_ERR _ => def;

fun remove_pair_abs def = let
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val def = SPEC_ALL def
  fun delete_pair_arg def = let
    val (lhs,rhs) = def |> concl |> dest_eq
    val xs = args lhs
    val p = first pairSyntax.is_pair xs
    val v = hd (rev (free_vars p)) |> dest_var |> fst
    val v = mk_var(v,type_of p)
    val goal = mk_eq(subst [p|->v] lhs,mk_comb(pairSyntax.mk_pabs(p,rhs),v))
    val lemma = prove(goal,
      SPEC_TAC (v,v) \\ FULL_SIMP_TAC std_ss [FORALL_PROD]
      \\ SIMP_TAC std_ss [Once def]);
    in delete_pair_arg lemma end handle HOL_ERR _ => def
  val def = delete_pair_arg def
  val def = SIMP_RULE std_ss [UNCURRY_SIMP] def
  in def end

fun preprocess_def def = let
  val def = single_line_def def |> SPEC_ALL
  val def = remove_pair_abs def |> SPEC_ALL
  in def end;


(* definition of the main work horse: hol2deep: term -> thm *)

fun D th = let
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  in if is_imp (concl th) then th else DISCH T th end

fun dest_builtin_binop tm = let
  val (px,y) = dest_comb tm
  val (p,x) = dest_comb px
  in (p,x,y,if p = ``($+):num->num->num`` then SPEC p Eval_Opn else
            if p = ``($-):num->num->num`` then SPEC p Eval_Opn else
            if p = ``($*):num->num->num`` then SPEC p Eval_Opn else
            if p = ``($DIV):num->num->num`` then SPEC p Eval_Opn else
            if p = ``($MOD):num->num->num`` then SPEC p Eval_Opn else
            if p = ``($=):num->num->bool`` then SPEC p Eval_Opb else
            if p = ``($<):num->num->bool`` then SPEC p Eval_Opb else
            if p = ``($<=):num->num->bool`` then SPEC p Eval_Opb else
            if p = ``($>):num->num->bool`` then SPEC p Eval_Opb else
            if p = ``($>=):num->num->bool`` then SPEC p Eval_Opb else
            if p = ``($/\):bool->bool->bool`` then Eval_And else
            if p = ``($\/):bool->bool->bool`` then Eval_Or else
            if p = ``($==>):bool->bool->bool`` then Eval_Implies else
            if p = ``($=):bool->bool->bool`` then Eval_Bool_Equal else
              failwith("Not a builtin operator"))
  end

fun inst_Eval_env v th = let
  val thx = th
  val name = fst (dest_var v)
  val str = stringLib.fromMLstring name
  val inv = get_type_inv (type_of v)
  val assum = ``Eval env (Var ^str) (^inv ^v)``
  val new_env = ``(^str,v:v)::env``
  val old_env = new_env |> rand
  val th = thx |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl th))
  val th1 = th |> UNDISCH_ALL
               |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
               |> DISCH new_assum
  in th1 end;

fun apply_Eval_Fun v th fix = let
  val th1 = inst_Eval_env v th
  val th2 = if fix then MATCH_MP Eval_Fun_Fix (GEN ``v:v`` th1)
                   else MATCH_MP Eval_Fun (GEN ``v:v`` (GEN v th1))
  in th2 end;

(*
val v = (last rev_params)
*)

fun apply_Eval_Recclosure fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val body = th |> UNDISCH_ALL |> concl |> rator |> rand
  val inv = get_type_inv (type_of v)
  val new_env = ``(^vname_str,v:v)::(^fname_str,
                    Recclosure env [(^fname_str,^vname_str,^body)] ^fname_str)::env``
  val old_env = ``env:(string # v) list``
  val assum = subst [old_env|->new_env] ``Eval env (Var ^vname_str) (^inv ^v)``
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH_ALL
                |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
                |> DISCH new_assum
  val th2 = MATCH_MP Eval_Recclosure (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
  val lemma = MATCH_MP Eval_Eq_Recclosure assum
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    in INST i (INST_TYPE t lemma) end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  (* lift cl_env assumptions out *)
  val cl_env = mk_var("cl_env",type_of old_env)
  val pattern = ``Eval env (Var name) (Eq x)``
  val cl_assums = find_terms (fn tm => can (match_term pattern) tm andalso
                      ((tm |> rator  |> rator |> rand) = cl_env)) (concl th4)
  val th5 = REWRITE_RULE (map ASSUME cl_assums) th4
  in th5 end

local
  val memory = ref (tl [(T,TRUTH)])
in
  fun store_cert const th = (memory := (const,th)::(!memory))
  fun lookup_cert const = snd (first (fn (c,_) => can (match_term c) const) (!memory))
  fun delete_cert const = (memory := filter (fn (c,_) => c <> const) (!memory))
  fun get_mem () = !memory
end

local
  val rec_pattern = ref T;
in
  fun install_rec_pattern tm = (rec_pattern := tm)
  fun can_match_rec_pattern tm = can (match_term (!rec_pattern)) tm
  fun uninstall_rec_pattern () = (rec_pattern := ``ARB:bool``)
  fun rec_fun () = repeat rator (!rec_pattern)
end

(*
val tm = ``n::xs:num list``
*)

fun hol2deep tm =
  (* variables *)
  if is_var tm then let
    val (name,ty) = dest_var tm
    val inv = get_type_inv ty
    val str = stringSyntax.fromMLstring name
    in ASSUME ``Eval env (Var ^str) (^inv ^tm)`` end else
  (* constants *)
  if numSyntax.is_numeral tm then SPEC tm Eval_Val_NUM else
  if (tm = T) orelse (tm = F) then SPEC tm Eval_Val_BOOL else
  if is_const tm andalso can lookup_cert tm then let
    val th = lookup_cert tm
    val res = th |> UNDISCH_ALL |> concl |> rand
    val inv = get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term res target
    in INST ss (INST_TYPE ii th) end else
  (* data-type constructor *)
  inst_cons_thm tm hol2deep handle HOL_ERR _ =>
  (* data-type pattern-matching *)
  inst_case_thm tm hol2deep handle HOL_ERR _ =>
  (* recursive pattern *)
  if can_match_rec_pattern tm then let
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = rec_fun ()
    val str = stringLib.fromMLstring (fst (dest_const f))
    fun mk_fix tm = let
      val inv = get_type_inv (type_of tm)
      in ``Fix ^inv ^tm`` end
    fun mk_arrow x y = ``Arrow ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_arrow (mk_fix x) res)
    val inv = mk_inv xs (get_type_inv (type_of tm))
    val hyp = ASSUME ``Eval env (Var ^str) (^inv ^f)``
    val ys = map (fn tm => MATCH_MP Eval_Fix (hol2deep tm)) xs
    fun apply_arrow hyp [] = hyp
      | apply_arrow hyp (x::xs) =
          MATCH_MP (MATCH_MP Eval_Arrow (apply_arrow hyp xs)) x
    val th = apply_arrow hyp ys
    in th end else
  (* built-in binary operations *)
  if can dest_builtin_binop tm then let
    val (p,x1,x2,lemma) = dest_builtin_binop tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    in MATCH_MP (MATCH_MP lemma th1) th2 end else
  (* boolean not *)
  if can (match_term ``~(b:bool)``) tm then let
    val x1 = rand tm
    val th1 = hol2deep x1
    in MATCH_MP Eval_Bool_Not th1 end else
  (* if statements *)
  if is_cond tm then let
    val (x1,x2,x3) = dest_cond tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val th3 = hol2deep x3
    val th = MATCH_MP Eval_If (LIST_CONJ [D th1, D th2, D th3])
    in UNDISCH th end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = hol2deep x
    val th2 = inst_Eval_env v th2
    val th2 = th2 |> GEN v |> GEN ``v:v``
    in MATCH_MP Eval_Let (CONJ th1 th2) end else
  (* normal function applications *)
  if is_comb tm then let
    val (f,x) = dest_comb tm
    val thf = hol2deep f
    val thx = hol2deep x
    in MATCH_MP (MATCH_MP Eval_Arrow thf) thx end else
  (* lambda applications *)
  if is_abs tm then let
    val (v,x) = dest_abs tm
    val thx = hol2deep x
    val th1 = apply_Eval_Fun v thx false
    in th1 end else failwith("Cannor translate: " ^ term_to_string tm)


(* main translation routines *)

fun translate def ind = let
  (* perform preprocessing -- reformulate def *)
  val def = preprocess_def def
  val (lhs,rhs) = dest_eq (concl def)
  val is_rec = let
    val const = lhs |> repeat rator
    in can (find_term (fn tm => tm = const)) rhs end
  (* read off information *)
  val _ = register_term_types (concl def)
  fun rev_param_list tm = rand tm :: rev_param_list (rator tm) handle HOL_ERR _ => []
  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
  (* derive deep embedding *)
  val _ = delete_cert (repeat rator lhs)
  val _ = install_rec_pattern lhs
  val th = hol2deep rhs
  val _ = uninstall_rec_pattern ()
  (* replace rhs with lhs in th *)
  val th = CONV_RULE ((RAND_CONV o RAND_CONV) (REWRITE_CONV [GSYM def,CONTAINER_def])) th
  (* abstract parameters *)
  val fname = repeat rator lhs |> dest_const |> fst
  val fname_str = stringLib.fromMLstring fname
  val th = foldr (fn (v,th) => apply_Eval_Fun v th true) th (rev (butlast rev_params))
  val th = if is_rec then apply_Eval_Recclosure fname (last rev_params) th
                     else apply_Eval_Fun (last rev_params) th true
                            |> MATCH_MP Eval_Eq_Fun
                            |> Q.INST [`env`|->`cl_env`] |> Q.SPEC `env` |> UNDISCH_ALL
                            |> Q.INST [`name`|->`^fname_str`]
  val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
  (* apply induction *)
  val th = if not is_rec then th else let
    val th = REWRITE_RULE [CONTAINER_def] th
    val hs = hyp th
    val hyp_tm = list_mk_abs(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = list_mk_forall(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = mk_imp(list_mk_conj hs,goal)
(*
    set_goal([],goal)
*)
    val lemma = prove(goal,
      STRIP_TAC
      \\ SIMP_TAC std_ss [FORALL_PROD]
      \\ MATCH_MP_TAC (SPEC hyp_tm ind |> CONV_RULE (DEPTH_CONV BETA_CONV))
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC th
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);
    val th = UNDISCH lemma |> SPECL (rev rev_params)
    in th end
  (* remove Fix *)
  fun f (v,th) =
    HO_MATCH_MP Eval_FUN_FORALL (GEN v th) |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
  val th = foldr f th rev_params
  (* abbreviate code *)
  val code_name = fname ^ "_ml"
  val th = DISCH_ALL th
  val code_tm = rand (find_term (can (match_term ``Closure env name exp``)) (concl th))
                handle HOL_ERR _ =>
                (find_term (can (match_term ``Recclosure env fns name``)) (concl th))
                |> rator |> rand
  val code_abbrev = new_definition(code_name ^ "_def",
    mk_eq(mk_var(code_name,type_of code_tm),code_tm))
  val th = REWRITE_RULE [GSYM code_abbrev] th |> UNDISCH_ALL
  (* store certificate for later use *)
  val _ = store_cert (repeat rator lhs) th
  in th end

fun find_ind_thm def = let
  val cname = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                  |> dest_eq |> fst |> repeat rator |> dest_const |> fst
  in fetch "-" (cname ^ "_ind") end handle HOL_ERR _ => TRUTH

fun auto_translate def = (def,translate def (find_ind_thm def))

val mlDefine = auto_translate o Define


(*

(* tests *)

val (def,res) = mlDefine `
  gcd m n = if n = 0 then m else gcd n (m MOD n)`

val (def,res) = mlDefine `
  fac n = if n = 0 then 1 else n * fac (n-1)`

val (def,res) = mlDefine `
  foo f x = f (f x (\x. x))`

val (def,res) = mlDefine `
  n_times n f x = if n = 0 then x else n_times (n-1) f (f x)`

val (def,res) = mlDefine `
  fac_gcd k m n = if k = 0 then k else fac_gcd (k-1) (fac (gcd m n)) n`

val (def,res) = mlDefine `
  nlist n = if n = 0 then [] else n :: nlist (n-1)`;

val (def,res) = mlDefine `
  rhs n = if n = 0 then INR n else INL n`;

val (def,res) = mlDefine `
  rhs_option n = if n = 0 then INL NONE else INR (SOME n)`;

val (def,res) = mlDefine `
  map f xs = case xs of [] => [] | (x::xs) => f x :: map f xs`;

val (def,res) = mlDefine `
  add ((x1,x2),(y1,y2)) = x1+x2+y1+y2:num`;

val (def,res) = mlDefine `
  (silly (x,INL y) = x + y) /\
  (silly (x,INR y) = x + y:num)`;

val (def,res) = mlDefine `
  (test1 ([],ys) = []) /\
  (test1 ([x],ys) = [x]) /\
  (test1 ((x::y::xs),(z1::z2::ys)) = [x;z1]) /\
  (test1 _ = [])`;

val (def,res) = mlDefine `
  (Map (f,[]) = []) /\
  (Map (f,x::xs) = f x :: Map (f,xs))`

val (def,res) = mlDefine `
  (ODDS [] = []) /\
  (ODDS [x] = [x]) /\
  (ODDS (x::y::xs) = x :: ODDS xs)`;

val (def,res) = mlDefine `
  (EVENS [] ys = []) /\
  (EVENS [x] ys = [x]) /\
  (EVENS (x::y::xs) (z1::z2::ys) = x :: EVENS xs ys) /\
  (EVENS _ _ = [])`;

*)

end
