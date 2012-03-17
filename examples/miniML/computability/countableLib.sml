open HolKernel pred_setTheory countableTheory lcsymtacs
open boolSyntax numSyntax pairSyntax pred_setSyntax

fun prove_inj_rwt inj = let
  val (hyps,c) = strip_imp (concl inj)
  val tm = rand(rator(rator c))
  val (ty,_) = dom_rng(type_of tm)
  val x = mk_var("x",ty)
  val y = mk_var("y",ty)
in
  prove(list_mk_imp(hyps,
    list_mk_forall([x,y],(mk_eq(
      mk_eq(mk_comb(tm,x),mk_comb(tm,y)),
      mk_eq(x,y))))),
    assume_tac inj >>
    fs[INJ_DEF] >>
    rpt strip_tac >> EQ_TAC >>
    fs[])
end

val count_num_aux_inj_rwt = prove_inj_rwt count_num_aux_inj
val _ = save_thm("count_num_aux_inj_rwt",count_num_aux_inj_rwt)
val _ = export_rewrites["count_num_aux_inj_rwt"]

val count_char_aux_inj_rwt = prove_inj_rwt count_char_aux_inj
val _ = save_thm("count_char_aux_inj_rwt",count_char_aux_inj_rwt)
val _ = export_rewrites["count_char_aux_inj_rwt"]

val count_int_aux_inj_rwt = prove_inj_rwt count_int_aux_inj
val _ = save_thm("count_int_aux_inj_rwt",count_int_aux_inj_rwt)
val _ = export_rewrites["count_int_aux_inj_rwt"]

fun uneta tm = let
  val (t,_) = dom_rng (type_of tm)
  val x = mk_var("x",t)
in mk_abs(x,mk_comb(tm,x)) end

val mk_count_aux_inj_rwt_ttac = let
  val count_num2 = ``count_num2``
  fun count_args ctr = let
    fun f [] = term_of_int 0
      | f [a] = mk_comb(ctr (type_of a), a)
      | f (a::xs) = mk_comb(count_num2,mk_pair(mk_comb(ctr (type_of a), a),f xs))
  in f end
  fun mk_eqn ctr lhs0 (c,(n,eqs,d)) = let
    val (c,ars) = strip_comb c
    val (ars,d) = foldr
      (fn (a,(ars,d)) => let val (n,ty) = dest_var a in
        case Redblackmap.peek(d,n) of
          SOME ty' => if ty = ty' then (a::ars,d) else
            let val vs = Redblackmap.foldl (fn (n,ty,ls) => mk_var(n,ty)::ls) [] d
              val a' = variant vs a
            in (a'::ars,Redblackmap.insert(d,fst(dest_var a'),ty)) end
        | NONE => (a::ars,Redblackmap.insert(d,n,ty)) end)
      ([],d) ars
    val c = list_mk_comb(c,ars)
    val lhs = mk_comb(lhs0, c)
    val rhs = mk_comb(count_num2,mk_pair(term_of_int n,count_args ctr ars))
    val eq = mk_eq (lhs, rhs)
  in (n+1,eq::eqs,d) end
  fun mk_inj_rwt_tm hyps (v,ctr) = let
    val (n,ty) = dest_var v
    val v' = mk_var (Lib.prime n, ty)
  in list_mk_forall([v,v'],list_mk_imp(hyps,mk_eq(mk_eq(mk_comb(ctr,v),mk_comb(ctr,v')),mk_eq(v,v')))) end
in fn tys => fn ttac => let
  val (names,argls) = unzip (map dest_type tys)
  val nchotomys = map (fn ty => SPEC_ALL (TypeBase.nchotomy_of ty)) tys
  val constructorls = map (fn th => map (rhs o snd o strip_exists) (strip_disj (concl th))) nchotomys
  val args = Lib.mk_set (flatten argls)
  val helpers = map (fn a => mk_var("count_"^(dest_vartype a),a --> num)) args
  val count_name_auxs = map (fn n => "count_"^n^"_aux") names
  val count_ty_aux_vars = map (fn (ty,count_name_aux) =>
    mk_var(count_name_aux,
        foldr (fn (h,ty) => type_of h --> ty) (ty --> num) helpers))
    (zip tys count_name_auxs)
  val lhs0s = map (fn v => list_mk_comb (v,helpers)) count_ty_aux_vars
  val counters = zip tys lhs0s
  fun counter_search c t = let
    val (n,ars) = dest_type t
    val ty = foldr (fn (x,t) => (x --> num) --> t) (t --> num) ars
    val ctr = mk_const("count_"^n^"_aux",ty)
  in list_mk_comb(ctr, map (uneta o c) ars) end
  fun counter t = Lib.assoc t counters
    handle HOL_ERR _ => Lib.first (fn h => fst(dom_rng(type_of h)) = t) helpers
    handle HOL_ERR _ => counter_search counter t
  val (eqs,_) = foldl (fn ((lhs0,cl),(eqs,d)) =>
       let val (_,eqs,d) = foldl (mk_eqn counter lhs0) (0,eqs,d) cl in (eqs,d) end)
    ([],Redblackmap.mkDict String.compare)
    (zip lhs0s constructorls)
  val define = case ttac of NONE => xDefine | SOME ttac => (fn x => fn y => tDefine x y ttac)
  val aux_name = hd count_name_auxs
  val count_aux_def = define aux_name [ANTIQUOTE (list_mk_conj eqs)]
  val count_aux_thm = SIMP_RULE (srw_ss()++boolSimps.ETA_ss) [] count_aux_def
  val aux_name_thm = aux_name^"_thm"
  val _ = save_thm(aux_name_thm,count_aux_thm)
  val _ = export_rewrites[aux_name_thm]
  val count_ty_aux_tms = map (fn (n,v) => mk_const(n, type_of v)) (zip count_name_auxs count_ty_aux_vars)
  val hyps = map (mk_inj_rwt_tm []) (zip (map (fn a => mk_var(dest_vartype a, a)) args) helpers)
  val induction = TypeBase.induction_of (hd tys)
  val cvars = map (fst o dest_forall) (strip_conj(snd(strip_imp(snd(strip_forall(concl induction))))))
  val lhs1s = map (fn c => list_mk_comb (c,helpers)) count_ty_aux_tms
  val counters = zip tys lhs1s
  fun counter t = Lib.assoc t counters handle HOL_ERR _ => counter_search counter t
  val concls = map (fn v => let
    val (n,ty) = dest_var v
    val ctr = counter ty
    in mk_inj_rwt_tm hyps (v,ctr) end)
    cvars
  val th = prove(list_mk_conj concls,
    ho_match_mp_tac induction >>
    srw_tac[boolSimps.ETA_ss][] >>
    qmatch_rename_tac `(X = Y z) ⇔ Z` ["X","Y","Z"] >>
    Cases_on `z` >> rw[])
  val (_,ths) = foldl
    (fn (ty,(all,ths)) => let
      val (th,all) = Lib.pluck (fn th => ty = type_of(fst(dest_forall(concl th)))) all
    in (all,th::ths) end)
    (CONJUNCTS th,[])
    tys
  val ths = map (GENL helpers o (SIMP_RULE (srw_ss()++boolSimps.ETA_ss) [])) ths
  val names = map (fn n => n^"_inj_rwt") count_name_auxs
  val _ = map save_thm (zip names ths)
  val _ = export_rewrites names
in ths end
end

val mk_count_aux_inj_rwt = Lib.C mk_count_aux_inj_rwt_ttac NONE

val [count_bool_aux_inj_rwt] = mk_count_aux_inj_rwt [``:bool``]
val [count_list_aux_inj_rwt] = mk_count_aux_inj_rwt [``:α list``]

val count_list_aux_cong = store_thm(
"count_list_aux_cong",
``∀l1 l2 f f'. (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (f x = f' x)) ⇒ (count_list_aux f l1 = count_list_aux f' l2)``,
rw[] >> Induct_on `l1` >>
rw[definition "count_list_aux_def"])
val _ = DefnBase.export_cong"count_list_aux_cong"

val [count_option_aux_inj_rwt] = mk_count_aux_inj_rwt [``:α option``]
val [count_prod_aux_inj_rwt] = mk_count_aux_inj_rwt [``:α # β``]

val count_prod_aux_cong = store_thm(
"count_prod_aux_cong",
``∀p1 p2 ca ca' cb cb'. (p1 = p2) ∧ (∀x. (x = FST p2) ⇒ (ca x = ca' x)) ∧ (∀x. (x = SND p2) ⇒ (cb x = cb' x))
    ⇒ (count_prod_aux ca cb p1 = count_prod_aux ca' cb' p2)``,
rw[] >> Cases_on `p1` >> fs[])
val _ = DefnBase.export_cong"count_prod_aux_cong"

open MiniMLTheory

val [count_error_aux_inj_rwt]        = mk_count_aux_inj_rwt [``:error``]
val [count_lit_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:lit``]
val [count_error_result_aux_inj_rwt] = mk_count_aux_inj_rwt [``:error_result``]
val [count_result_aux_inj_rwt]       = mk_count_aux_inj_rwt [``:α result``]
val [count_opn_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:opn``]
val [count_opb_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:opb``]
val [count_op_aux_inj_rwt]           = mk_count_aux_inj_rwt [``:op``]
val [count_log_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:log``]
val [count_pat_aux_inj_rwt] = let
  val tys  = [``:pat``]
  val ttac = SOME (
    WF_REL_TAC `measure pat_size` >>
    gen_tac >> Induct >>
    rw[pat_size_def] >>
    res_tac >> DECIDE_TAC )
in mk_count_aux_inj_rwt_ttac tys ttac end
val [count_exp_aux_inj_rwt,count_v_aux_inj_rwt] = let
  val tys  = [``:exp``,``:v``]
  val ttac = SOME (
    WF_REL_TAC `inv_image $< (λx. case x of INL v => v_size v | INR e => exp_size e)` >>
    srw_tac[ARITH_ss][] >>
    qmatch_assum_rename_tac `MEM X l` ["X"] >>
    Induct_on `l` >>
    srw_tac[ARITH_ss][exp_size_def] >>
    fs[]>>
    srw_tac[ARITH_ss][exp_size_def] )
in mk_count_aux_inj_rwt_ttac tys ttac end

fun mk_countable a = ``countable ^(mk_univ a)``

fun inj_rwt_to_countable th = let
  val (_,t) = dest_var(fst(dest_forall(concl th)))
in prove(mk_countable t,
  rw[countable_def,INJ_DEF] >>
  prove_tac[th])
end

val countable_v = save_thm("countable_v",inj_rwt_to_countable count_v_aux_inj_rwt)
