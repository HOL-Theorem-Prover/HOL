structure countableLib :> countableLib = struct
open HolKernel bossLib Tactical Drule lcsymtacs
open pred_setTheory countable_initTheory
open boolSyntax numSyntax pairSyntax pred_setSyntax

fun uneta tm = let
  val (t,_) = dom_rng (type_of tm)
  val x = genvar t
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
  val (_,ths) = foldr
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

fun mk_countable a = ``countable ^(mk_univ a)``

fun inj_rwt_to_countable th = let
  val (_,t) = dest_var(fst(dest_forall(concl th)))
in prove(mk_countable t,
  rw[countable_def,INJ_DEF] >>
  prove_tac[th])
end

end
