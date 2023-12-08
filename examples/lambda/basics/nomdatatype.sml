structure nomdatatype :> nomdatatype =
struct


open binderLib HolKernel Parse boolLib bossLib generic_termsTheory
open nomsetTheory

type coninfo = {con_termP : thm, con_def : thm}

val cpm_ty = let val sty = stringSyntax.string_ty
             in
               listSyntax.mk_list_type (pairSyntax.mk_prod (sty, sty))
             end

fun list_mk_icomb(f, args) = List.foldl (mk_icomb o swap) f args

(* utility functions *)
fun rpt_hyp_dest_conj th = let
  fun foldthis (t, acc) = let
    fun dc t = let
      val (c1, c2) = dest_conj t
    in
      CONJ (dc c1) (dc c2)
    end handle HOL_ERR _ => ASSUME t
  in
    PROVE_HYP (dc t) acc
  end
in
  HOLset.foldl foldthis th (hypset th)
end

fun hCONJ th1 th2 =
    case (hyp th1, hyp th2) of
      ([h1], [h2]) => let
        val h12 = ASSUME(mk_conj(h1,h2))
      in
        CONJ th1 th2
             |> PROVE_HYP (CONJUNCT1 h12)
             |> PROVE_HYP (CONJUNCT2 h12)
      end
    | _ => CONJ th1 th2

val FINITE_t = mk_thy_const{Name = "FINITE", Thy = "pred_set",
                            Ty = (stringSyntax.string_ty --> bool) --> bool}

fun elim_unnecessary_atoms {finite_fv} fths = let
  fun mainconv t = let
    val (vs, bod) = strip_forall t
    val (v,rest) = case vs of
                     [] => raise mk_HOL_ERR "nomdatatype" "elim_unnecessary_atoms"
                                            "Not a forall"
                   | v::vs => (v,vs)
    val _ = Type.compare(type_of v, stringSyntax.string_ty) = EQUAL orelse
            raise mk_HOL_ERR "nomdatatype" "elim_unnecessary_atoms"
                             "Forall not of an atom"
    val (h, c) = dest_imp bod
    val _ = free_in v h andalso not (free_in v c) orelse
            raise mk_HOL_ERR "nomdatatype" "elim_unnecessary_atoms"
                             "Uneliminable atom"
    fun PROVE_FINITE t = let
      open pred_setTheory pred_setSyntax
      val (v, bod) = dest_exists t
      val cs = strip_conj bod
      fun getset t = let
        val t0 = dest_neg t
      in
        if is_in t0 then rand t0 else mk_set [rhs t0]
      end
      val sets = map getset cs
      val union = List.foldl (mk_union o swap) (hd sets) (tl sets)
      val finite_t = mk_finite union
      val finite_th =
        REWRITE_CONV (FINITE_UNION::FINITE_INSERT::FINITE_EMPTY::finite_fv::fths)
                     finite_t
      val fresh_exists = MATCH_MP basic_swapTheory.new_exists (EQT_ELIM finite_th)
                                  |> REWRITE_RULE [IN_UNION, IN_INSERT, NOT_IN_EMPTY,
                                                   DE_MORGAN_THM, GSYM CONJ_ASSOC]
    in
      EQT_INTRO fresh_exists
    end

    val base = HO_REWR_CONV LEFT_FORALL_IMP_THM THENC
               LAND_CONV (((CHANGED_CONV EXISTS_AND_REORDER_CONV THENC
                            RAND_CONV PROVE_FINITE) ORELSEC
                           PROVE_FINITE)) THENC
               REWRITE_CONV []
    fun recurse t = ((SWAP_FORALL_CONV THENC BINDER_CONV recurse) ORELSEC base) t
  in
    recurse
  end t
in
  CONV_RULE (ONCE_DEPTH_CONV mainconv)
end



val gterm_ty = mk_thy_type {Thy = "generic_terms", Tyop = "gterm",
                            Args = [beta,alpha]}

local
  val num_ty = numSyntax.num
  val numlist_ty = listSyntax.mk_list_type num_ty
  val string_ty = stringSyntax.string_ty
in
val genind_t =
  mk_thy_const {Thy = "generic_terms", Name = "genind",
                Ty = (num_ty --> alpha --> bool) -->
                     (num_ty --> beta --> numlist_ty --> numlist_ty --> bool) -->
                     num_ty --> gterm_ty --> bool}
val GVAR_t = mk_thy_const {Thy = "generic_terms", Name = "GVAR",
                           Ty = string_ty --> alpha --> gterm_ty}
end

fun first2 l =
    case l of
      (x::y::_) => (x,y)
    | _ => raise Fail "first2: list doesn't have at least two elements"

fun new_type_step1 tyname n {vp, lp} = let
  val list_mk_icomb = uncurry (List.foldl (mk_icomb o swap))
  val termP =
      list_mk_icomb (genind_t, [vp,lp,numSyntax.mk_numeral (Arbnum.fromInt n)])
  fun termPf x = mk_comb(termP, x)
  val (gtty,_) = dom_rng (type_of termP)
  val x = mk_var("x",gtty) and y = mk_var("y", gtty)
  val (glam_ty, gvar_ty) = first2 (#2 (dest_type gtty))
  val term_exists =
      prove(mk_exists(x, mk_comb(termP, x)),
            irule_at (Pos hd) (cj 1 genind_rules) THEN BETA_TAC THEN
            REWRITE_TAC[])
  val {absrep_id, newty, repabs_pseudo_id, termP, termP_exists, termP_term_REP,
       term_ABS_t, term_ABS_pseudo11,
       term_REP_t, term_REP_11} =
      newtypeTools.rich_new_type (tyname, term_exists)
in
  {term_ABS_pseudo11 = term_ABS_pseudo11, term_REP_11 = term_REP_11,
   term_REP_t = term_REP_t, term_ABS_t = term_ABS_t, absrep_id = absrep_id,
   repabs_pseudo_id = repabs_pseudo_id, genind_term_REP = termP_term_REP,
   genind_exists = termP_exists, newty = newty, termP = termP}
end

fun termP_removal (info as {elimth,absrep_id,tpm_def,termP,repty}) t = let
  val (v, body) = dest_forall t
  fun ELIM_HERE t = let
    val (v,body) = dest_forall t
    val (h,c) = dest_imp body
  in
    BINDER_CONV (LAND_CONV
                     (markerLib.move_conj_left (aconv (mk_comb(termP, v)))) THENC
                     TRY_CONV (REWR_CONV (GSYM AND_IMP_INTRO)) THENC
                     RAND_CONV (UNBETA_CONV v)) THENC
    REWR_CONV elimth THENC BINDER_CONV BETA_CONV THENC
    PURE_REWRITE_CONV [absrep_id, GSYM tpm_def]
  end t

in
  if  Type.compare(type_of v, repty) = EQUAL then
    (SWAP_FORALL_CONV THENC BINDER_CONV (termP_removal info)) ORELSEC
    ELIM_HERE
  else NO_CONV
end t

fun lift_exfunction {repabs_pseudo_id, term_REP_t, cons_info} th = let
  fun mk_conremove {con_termP, con_def} =
      con_termP |> MATCH_MP repabs_pseudo_id
                |> CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV (GSYM con_def))))
                |> SYM
  val conremoves = map mk_conremove cons_info
  val f_REP_o = let
    val (d,r) = dom_rng (type_of term_REP_t)
    val f = mk_var("f", r --> Type.gen_tyvar())
    val x = mk_var("x", d)
  in
    prove(
      mk_eq(mk_comb(f, mk_comb(term_REP_t, x)),
            mk_comb(combinSyntax.mk_o(f, term_REP_t), x)),
      CONV_TAC (RAND_CONV (REWR_CONV combinTheory.o_THM)) THEN REFL_TAC)
  end

  fun fREPo_CONV t = let
    val (v, bod) = dest_exists t
    val o_t = combinSyntax.o_tm |> inst [alpha |-> Type.gen_tyvar()]
    val fREPo = list_mk_icomb(o_t, [v, term_REP_t])
  in
    BINDER_CONV (UNBETA_CONV fREPo) t
  end

  fun elimfREPo th = let
    val (v,bod) = dest_exists (concl th)
    val (vnm, _) = dest_var v
    val bod_th = ASSUME bod
    val (P, arg) = dest_comb bod
    val newf = mk_var(vnm, type_of arg)
    val newbod = mk_comb(P, newf)
  in
    CHOOSE (v, th) (EXISTS (mk_exists(newf, newbod), arg) bod_th)
           |> CONV_RULE (BINDER_CONV BETA_CONV)
  end
in
  th |> REWRITE_RULE (f_REP_o::conremoves)
     |> CONV_RULE fREPo_CONV
     |> elimfREPo
end

fun sort_uvars t = let
  val (v, bod) = dest_forall t
  val (v', _) = dest_forall bod
  val (nm1, ty1) = dest_var v
  val (nm2, ty2) = dest_var v'
  fun tycmp (ty1,ty2) =
      if Type.compare(ty1,ty2) = EQUAL then EQUAL
      else if Type.compare(ty1,``:string``) = EQUAL then LESS
      else if is_vartype ty2 andalso not (is_vartype ty1) then LESS
      else Type.compare(ty1, ty2)
in
  if pair_compare(tycmp,String.compare) ((ty1,nm1), (ty2,nm2)) = GREATER then
    SWAP_FORALL_CONV
  else NO_CONV
end t

fun rename_vars alist t = let
  val (bv, _) = dest_abs t
  val (v, _) = dest_var bv
in
  case Lib.total (Lib.assoc v) alist of
    NONE => NO_CONV
  | SOME v' => RENAME_VARS_CONV [v']
end t

fun prove_alpha_fcbhyp {ppm, alphas, rwts} th = let
  open nomsetTheory
  val th = rpt_hyp_dest_conj (UNDISCH th)
  fun foldthis (h,th) = let
    val h_th =
      TAC_PROOF(([], h),
                rpt gen_tac >> strip_tac >>
                FIRST (map (match_mp_tac o GSYM) alphas) >>
                match_mp_tac (GEN_ALL notinsupp_fnapp) >>
                EXISTS_TAC ppm >>
                srw_tac [] rwts)
  in
    PROVE_HYP h_th th
  end
in
  HOLset.foldl foldthis th (hypset th)
end

val pi_t = mk_var("pi", cpm_ty)
val gterm_ty = mk_thy_type {Tyop = "gterm", Thy = "generic_terms",
                            Args = [beta,alpha]}
val pmact_t = prim_mk_const{Name = "pmact", Thy = "nomset"}
val mk_pmact_t = prim_mk_const{Name = "mk_pmact", Thy = "nomset"}
val raw_gtpm_t =
    mk_thy_const{Name = "raw_gtpm", Thy = "generic_terms",
                 Ty = cpm_ty --> gterm_ty --> gterm_ty}
val gtpm_t = mk_icomb(pmact_t, mk_icomb(mk_pmact_t, raw_gtpm_t))

fun defined_const th = th |> concl |> strip_forall |> #2 |> lhs |> repeat rator

val pmact_absrep' = pmact_bijections |> CONJUNCT2 |> GSYM

fun Save_thm(n, th) = save_thm(n,th) before BasicProvers.export_rewrites [n]

fun define_permutation { name_pfx, name, term_ABS_t, term_REP_t,
                         absrep_id, repabs_pseudo_id, newty,
                         genind_term_REP, cons_info} = let
  val tpm_name = name_pfx ^ "pm"
  val raw_tpm_name = "raw_" ^ tpm_name
  val raw_tpm_t = mk_var(raw_tpm_name, cpm_ty --> newty --> newty)
  val t = mk_var("t", newty)
  val raw_tpm_def = new_definition(
    raw_tpm_name ^ "_def",
    mk_eq(list_mk_comb(raw_tpm_t, [pi_t, t]),
          mk_comb(term_ABS_t,
                  list_mk_icomb(gtpm_t, [pi_t, mk_comb(term_REP_t, t)]))))
  val raw_tpm_t = defined_const raw_tpm_def
  val t_pmact_name = name ^ "_pmact"
  val t_pmact_t = mk_icomb(mk_pmact_t, raw_tpm_t)
  val tpm_t = mk_icomb(pmact_t, t_pmact_t)
  val _ = overload_on (t_pmact_name, t_pmact_t)
  val _ = overload_on (tpm_name, tpm_t)
  val (termP_t, REPg) = dest_comb (concl genind_term_REP)
  val termP_gtpmREP =
      mk_comb(termP_t, list_mk_icomb(gtpm_t, [pi_t, REPg]))
             |> PURE_REWRITE_CONV [genind_gtpm_eqn]
             |> SYM |> C EQ_MP genind_term_REP
  val term_REP_raw_tpm =
      raw_tpm_def |> SPEC_ALL |> AP_TERM term_REP_t
                  |> PURE_REWRITE_RULE [MATCH_MP repabs_pseudo_id termP_gtpmREP]
  val tpm_raw = store_thm(
    tpm_name ^ "_raw",
    mk_eq(tpm_t, raw_tpm_t),
    REWRITE_TAC[pmact_absrep', is_pmact_def, FUN_EQ_THM, raw_tpm_def,
                pmact_nil, pmact_decompose, absrep_id] THEN
    REPEAT CONJ_TAC THENL [
      REPEAT GEN_TAC THEN
      NTAC 2 AP_TERM_TAC THEN CONV_TAC (REWR_CONV EQ_SYM_EQ) THEN
      REWRITE_TAC [GSYM term_REP_raw_tpm, absrep_id],
      REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN
      Q.ISPEC_THEN `gtpm`     (fn is_pmact_def =>
      Q.ISPEC_THEN `gt_pmact` (fn is_pmact_pmact =>
        is_pmact_def |> C EQ_MP is_pmact_pmact
                     |> CONJUNCTS |> last
                     |> MATCH_MP_TAC) is_pmact_pmact) is_pmact_def THEN
      POP_ASSUM ACCEPT_TAC
    ])
  val term_REP_tpm = SUBS [GSYM tpm_raw] term_REP_raw_tpm
  fun tpm_clause {con_termP, con_def} =
      con_def |> SPEC_ALL
              |> AP_TERM (mk_comb(tpm_t, pi_t))
              |> CONV_RULE (RAND_CONV (REWR_CONV
                                           (SUBS [GSYM tpm_raw] raw_tpm_def)))
              |> REWRITE_RULE [MATCH_MP repabs_pseudo_id con_termP,
                               gtpm_thm, listTheory.MAP, listpm_thm]
              |> REWRITE_RULE [GSYM con_def, GSYM term_REP_tpm]
              |> GEN_ALL
  val tpm_thm = Save_thm(tpm_name ^ "_thm",
                         LIST_CONJ (map tpm_clause cons_info))
in
  {term_REP_tpm = term_REP_tpm, tpm_thm = tpm_thm, t_pmact_t = t_pmact_t,
   tpm_t = tpm_t}
end




end (* struct *)
