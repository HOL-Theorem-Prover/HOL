structure nomdatatype :> nomdatatype =
struct

  open binderLib HolKernel Parse boolLib generic_termsTheory

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

fun new_type_step1 tyname {vp, lp} = let
  val list_mk_icomb = uncurry (List.foldl (mk_icomb o swap))
  val termP = list_mk_icomb (genind_t, [vp,lp,numSyntax.mk_numeral Arbnum.zero])
  fun termPf x = mk_comb(termP, x)
  val (gtty,_) = dom_rng (type_of termP)
  val x = mk_var("x",gtty) and y = mk_var("y", gtty)
  val (glam_ty, gvar_ty) = first2 (#2 (dest_type gtty))
  infix /\
  fun t1 /\ t2 = mk_conj (t1, t2)
  val term_exists =
      prove(mk_exists(x, mk_comb(termP, x)),
            EXISTS_TAC (list_mk_icomb(inst [beta |-> glam_ty] GVAR_t,
                                      [mk_arb stringSyntax.string_ty,
                                       mk_arb gvar_ty])) THEN
            MATCH_MP_TAC (genind_rules |> SPEC_ALL |> CONJUNCT1) THEN
            BETA_TAC THEN REWRITE_TAC [])
  val term_bij_ax = new_type_definition (tyname, term_exists)
  val newty = term_bij_ax |> concl |> dest_exists |> #1 |> type_of |> dom_rng |> #1
  val term_ABSREP =
      define_new_type_bijections { ABS = tyname ^ "_ABS", REP = tyname ^ "_REP",
                                   name = tyname ^ "_ABSREP", tyax = term_bij_ax}
  val absrep_id = term_ABSREP |> CONJUNCT1
  val (term_ABS_t, term_REP_t) = let
    val eqn1_lhs = absrep_id|> concl |> strip_forall |> #2 |> lhs
    val (a, x) = dest_comb eqn1_lhs
  in
    (a, rator x)
  end
  fun term_ABSf x = mk_comb(term_ABS_t, x)
  fun term_REPf x = mk_comb(term_REP_t, x)
  val g = mk_var("g", newty) and h = mk_var("h", newty)
  val term_ABS_pseudo11 = prove(
    mk_imp(termPf x /\ termPf y, mk_eq(mk_eq(term_ABSf x, term_ABSf y), mk_eq(x,y))),
    STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
    DISCH_THEN (MP_TAC o AP_TERM term_REP_t) THEN
    REPEAT (POP_ASSUM (SUBST1_TAC o CONV_RULE (REWR_CONV (CONJUNCT2 term_ABSREP)))) THEN
    REWRITE_TAC [])
  val term_REP_11 = prove(
    mk_eq(mk_eq(term_REPf g, term_REPf h), mk_eq(g,h)),
    EQ_TAC THENL [ALL_TAC, DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
    DISCH_THEN (MP_TAC o AP_TERM term_ABS_t) THEN REWRITE_TAC [absrep_id])
  val genind_term_REP = prove(
    termPf (term_REPf g),
    CONV_TAC (REWR_CONV (CONJUNCT2 term_ABSREP) THENC
              LAND_CONV (RAND_CONV (REWR_CONV absrep_id))) THEN
    REFL_TAC)
  val genind_exists = prove(
    mk_eq(termPf x, mk_exists(g, mk_eq(x, term_REPf g))),
    EQ_TAC THENL [
      REWRITE_TAC [CONJUNCT2 term_ABSREP] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      EXISTS_TAC (term_ABSf x) THEN REFL_TAC,
      DISCH_THEN (X_CHOOSE_THEN g SUBST1_TAC) THEN
      CONV_TAC (REWR_CONV (EQT_INTRO genind_term_REP))
    ])
  val repabs_pseudo_id =
      term_ABSREP |> CONJUNCT2 |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GEN_ALL
in
  {term_ABS_pseudo11 = term_ABS_pseudo11,
   term_REP_11 = term_REP_11, repabs_pseudo_id = repabs_pseudo_id,
   absrep_id = absrep_id,
   genind_term_REP = genind_term_REP,
   genind_exists = genind_exists,
   newty = newty,
   termP = termP,
   term_REP_t = term_REP_t, term_ABS_t = term_ABS_t}
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

(* Vacuous FCBs are of the form
     !vars.... . sideconds ==> v ∉ supp dpm (af args)
   where none of the args are v, and where the sideconds are sufficient to establish
   that v is not in the support of the args, nor in the support of af.

   These arise from the encoding of non-binding recursive constructors with the GLAM
   constructor, which introduces an unused binding name.
*)

fun impconcl t = t |> strip_forall |> #2 |> dest_imp |> #2
val argcong = let
  val fg = mk_eq(mk_var("f", alpha --> beta), mk_var("g", alpha --> beta))
  val xy = mk_eq(mk_var("x", alpha), mk_var("y", alpha))
  val (xy_th, fg_th) = CONJ_PAIR (ASSUME (mk_conj(xy, fg)))
in
  MK_COMB (fg_th, xy_th) |> DISCH_ALL |> GEN_ALL
end

val is_perm_t = prim_mk_const{Thy = "nomset", Name = "is_perm"}
fun elim_vacuous_FCBs {finite_fv,tpm_is_perm} th = let
  val h = hyp th
  fun spot_vacuous t = let
    val c = t |> impconcl |> dest_neg
    val (v,supp_t) = pred_setSyntax.dest_in c
  in
    if free_in v supp_t then NONE else SOME(t,repeat rator (rand supp_t))
  end handle HOL_ERR _ => NONE
  val vacs = List.mapPartial spot_vacuous h
  fun permfor v t = let
    val c = t |> impconcl
  in
    Term.aconv v (repeat rator (rhs c))
  end handle HOL_ERR _ => false
  val vac_pms = map (fn (t,v) => (t,v,valOf (List.find (permfor v) h))) vacs
  val finite_t = valOf (List.find pred_setSyntax.is_finite h)
  val perm_t = valOf (List.find (same_const is_perm_t o rator) h)
  fun GET_FRESH_SETS (asl,w) = let
    val (_, bod) = dest_exists w
    val vnotinA_c = last (strip_conj bod)
    val v = lhand (dest_neg vnotinA_c)
    fun getset t = let
      val (v', s) = t |> dest_neg |> pred_setSyntax.dest_in
    in
      if aconv v' v then SOME s else NONE
    end handle HOL_ERR _ => NONE
    val sets = List.mapPartial getset asl
  in
    EXISTS_TAC (List.foldr pred_setSyntax.mk_union (hd sets) (tl sets))
  end (asl,w)
  open nomsetTheory
  fun mk_result(goal,v,pm) =
      TAC_PROOF(([], goal),
                REPEAT GEN_TAC THEN STRIP_TAC THEN
                MATCH_MP_TAC nomsetTheory.notinsupp_I THEN
                GET_FRESH_SETS THEN REPEAT CONJ_TAC THENL [
                  ACCEPT_TAC (ASSUME perm_t),
                  REWRITE_TAC [ASSUME finite_t, finite_fv,
                               pred_setTheory.FINITE_UNION],
                  REWRITE_TAC [support_def, pred_setTheory.IN_UNION,
                               DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
                  (fn (asl,w) =>
                      MP_TAC (PART_MATCH (lhs o #2 o strip_imp) (ASSUME pm) (lhs w))
                             (asl,w)) THEN
                  ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
                  REPEAT (MATCH_MP_TAC argcong THEN CONJ_TAC THEN1
                            (MATCH_MP_TAC supp_fresh THEN
                             ASM_REWRITE_TAC [tpm_is_perm, ASSUME perm_t] THEN
                             CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
                             ASM_REWRITE_TAC [])) THEN
                  REFL_TAC,
                  ASM_REWRITE_TAC [pred_setTheory.IN_UNION]
                ])
  val elims = map mk_result vac_pms
in
  List.foldl (uncurry PROVE_HYP) th elims
end

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
  open lcsymtacs nomsetTheory
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

end (* struct *)
