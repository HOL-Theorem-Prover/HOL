structure countable_typesLib :> countable_typesLib = struct

open pred_setTheory countable_typesTheory boolTheory
open bossLib HolKernel Tactic Tactical boolSyntax Drule Rewrite Hol_pp

fun goal_tac gt = (fn (asms, gl) => gt gl (asms, gl)) : tactic

fun find_toplevel_cases xs [] = xs
  | find_toplevel_cases xs (t :: ts) = if is_comb t
  then find_toplevel_cases ((if TypeBase.is_case t then [t] else []) @ xs)
    (rator t :: rand t :: ts)
  else find_toplevel_cases xs ts

val var_case_tac = goal_tac (fn gl => let
    val xs = find_toplevel_cases [] [gl] |> map (#2 o TypeBase.dest_case)
        |> filter is_var
  in case xs of
    [] => NO_TAC
    | v :: _ => tmCases_on v []
        \\ simp_tac bool_ss [TypeBase.case_def_of (type_of v)]
 end)

val countable_tm = concl inj_countable |> strip_forall |> snd
    |> dest_imp |> snd |> rator

fun mk_countable_lemma ty = let
    val ind = TypeBase.induction_of ty
    val conses = find_terms (fn t => is_comb t andalso is_var (rator t)) (concl ind)
      |> map rand |> filter (not o is_var)
    val size_thm = snd (TypeBase.size_of ty)
    val sizes = strip_conj (concl size_thm) |> map (lhs o snd o strip_forall)
      |> map rator |> HOLset.fromList Term.compare |> HOLset.listItems
    val lemma_tys = map (fst o dom_rng o type_of) sizes
    fun ty_n ty = total (index (fn ty2 => ty2 = ty)) lemma_tys
    val ex_param_tys = map (snd o strip_comb) conses |> List.concat |> map type_of
      |> HOLset.fromList Type.compare |> HOLset.listItems
      |> filter (not o Option.isSome o ty_n)
    val assms = map (curry mk_icomb countable_tm o pred_setSyntax.mk_univ) ex_param_tys
    val sum_ty = sumSyntax.list_mk_sum lemma_tys
    val u_sum_ty = pred_setSyntax.mk_univ sum_ty
    val _ = print ("Making countable lemma for: ")
    val _ = Hol_pp.print_term u_sum_ty
    val _ = print ("\n")
    fun mk_sum t = let
        val n = Option.valOf (ty_n (type_of t))
        val t2 = if n = length lemma_tys - 1 then t
          else sumSyntax.mk_inl (t, sumSyntax.list_mk_sum (List.drop (lemma_tys, n + 1)))
      in foldr (fn (ty, t) => sumSyntax.mk_inr (t, ty)) t2 (List.take (lemma_tys, n)) end
    fun mk_rec t = let
        val xs = snd (strip_comb t) |> filter (Option.isSome o ty_n o type_of)
      in listSyntax.mk_list (map mk_sum xs, sum_ty) end
    fun mk_ints (i, t) = let
        val xs = snd (strip_comb t) |> filter (not o Option.isSome o ty_n o type_of)
        val ns = map (fn x => mk_comb (mk_var ("f", type_of x --> numSyntax.num), x)) xs
      in listSyntax.mk_list ([numSyntax.term_of_int i] @ ns, numSyntax.num) end
    fun mk_case i t = (mk_sum t, pairSyntax.mk_pair (mk_ints (i, t), mk_rec t))
    val f = TypeBase.mk_pattern_fn (mapi mk_case conses)
    fun ss x y = list_mk_icomb (basicSizeSyntax.sum_size_tm, [x, y])
    val m1 = list_mk_rbinop ss sizes
    fun mk_k0 ty = mk_abs (mk_var ("x", ty), numSyntax.zero_tm)
    val m = subst (map (fn f => f |-> mk_k0 (fst (dom_rng (type_of f)))) (free_vars m1)) m1
    val lemma = countable_split |> ISPEC u_sum_ty |> SPECL [f, m]
    val prop = mk_imp (list_mk_conj (T :: assms), snd (dest_imp (concl lemma)))
    val ty_ss = foldr (fn (sf, ss) => ss ++ sf) list_ss (map simpLib.type_ssfrag lemma_tys)
    val lemma2 = TAC_PROOF (([], prop),
      disch_tac
      \\ match_mp_tac (GEN_ALL lemma)
      \\ full_simp_tac bool_ss [countable_def]
      \\ rpt (FIRST_ASSUM (MAP_FIRST EXISTS_TAC o free_vars o concl))
      \\ simp_tac bool_ss [INJ_DEF, IN_UNIV]
      \\ rpt (FIRST [conj_tac, gen_tac, var_case_tac])
      \\ simp_tac ty_ss []
      \\ simp_tac arith_ss [DISJ_IMP_THM, basicSizeTheory.sum_size_def, size_thm]
      \\ full_simp_tac bool_ss [INJ_IFF, IN_UNIV]
    )
  in REWRITE_RULE [countable_Usum, IMP_CONJ_THM] lemma2 end

fun mk_countable ty = let
    val final_concl = mk_icomb (countable_tm, pred_setSyntax.mk_univ ty)
    val lemmas = [unit_countable, num_countable]
    fun mk_thm lemmas = let open ConseqConv
      in DEPTH_CONSEQ_CONV (CONSEQ_REWRITE_CONV ([], lemmas, []))
          CONSEQ_CONV_STRENGTHEN_direction final_concl end
    val thm = mk_thm (mk_countable_lemma ty :: lemmas)
    fun loop (thm, lemmas) = let
        val thm = mk_thm (thm :: lemmas)
        val tys = find_terms pred_setSyntax.is_univ (concl thm)
          |> map (fst o dom_rng o pred_setSyntax.dest_univ)
          |> filter (fn ty2 => ty2 <> ty andalso can TypeBase.induction_of ty2)
      in case tys of [] => thm
        | (ty2 :: _) => loop (thm, mk_countable_lemma ty2 :: lemmas)
      end
  in loop (thm, lemmas) |> REWRITE_RULE [] end

end

