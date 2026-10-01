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

(* the size of a value of a type, composed from the operators' own:
   `list_size rose_tricky_size` of a list of them *)
fun size_term ty =
    let val zero = mk_abs (mk_var ("x", ty), numSyntax.zero_tm)
    in
      if is_vartype ty then zero
      else
        let val (_, args) = dest_type ty
            val sz = #1 (TypeBase.size_of ty)
        in if null args then sz else list_mk_icomb (sz, map size_term args) end
        handle HOL_ERR _ => zero
    end

fun mk_countable_lemma ty = let
    (* The older datatype construction presented a type recursing under
       an operator as a mutually recursive family, and defined a size
       function for each member -- the `<ty>1_size` of a list of the
       type.  The BNF construction defines the type's own and nothing
       else, so the family is what legacyInduction makes of the type's
       principle, and each member's size is composed rather than named. *)
    val ind0 = TypeBase.induction_of ty
    val ind = legacyInduction.mutual_induction
                (legacyInduction.operators_of ind0) ind0
              handle HOL_ERR _ => ind0
    val conses = find_terms (fn t => is_comb t andalso is_var (rator t)) (concl ind)
      |> map rand |> filter (not o is_var)
    val lemma_tys = concl ind |> strip_forall |> snd |> dest_imp |> snd
      |> strip_conj |> map (type_of o fst o dest_forall)
    val sizes = map size_term lemma_tys
(*  The size definition stored in the theory segment says of a member's
    contents what the construction's axiom handed over -- `list_size (\x. x)
    (MAP rose_tricky_size l)` -- where the TypeBase holds the same equation
    with the fold stated, which is what a composed size is written as.  So
    this takes the TypeBase's, for the type and for the operators alike. *)
    fun eqnsFor t = [#2 (TypeBase.size_of t)] handle HOL_ERR _ => []
    val size_thm = LIST_CONJ (List.concat (map eqnsFor lemma_tys))
    fun ty_n ty = total (index (fn ty2 => ty2 = ty)) lemma_tys
    val ex_param_tys = map (snd o strip_comb) conses |> List.concat |> map type_of
      |> HOLset.fromList Type.compare |> HOLset.listItems
      |> filter (not o Option.isSome o ty_n)
    val assms = map (curry mk_icomb countable_tm o pred_setSyntax.mk_univ) ex_param_tys
    val sum_ty = sumSyntax.list_mk_sum lemma_tys
    val u_sum_ty = pred_setSyntax.mk_univ sum_ty
    val _ = HOL_MESG ("Making countable lemma for: " ^ term_to_string u_sum_ty)
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
    (* A lemma that does not discharge the type it is about leaves that
       type to be asked for again, and the loop would go round for ever
       gathering lemmas.  So each type is asked for once. *)
    fun loop (thm, lemmas, asked) = let
        val thm = mk_thm (thm :: lemmas)
        val tys = find_terms pred_setSyntax.is_univ (concl thm)
          |> map (fst o dom_rng o pred_setSyntax.dest_univ)
          |> filter (fn ty2 => ty2 <> ty andalso can TypeBase.induction_of ty2)
      in case filter (fn ty2 => not (Lib.mem ty2 asked)) tys of
          [] => (case tys of
                     [] => thm
                   | ty2 :: _ =>
                     raise mk_HOL_ERR "countable_typesLib" "mk_countable"
                       ("no lemma of " ^ type_to_string ty2 ^
                        " settles it; " ^ type_to_string ty ^
                        " is left asking for it"))
        | (ty2 :: _) =>
          loop (thm, mk_countable_lemma ty2 :: lemmas, ty2 :: asked)
      end
  in loop (thm, lemmas, [ty]) |> REWRITE_RULE [] end

end
