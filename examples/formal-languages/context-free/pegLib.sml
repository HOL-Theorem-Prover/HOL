structure pegLib :> pegLib =
struct

open HolKernel Parse boolLib

fun add_peg_compset cs =
  (computeLib.add_thms
    [grammarTheory.isTOK_def
    ,grammarTheory.language_def
    ,grammarTheory.derive_def
    ,grammarTheory.ptree_fringe_def
    ,grammarTheory.complete_ptree_def
    ,grammarTheory.ptree_head_def
    ,grammarTheory.ptree_size_def
    ,pegTheory.subexprs_def
    ,pegTheory.wfG_def
    ,pegTheory.Gexprs_def
    ,pegexecTheory.poplist_aux_def
    ,pegexecTheory.poplistval_def
    ,pegexecTheory.pegparse_def
    ,pegexecTheory.destResult_def
    ,pegexecTheory.applykont_thm
    ,pegexecTheory.peg_exec_thm
    ] cs;
   List.app (computeLib.add_datatype_info cs o valOf o TypeBase.fetch)
    [``:('a,'b)grammar$symbol``
    ,``:('a,'b)grammar``
    ,``:('a,'b)parsetree``
    ,``:('a,'b,'c)pegsym``
    ,``:('a,'b,'c)peg``
    ,``:('a,'b,'c)kont``
    ,``:('a,'b,'c)evalcase``
    ])

fun derive_compset_distincts ty =
  let
    val ax = TypeBase.axiom_of ty
    val th = Prim_rec.prove_constructors_distinct ax |> hd |> valOf
  in
    CONJ th (GSYM th)
  end

val peg_rules_t = prim_mk_const{Thy = "peg", Name = "peg_rules"}

fun strip_insert t = let
  open pred_setSyntax
  fun recurse acc t =
    case Lib.total dest_insert t of
        NONE => acc
      | SOME (e,s) => recurse (e::acc) s
in
  recurse [] t
end

fun derive_lookup_ths {pegth, ntty, simp} =
  let
    open finite_mapSyntax pred_setTheory finite_mapTheory
    val pegc = lhs (concl pegth)
    val nt_thm = pegexecTheory.peg_nt_thm |> Q.GEN `n` |> Q.GEN `G` |> ISPEC pegc
    val NT_ty = sumSyntax.mk_sum (ntty, numSyntax.num)
    val mkNT_t = Term.inst [alpha |-> ntty, beta |-> numSyntax.num]
                           sumSyntax.inl_tm
    val Grules_t = mk_icomb(peg_rules_t, pegc)
    val fdomrules_t = mk_fdom Grules_t
    val fdom_thm = simp[pegth, FUPDATE_LIST] fdomrules_t
    val cs = strip_insert (rhs (concl fdom_thm))
    fun fdom c =
      AP_TERM (mk_icomb(pred_setSyntax.in_tm, c)) fdom_thm
        |> CONV_RULE
             (RAND_CONV
                  (PURE_REWRITE_CONV [IN_INSERT, OR_CLAUSES, REFL_CLAUSE]))
    val fdoms = map fdom cs
    fun fapp c =
      mk_fapply(Grules_t, c)
               |> simp[pegth, FUPDATE_LIST, FAPPLY_FUPDATE_THM]
    val fapps = map fapp cs
    fun final c = CONV_RULE
                      (RAND_CONV
                           (PURE_REWRITE_CONV (COND_CLAUSES :: fdoms @ fapps)))
                      (SPEC c nt_thm)
  in
    {lookups = map final cs, fdom_thm = fdom_thm, applieds = fapps}
  end




end
