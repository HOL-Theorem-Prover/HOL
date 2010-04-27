structure pred_setSimps :> pred_setSimps =
struct

  open HolKernel boolLib pred_setTheory

  val PRED_SET_ss = simpLib.merge_ss [BasicProvers.thy_ssfrag "pred_set",
                                      SET_SPEC_ss]

  val PRED_SET_AC_ss = simpLib.SSFRAG
    {name=SOME"PRED_SET_AC",
     convs = [], rewrs = [], filter = NONE, dprocs = [], congs = [],
     ac = [(UNION_ASSOC, UNION_COMM), (INTER_ASSOC, INTER_COMM)]
     }

  val NOT_IN_EMPTY' = NOT_IN_EMPTY |> SPEC_ALL |> EQF_INTRO |> GEN_ALL
  val IN_UNIV' = IN_UNIV |> SPEC_ALL |> EQT_INTRO |> GEN_ALL

  fun GSPEC_SIMP_CONV t = let
    open pairSyntax pred_setSyntax
    fun ERR s = mk_HOL_ERR "pred_setSimps" "GSPEC_SIMP_CONV" s
    val (f, arg) = dest_comb t
    val _ = same_const f gspec_tm orelse
            raise ERR "Inapplicable: term not a GSPEC"
    val (vars,body) = dest_pabs arg
    val (_,pred) = dest_pair body
    val (elty,_) = dom_rng (type_of t)
    val basethm0 =
        if same_const pred boolSyntax.T then IN_UNIV'
        else if same_const pred boolSyntax.F then NOT_IN_EMPTY'
        else raise ERR "Inapplicable: gspec body not T or F"
    val basethm = INST_TYPE [alpha |-> elty] basethm0
    val v = genvar elty
    val v_IN_t = mk_in(v,t)
    val v_IN_t_th = (PGspec.SET_SPEC_CONV GSPECIFICATION THENC
                     PURE_REWRITE_CONV [AND_CLAUSES, EXISTS_SIMP]) v_IN_t
    val rhs_th = basethm |> SPEC v |> SYM
    val vrhs_th = TRANS v_IN_t_th rhs_th
                  handle HOL_ERR _ =>
                         raise ERR "Inapplicable: gspec pattern may preclude \
                                   \universality"
    val gvrhs_th = GEN v vrhs_th
  in
    CONV_RULE (REWR_CONV (GSYM EXTENSION)) gvrhs_th
  end

  val GSPEC_SIMP_ss = let
    open pred_setSyntax pairSyntax
    val f = mk_var ("f", beta --> mk_prod(alpha, bool))
  in
    simpLib.SSFRAG {
      ac = [], name = SOME "GSPEC_SIMP", congs = [],
      convs = [{key = SOME ([], mk_comb(gspec_tm, f)),
                conv = K (K GSPEC_SIMP_CONV), trace = 2,
                name = "GSPEC_SIMP_CONV"}], rewrs = [],
      dprocs = [], filter = NONE
    }
  end

  val _ = BasicProvers.augment_srw_ss [GSPEC_SIMP_ss]


end (* pred_setSimps *)
