structure mp_then :> mp_then =
struct

open HolKernel Drule Conv Parse boolTheory boolSyntax

open thmpos_dtype

fun match_subterm pat = find_term (can (match_term pat))

val op$ = Portable.$
val notT = el 2 (CONJUNCTS NOT_CLAUSES)
val imp_clauses = IMP_CLAUSES |> SPEC_ALL |> CONJUNCTS
val Timp = el 1 imp_clauses
val impF = last imp_clauses

fun mp_then pos (ttac : thm_tactic) ith0 rth (g as (asl,w)) =
  let
    val ith = MP_CANON (GEN_ALL ith0)
    val rth_eqT = EQT_INTRO rth
    val rth_eq = EQF_INTRO rth handle HOL_ERR _ => rth_eqT
    fun m f k t =
      let
        val th0 = PART_MATCH' f ith t
        val th =
            CONV_RULE
              (STRIP_QUANT_CONV
                 (FORK_CONV (EVERY_CONJ_CONV $ TRY_CONV $ REWR_CONV rth_eqT,
                             (REWR_CONV rth_eq ORELSEC
                              TRY_CONV (RAND_CONV (REWR_CONV rth_eq) THENC
                                        REWR_CONV notT))) THENC
                  TRY_CONV (REWR_CONV Timp)))
              th0
      in
        ttac th g
      end handle HOL_ERR _ => k()
    fun conj f t = t |> dest_imp |> #1 |> strip_conj |> f
    val max = ith |> concl |> strip_forall |> #2 |> conj length
    val fail = mk_HOL_ERR "mp_then" "mp_then" "No match"
    val t = concl rth
  in
    case pos of
        Any =>
        let
          fun doit (n:int) =
            if n > max then raise fail
            else m (conj (el n)) (fn _ => doit (n + 1)) t
        in
          doit 1
        end
      | Pos f => m (conj f) (fn _ => raise fail) t
      | Pat q =>
        let
          open TermParse
          val pats =
              prim_ctxt_termS Parse.Absyn (term_grammar())
                              (HOLset.listItems (FVL (w::asl) empty_tmset))
                              q
          fun doit ps n =
            if n > max then raise fail
            else
              case seq.cases ps of
                  NONE => doit pats (n + 1)
                | SOME (pat, rest) =>
                    m (fn t => let val subterm = conj (el n) t
                               in
                                 if can (match_subterm pat) subterm then
                                   subterm
                                 else raise fail
                               end)
                      (fn _ => doit rest n)
                   t
        in
          doit pats 1
        end
      | Concl => m (fn t => t |> dest_imp |> #2)
                   (fn _ => raise fail)
                   (dest_neg t handle HOL_ERR _ => mk_neg t)
  end

end
