structure Diff :> Diff =
struct

open HolKernel Parse boolLib hol88Lib jrhUtils limTheory;


val xreal    = Term`x:real`;
val lreal    = Term`l:real`
val diffl_tm = Term`$diffl`;
val pow_tm   = Term`$pow`;

(*---------------------------------------------------------------------------*)
(* A conversion to differentiate expressions                                 *)
(*---------------------------------------------------------------------------*)

val basic_diffs = ref ([]:thm list);


(*---------------------------------------------------------------------------*)
(* DIFF_CONV "fn t => f[t]" =                                                *)
(*   |- !l1..ln x. conditions[x] ==> ((fn t => f[t]) diffl f'[x])(x)         *)
(* Where the li's are hypothetical derivatives for unknown sub-functions     *)
(*---------------------------------------------------------------------------*)
val iths = map TAUT_CONV
             [(--`(a ==> c) /\ (b ==> d) ==> ((a /\ b) ==> (c /\ d))`--),
              (--`c /\ (b ==> d) ==> (b ==> (c /\ d))`--),
              (--`(a ==> c) /\ d ==> (a ==> (c /\ d))`--),
              (--`c /\ d ==> c /\ d`--)];

val [DIFF_INV', DIFF_DIV'] =
   map (ONCE_REWRITE_RULE[TAUT_CONV (--`a /\ b ==> c = a ==> b ==> c`--)])
          [DIFF_INV, REWRITE_RULE[CONJ_ASSOC] DIFF_DIV];

val comths = [DIFF_ADD, DIFF_MUL, DIFF_SUB, DIFF_DIV', DIFF_NEG, DIFF_INV'];

val CC = TAUT_CONV (--`a ==> b ==> c = a /\ b ==> c`--);

fun DIFF_CONV tm =
  let val xv = variant (frees tm) xreal
      fun is_diffl tm =
        (funpow 3 rator tm = diffl_tm handle HOL_ERR _ => false)
      fun make_assoc th =
        let val tm1 = (snd o strip_imp o snd o strip_forall o concl) th
            val tm2 = (rand o rator o rator) tm1 in
            if is_abs tm2 then
              (fst(strip_comb(body tm2)),th)
            else
              let val th1 = ETA_CONV (mk_abs(xreal,mk_comb(tm2, xreal)))
                  val th2 = AP_TERM diffl_tm (SYM th1)
                  val th3 = ONCE_REWRITE_RULE[th2] th
              in
                (fst(strip_comb tm2),th3)
              end
        end
      val (cths, bths) = case map (map make_assoc) [comths, !basic_diffs]
                         of [cths, bths] => (cths, bths)
                          | _ => raise ERR "DIFF_CONV" ""
      fun ICONJ th1 th2 =
        let val (th1a, th2a) = case map (SPEC xv) [th1, th2]
                               of [th1a, th2a] => (th1a, th2a)
                                | _ => raise ERR "DIFF_CONV" ""
        in
          GEN xv (tryfind (C MATCH_MP (CONJ th1a th2a)) iths)
        end
      fun diff tm =
        let val (v,bod) = dest_abs tm in
            if not (free_in v bod) then
              GEN xv (SPECL [bod, xv] DIFF_CONST)
            else if bod = v then
              GEN xv (SPEC xv DIFF_X)
            else
              let val (opp,args) = strip_comb bod in
              (let val th1 = snd(assoc opp cths)
                   val nargs = map (curry mk_abs v) args
                   val dargs = map diff nargs
                   val th2 = end_itlist ICONJ dargs
                   val th3 = UNDISCH (SPEC xv th2)
                             handle HOL_ERR _ => SPEC xv th2
                   val th4 = MATCH_MP th1 th3
                   val th5 = DISCH_ALL th4 handle _ => th4
                   val th6 = Rewrite.GEN_REWRITE_RULE I Rewrite.empty_rewrites
                              [CC] th5 handle HOL_ERR _ => th5
                   val th7 = CONV_RULE(REDEPTH_CONV BETA_CONV) th6 in
               GEN xv th7 end handle HOL_ERR _ =>
               let val arg = Lib.trye hd args
                   val narg = mk_abs(v,arg)
                   val th1 = if opp = pow_tm
                             then SPEC (last args) DIFF_POW
                             else snd(assoc opp bths)
                   val th2 = GEN xv (SPEC (mk_comb(narg,xv)) th1)
                   val th3 = diff narg
                   val th4 = SPEC xv (ICONJ th2 th3)
                   val th5 = MATCH_MP DIFF_CHAIN (UNDISCH th4
                             handle HOL_ERR _ => th4)
                   val th6 = CONV_RULE(REDEPTH_CONV BETA_CONV) (DISCH_ALL th5)
               in
               GEN xv th6
               end handle HOL_ERR _ =>
                    let val tm1 = mk_comb(diffl_tm, tm)
                        val var = variant (frees tm) lreal
                        val tm2 = mk_comb(tm1,var)
                        val tm3 = mk_comb(tm2,xv)
                    in
                      GEN xv (DISCH tm3 (ASSUME tm3))
                    end)
              end end
      val tha = diff tm
      val cjs = strip_conj (fst (dest_imp
                  (snd (strip_forall (concl tha))))) handle HOL_ERR _ => []
      val cj2 = filter is_diffl cjs
      val fvs = map (rand o rator) cj2
      val thb = itlist GEN fvs tha
  in
   CONV_RULE (ONCE_DEPTH_CONV(C ALPHA tm)) thb
end;

end;
