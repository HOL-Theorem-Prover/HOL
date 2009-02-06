structure Rules :> Rules =
struct

open HolKernel boolLib pairLib wfrecUtils;


val ERR = mk_HOL_ERR "Rules";

fun sthat P x = P x handle Interrupt => raise Interrupt
                         |     _     => false;

fun simpl_conv thl =
  let open RW
      val RWC = Rewrite Fully
                   (Simpls(std_simpls,thl),
                    Context([],DONT_ADD),
                    Congs[boolTheory.IMP_CONG],
                    Solver always_fails)
      fun simpl tm =
       let val th = Conv.THENC(RWC,Conv.DEPTH_CONV GEN_BETA_CONV) tm
           val (lhs,rhs) = dest_eq(concl th)
       in if aconv lhs rhs then th else TRANS th (simpl rhs)
       end
  in simpl
  end;

fun is_triv_rw tm = uncurry aconv (dest_eq tm) handle HOL_ERR _ => false;

fun non_triv thl = gather (not o is_triv_rw o concl) thl

(*---------------------------------------------------------------------------*)
(* PURE_REWRITE_RULE plus generalized beta conversion.                       *)
(*---------------------------------------------------------------------------*)

fun simplify thl = 
 let val rewrite = PURE_REWRITE_RULE (non_triv thl) (* PURE_ONCE_REWRITE_RULE *)
     fun simpl th =
      let val th' = GEN_BETA_RULE (rewrite th)
          val (_,c1) = dest_thm th
          val (_,c2) = dest_thm th'
      in if aconv c1 c2 then th else simpl th'
      end
 in simpl
 end;

val RIGHT_ASSOC = PURE_REWRITE_RULE [GSYM boolTheory.DISJ_ASSOC];

fun FILTER_DISCH_ALL P th = itlist DISCH (filter (sthat P) (Thm.hyp th)) th;

(*----------------------------------------------------------------------------
 *
 *         A |- M
 *   -------------------   [v_1,...,v_n]
 *    A |- ?v1...v_n. M
 *
 *---------------------------------------------------------------------------*)

fun EXISTL vlist thm =
   itlist (fn v => fn thm => EXISTS(mk_exists(v,concl thm),v) thm)
          vlist thm;

(*----------------------------------------------------------------------------
 *
 *       A |- M[x_1,...,x_n]
 *   ----------------------------   [(x |-> y)_1,...,(x |-> y)_n]
 *       A |- ?y_1...y_n. M
 *
 *---------------------------------------------------------------------------*)

fun IT_EXISTS theta thm =
 itlist (fn (b as {redex,residue}) => fn thm =>
           EXISTS(mk_exists(residue, subst [b] (concl thm)), redex) thm)
        theta thm;

(*----------------------------------------------------------------------------
 *
 *                   A1 |- M1, ..., An |- Mn
 *     ---------------------------------------------------
 *     [A1 |- M1 \/ ... \/ Mn, ..., An |- M1 \/ ... \/ Mn]
 *
 *---------------------------------------------------------------------------*)

fun EVEN_ORS thms =
  let fun blue ldisjs [] _ = []
        | blue ldisjs (th::rst) rdisjs =
            let val rdisj_tl = list_mk_disj(Lib.trye tl rdisjs)
            in itlist DISJ2 ldisjs (DISJ1 th rdisj_tl)
               :: blue (ldisjs@[concl th]) rst (Lib.trye tl rdisjs)
            end
            handle HOL_ERR _ => [itlist DISJ2 ldisjs th]
   in
   blue [] thms (map concl thms)
   end;

(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*         v = pat[v1,...,vn]  |- M[x]                                       *)
(*    ------------------------------------------                             *)
(*      ?v1 ... vn. v = pat[v1,...,vn] |- M[x]                               *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun CHOOSER v (tm,thm) =
 let val ex_tm = mk_exists(v,tm)
 in (ex_tm, CHOOSE(v, ASSUME ex_tm) thm)
 end;

fun LEFT_ABS_VSTRUCT thm =
 let open boolSyntax
     val veq = Lib.trye hd (filter (can dest_eq) (Thm.hyp thm))
     val pat = rhs veq
 in snd(itlist CHOOSER (free_vars_lr pat) (veq,thm))
 end;

(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*      Gamma, (x = pat[v1,...,vn]) /\ constraints |- M[x]                   *)
(*    ------------------------------------------------------------------     *)
(*      Gamma, ?v1 ... vn. (x = pat[v1,...,vn]) /\ constraints |- M[x]       *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun LEFT_EXISTS thm =
 case filter (can (dest_eq o hd o strip_conj)) (Thm.hyp thm)
  of [] => raise ERR "LEFT_EXISTS" "expected an eqn in hyps"
   | veq_conj :: _ =>
     let val (_,pat) = dest_eq (hd (strip_conj veq_conj))
     in snd (itlist CHOOSER (free_vars_lr pat) (veq_conj,thm))
     end;

end (* Rules *)
