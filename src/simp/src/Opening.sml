structure Opening :>  Opening =
struct

open HolKernel boolLib liteLib Trace BBConv;


fun samerel t1 t2 = can (match_term t1) t2

type congproc  = {relation:term,
                  solver : conv,
                  freevars: term list,
                  depther : thm list * term -> bbconv} -> bbconv


fun WRAP_ERR x = STRUCT_WRAP "Opening" x;
fun ERR x = STRUCT_ERR "Opening" x;

(* ---------------------------------------------------------------------
 * is_congruence
 *    Test if a term is a valid conclusion of a congruence rule,
 *
 * EXAMPLES
 *   is_congruence (--`(A ==> B) = (A' ==> B')`--);
 *   is_congruence (--`(A ==> B) ==> (A' ==> B')`--);
 *   is_congruence (--`(A ==> B) <== (A' ==> B')`--);
 *   is_congruence (--`(!x:'a. P x) <== (!x:'a. P' x)`--);
 *   is_congruence (--`(A <== A') ==> (A ==> B) ==> (A' ==> B')`--); (*false*)
 *
 * rel_of_congruence
 *   Discover the relation a congruence is expressed over.
 *
 * EXAMPLES
 *   rel_of_congrule imp_imp_rule;
 *   rel_of_congrule imp_pmi_rule;
 *   rel_of_congrule pmi_imp_rule;
 *   rel_of_congrule pmi_neg_rule;
 *   rel_of_congrule imp_forall_rule;
 *
 * nconds_of_congrule
 *   Discover how many side conditions a congruence rule has.  Nb. Can't
 * just call strip_imp as the congruence may be expressed over (--`$==>`--)
 *
 *   nconds_of_congrule imp_imp_rule;  (* 2 *)
 *   nconds_of_congrule imp_pmi_rule;  (* 2 *)
 *   nconds_of_congrule pmi_imp_rule;  (* 2 *)
 *   nconds_of_congrule pmi_neg_rule;  (* 1 *)
 *   nconds_of_congrule pmi_forall_rule;  (* 1 *)
 *   nconds_of_congrule imp_forall_rule;  (* 1 *)
 * ---------------------------------------------------------------------*)

fun dest_binop t = let
  val (fx,y) = dest_comb t
  val (f,x) = dest_comb fx
in
  (f,x,y)
end

fun relOfTm t = rator (rator t)

fun is_congruence tm =
    is_eq tm orelse let
      val (rel,left,right) = dest_binop tm
    in
      (can (ho_match_term [] empty_tmset left) right) andalso
      (can (ho_match_term [] empty_tmset right) left)
    end
   handle HOL_ERR _ => false

fun rel_of_congrule thm = let
  fun aux tm = if is_congruence tm then relOfTm tm
               else aux (snd (dest_imp tm))
in
  aux (snd(strip_forall (concl thm)))
end handle e => WRAP_ERR("rel_of_congrule",e)

fun nconds_of_congrule thm = let
  fun aux tm = if is_congruence tm then 0 else aux (snd(dest_imp tm)) + 1
in
  aux (snd(strip_forall(concl thm)))
end handle e => WRAP_ERR("nconds_of_congrule",e)

(* ---------------------------------------------------------------------
 * CONGPROC : REFL -> congrule -> congproc
 *
 * ---------------------------------------------------------------------*)

fun strip_n_imp 0 tm = ([],tm)
  | strip_n_imp n tm =
      let val (x,y) = dest_imp tm
          val (z,w) = strip_n_imp (n-1) y
      in (x::z,w)
      end;

fun strip_ncomb 0 A tm = SOME (tm, A)
  | strip_ncomb n A tm =
    case Lib.total dest_comb tm of
        NONE => NONE
      | SOME (fxs,x) => strip_ncomb (n - 1) (x::A) fxs

(* ---------------------------------------------------------------------
 * strip_imp_until_rel
 *
 * this function strips implications off a sub-congruence until
 * it is a relation (i.e. the rhs is one of the genvars we have chosen)
 * or it is no longer an implication (in which case the sub-congruence
 * is really a side condition.
 *
 * ---------------------------------------------------------------------*)


fun strip_imp_until_rel genvars tm =
  if is_var (rand tm) andalso op_mem aconv (rand tm) genvars then ([],tm)
  else
    let
      val (x,y) = dest_imp tm
      val (z,w) = strip_imp_until_rel genvars y
    in
      (x::z,w)
    end handle HOL_ERR _ => ([],tm);

(* ---------------------------------------------------------------------
 * CONGPROC : REFL -> congrule -> congproc
 *
 * ---------------------------------------------------------------------*)

val equality = boolSyntax.equality

fun CONGPROC refl trans congrule =
let

   (* this discharges each antecedent of the congruence rule.  Each
      antecedent is either a side condition or a sub-congruence.
      Side conditions must be passed to the solver, sub-congruences
      must be passed to the depther. *)

   val congrule' = GSPEC (GEN_ALL congrule)
   val nconds = nconds_of_congrule congrule'
   val rel = rel_of_congrule congrule'

   val (conditions,conc) = strip_n_imp nconds (concl congrule')
   val normal = let val (_, l,r) = dest_binop conc
                in
                  can (match_term l) r andalso can (match_term r) l
                end
   val matcher =
      HO_PART_MATCH (rator o snd o strip_n_imp nconds) congrule'

 (* work out whether context assumptions need to be reprocessed *)
 (* e.g "~g" in the "else" branch of COND_CONG needs to be.     *)

   val vars = free_vars (concl congrule')
   fun reprocess_flag assum = if is_var assum then false else true;
   val reprocess_flags =
       map (map reprocess_flag o fst o strip_imp_until_rel vars o
            #2 o strip_forall)
           conditions

in fn {relation,solver,depther,freevars} =>
  if not (samerel rel relation) andalso not (same_const rel relation) then (
    trace(
      5,
      Trace.LZ_TEXT(fn () =>
         "rejecting CONGPROC theorem " ^ thm_to_string congrule ^
         " as existing relation = " ^ term_to_string relation)
    );
    failwith "not applicable"
  ) else fn th0 =>
  let
    val depther : thm list * term -> bbconv = depther
    val tm0 = rand (concl th0)
    val theta = match_type (#1 (dom_rng (type_of relation))) (type_of tm0)
    val relation' = Term.inst theta relation
    val match_thm = matcher (mk_comb(relation',tm0))
    val _ = trace(3,OPENING(tm0,match_thm))
    val (_,conc) = strip_n_imp nconds (concl match_thm)
    val genvars = filter is_genvar (free_vars (rand conc))

    (* this function does all the work of solving the side conditions
       one by one.  The integer is the number of side conditions
       remaining to be discharged.  Most of the side conditions
       will be sub-congruences of the form (--`A = ?A`--)  *)

    fun process_subgoals (0,match_thm,_,allunch) = (match_thm, allunch)
      | process_subgoals (_,_,[],_) = raise Fail "process_subgoals BIND"
      | process_subgoals (n,match_thm,flags::more_flags,allunch) =
        let val condition = #1 (dest_imp (concl match_thm))

           (* work out whether the condition is a congruence condition
              or a side condition.  If it is two place and the
              head combinator of the rhs is one of the subterms
              in the congruence (see subterms above) then it
              is a congruence condition *)
            val (ho_vars,bdy1) = strip_forall condition
            val (assums,bdy2) = strip_imp_until_rel genvars bdy1
            val (oper,args) = let
              val (f,x,y) = dest_binop bdy2
            in
              (f,[x,y])
            end handle HOL_ERR _ => strip_comb bdy2
        in
          if length args = 2 andalso
             op_mem aconv (#1 (strip_comb (el 2 args))) genvars
          then
            let
              val (orig,res) = case args of [x,y] => (x,y) | _ => raise Bind
              val origth : thm = refl {Rinst = oper, arg = orig}
              val genv = #1 (strip_comb res)
              val assum_thms = map ASSUME assums
              fun reprocess thm flag =
                  if flag then
                    BBCONV_RULE (depther ([],equality)) thm
                    handle HOL_ERR _ =>
                           (trace(5,PRODUCE(concl thm,"UNCHANGED",thm));thm)
                  else thm
              val reprocessed_assum_thms = map2 reprocess assum_thms flags
              val (rewr_thm,changed) = (
                trace (7,
                  LZ_TEXT (fn () =>
                    "oper: " ^ term_to_string oper ^
                    " rpa_thms: [" ^
                    String.concatWith ", "
                                      (map thm_to_string reprocessed_assum_thms) ^
                    "] origth: " ^ thm_to_string origth));
                (depther (reprocessed_assum_thms,oper) origth,true)
              ) handle e as HOL_ERR _ => (
                    trace(5,PRODUCE(orig,"UNCHANGED",origth));
                    trace(7, LZ_TEXT(fn () => "exn: " ^ General.exnMessage e));
                    (origth,false)
                  )
              val absify = CONV_RULE (RAND_CONV (MK_ABSL_CONV ho_vars))
              val abs_rewr_thm =
                  if null ho_vars then rewr_thm
                  else
                    let val r = rand (concl rewr_thm)
                    in
                      case strip_ncomb (length ho_vars) [] r of
                          NONE => absify rewr_thm
                        | SOME (fxs, sfx) =>
                          if list_eq aconv sfx ho_vars then
                            let val fvs = free_vars fxs
                            in
                              if List.all (fn hv => not (op_mem aconv hv fvs))
                                          ho_vars
                              then rewr_thm
                              else absify rewr_thm
                            end
                          else absify rewr_thm
                    end
              val disch_abs_rewr_thm = itlist DISCH assums abs_rewr_thm
              val gen_abs_rewr_thm = GENL ho_vars disch_abs_rewr_thm
              val gen_abs_res =
                  funpow (length ho_vars) rator (rand (concl abs_rewr_thm))
              val spec_match_thm = SPEC gen_abs_res (GEN genv match_thm)
              val new_match_thm = MP spec_match_thm gen_abs_rewr_thm
            in
              process_subgoals (n-1,new_match_thm,more_flags,
                                allunch andalso not changed)
            end
          else let
            fun output() =
                "Instantiated congruence condition is a side condition: "^
                term_to_string condition
            val _ = trace (6, LZ_TEXT output)
            val side_condition_thm = solver condition
            val new_match_thm = MP match_thm side_condition_thm
          in process_subgoals (n-1,new_match_thm,more_flags,allunch)
          end
        end

    val (final_thm,allunch) =
        process_subgoals (nconds,match_thm,reprocess_flags,normal)

  in
    if allunch then
      (* note critical link between this exception and traversal code in
         Traverse.FIRSTCQC_CONV *)
      raise mk_HOL_ERR "Opening" "CONGPROC" "Congruence gives no change"
    else (trace(3,PRODUCE(tm0,"congruence rule",final_thm));
          trans th0 final_thm)
  end
end;


(* ---------------------------------------------------------------------
 * EQ_CONGPROC
 *
 *  Opening through HOL terms under HOL equality.
 * ---------------------------------------------------------------------*)

fun EQ_CONGPROC {relation,depther,solver,freevars} th =
    let
      val c = concl th
      val tm0 = rhs (concl th)
      val _ = same_const (relOfTm c) boolSyntax.equality orelse
              (trace(
                  5,
                  Trace.LZ_TEXT(fn () =>
                    "failing to EQ_CONGPROC-open theorem " ^ thm_to_string th ^
                    " with relation = " ^ term_to_string relation)
                );
               failwith "not applicable")
    in
      case dest_term tm0 of
          COMB _ =>
          let val (fth0, xth0, mk_comb_fn) = Mk_comb th
          in
            let val fth = depther ([],equality) fth0
                val xth = depther ([],equality) xth0 handle HOL_ERR _ => xth0
            in
              mk_comb_fn fth xth
            end
            handle (* should only get an exn if fth failed to change *)
            HOL_ERR _ => mk_comb_fn fth0 (depther ([],equality) xth0)
          end
        | LAMB(Bvar,Body) =>
          if op_mem aconv Bvar freevars then
            let val v = variant (freevars@free_vars Body) Bvar
                val th1 = ALPHA_CONV v tm0
                          handle e as HOL_ERR _
                                 => (trace(0,REDUCE("SIMPLIFIER ERROR: bug when alpha converting",tm0));
                                     trace(0,REDUCE("trying to alpha convert to",v));
                                     Raise e)
                val (bv, bodyth0, mk_abs_fn) = Mk_abs (TRANS th th1)
                val bodyth = depther ([],equality) bodyth0
            in
              mk_abs_fn bodyth
            end
          else
            let val _ = trace(4,TEXT "no alpha conversion")
                val (bv,bodyth0,mk_abs_fn) = Mk_abs th
            in
              mk_abs_fn (depther ([],equality) bodyth0)
            end
        | _ => failwith "unchanged"
    end


end (* struct *)
