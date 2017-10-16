structure Opening :>  Opening =
struct

open HolKernel boolLib liteLib Trace;


fun samerel t1 t2 = can (match_term t1) t2

type congproc  = {relation:term,
		  solver : term -> thm,
		  freevars: term list,
		  depther : thm list * term -> conv} -> conv


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

fun is_congruence tm =
    is_eq tm orelse let
      val (rel,left,right) = dest_binop tm
    in
      (can (ho_match_term [] empty_tmset left) right) andalso
      (can (ho_match_term [] empty_tmset right) left)
    end
   handle HOL_ERR _ => false

fun rel_of_congrule thm = let
  fun aux tm = if is_congruence tm then #1 (dest_binop tm)
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

fun CONGPROC refl congrule =
let

   (* this discharges each antecedent of the congruence rule.  Each
      antecedent is either a side condition or a sub-congruence.
      Side conditions must be passed to the solver, sub-congruences
      must be passed to the depther. *)

   val congrule' = GSPEC (GEN_ALL congrule)
   val nconds = nconds_of_congrule congrule'
   val rel = rel_of_congrule congrule'

   val (conditions,conc) = strip_n_imp nconds (concl congrule')
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
  if not (samerel rel relation) andalso not (same_const rel relation) then
    failwith "not applicable"
  else fn tm =>
  let
    val theta = match_type (#1 (dom_rng (type_of relation))) (type_of tm)
    val relation' = Term.inst theta relation
    val match_thm = matcher (mk_comb(relation',tm))
    val _ = trace(3,OPENING(tm,match_thm))
    val (_,conc) = strip_n_imp nconds (concl match_thm)
    val genvars = filter is_genvar (free_vars (rand conc))

    (* this function does all the work of solving the side conditions
       one by one.  The integer is the number of side conditions
       remaining to be discharged.  Most of the side conditions
       will be sub-congruences of the form (--`A = ?A`--)  *)

    fun process_subgoals (0,match_thm,_) = match_thm
      | process_subgoals (_,_,[]) = raise Fail "process_subgoals BIND"
      | process_subgoals (n,match_thm,flags::more_flags) =
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
          then let
                val (orig,res) = case args of [x,y] => (x,y) | _ => raise Bind
                val genv = #1 (strip_comb res)
                val assum_thms = map ASSUME assums
                fun reprocess thm flag =
                  if flag then CONV_RULE (depther ([],equality)) thm
                    handle HOL_ERR _ =>
                    (trace(5,PRODUCE(concl thm,"UNCHANGED",thm));thm)
                  else thm
                val reprocessed_assum_thms = map2 reprocess assum_thms flags
                val rewr_thm =
                  (depther (reprocessed_assum_thms,oper) orig)
                  handle HOL_ERR _ =>
                  let val thm = refl {Rinst = oper, arg = orig}
                  in (trace(5,PRODUCE(orig,"UNCHANGED",thm));thm)
                  end
                val abs_rewr_thm =
                    CONV_RULE (RAND_CONV (MK_ABSL_CONV ho_vars)) rewr_thm
                val disch_abs_rewr_thm = itlist DISCH assums abs_rewr_thm
                val gen_abs_rewr_thm = GENL ho_vars disch_abs_rewr_thm
                val gen_abs_res =
                    funpow (length ho_vars) rator (rand (concl abs_rewr_thm))
                val spec_match_thm = SPEC gen_abs_res (GEN genv match_thm)
                val new_match_thm = MP spec_match_thm gen_abs_rewr_thm
            in process_subgoals (n-1,new_match_thm,more_flags)
            end
          else let
              fun output() =
                  "Instantiated congruence condition is a side condition: "^
                  term_to_string condition
              val _ = trace (6, LZ_TEXT output)
              val side_condition_thm = solver condition
              val new_match_thm = MP match_thm side_condition_thm
            in process_subgoals (n-1,new_match_thm,more_flags)
            end
        end

    val final_thm = process_subgoals (nconds,match_thm,reprocess_flags)

  in
    if aconv (rand (rator (concl final_thm))) (rand (concl final_thm)) then
      raise HOL_ERR { origin_structure = "Opening",
                      origin_function = "CONGPROC",
                      message = "Congruence gives no change" }
    else (trace(3,PRODUCE(tm,"congruence rule",final_thm)); final_thm)
  end
end;


(* ---------------------------------------------------------------------
 * EQ_CONGPROC
 *
 *  Opening through HOL terms under HOL equality.
 * ---------------------------------------------------------------------*)

fun EQ_CONGPROC {relation,depther,solver,freevars} tm =
 if not (same_const relation boolSyntax.equality) then failwith "not applicable"
 else
 case dest_term tm
  of COMB(Rator,Rand) =>
      (let val th = depther ([],equality) Rator
      in  MK_COMB (th, depther ([],equality)  Rand)
        handle HOL_ERR _ => AP_THM th Rand
      end
       handle HOL_ERR _ => AP_TERM Rator (depther ([],equality)  Rand))
   | LAMB(Bvar,Body) =>
     if op_mem aconv Bvar freevars then
     let val v = variant (freevars@free_vars Body) Bvar
         val th1 = ALPHA_CONV v tm handle e as HOL_ERR _
         => (trace(0,REDUCE("SIMPLIFIER ERROR: bug when alpha converting",tm));
             trace(0,REDUCE("trying to alpha convert to",v));
             Raise e)
         val rhs' = rhs(concl th1)
         val Body' = body rhs' (* v = Bvar *)
         val body_thm = depther ([],equality) Body'
         val eq_thm' = ABS v body_thm
     in
        TRANS th1 eq_thm'
     end
     else let val _ = trace(4,TEXT "no alpha conversion")
              val Bth = depther ([],equality) Body
          in ABS Bvar Bth
          end
   | _ => failwith "unchanged";


end (* struct *)
