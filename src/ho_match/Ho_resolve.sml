(* ===================================================================== 
 * FILE      : $Id$
 * ===================================================================== *)


structure Ho_resolve :> Ho_resolve =
struct

open HolKernel liteLib Drule Tactical Tactic Conv Ho_net Psyntax;

infix 5 |->
infix THEN

type thm = Thm.thm;
type tactic = Abbrev.tactic;
type conv = Abbrev.conv;


fun ERR p = STRUCT_ERR "HOResolve" p;
fun WRAP_ERR p = STRUCT_WRAP "HOResolve" p;


(* ---------------------------------------------------------------------*)
(* Matching modus ponens.                                               *)
(* ---------------------------------------------------------------------*)

fun MATCH_MP ith =
  let val sth =
      let val tm = concl ith
          val (avs,bod) = strip_forall tm
          val (ant,con) = dest_imp bod
          val (svs,pvs) = partition (C free_in ant) avs
      in if pvs = [] then ith else
          let val th1 = SPECL avs (ASSUME tm)
              val th2 = GENL svs (DISCH ant (GENL pvs (UNDISCH th1)))
          in MP (DISCH tm th2) ith
          end
      end
      handle HOL_ERR _ => ERR("MATCH_MP","Not an implication")
      val match_fun = Ho_match.PART_MATCH (fst o dest_imp) sth
  in fn th => 
      MP (match_fun (concl th)) th
      handle HOL_ERR _ => ERR("MATCH_MP","No match")
  end;;

(* ---------------------------------------------------------------------*)
(* Accept a theorem that, properly instantiated, satisfies the goal     *)
(* ---------------------------------------------------------------------*)

fun MATCH_ACCEPT_TAC thm =
    let val fmatch = Ho_match.PART_MATCH I thm 
        fun atac (asl,w) = ([], K (fmatch w))
    in REPEAT GEN_TAC THEN atac
    end
    handle HOL_ERR _ => ERR("MATCH_ACCEPT_TAC","");

(* ------------------------------------------------------------------------- *)
(* Simplified version of MATCH_MP_TAC to avoid quantifier troubles.          *)
(* ------------------------------------------------------------------------- *)

fun BACKCHAIN_TAC th =
    let val match_fn = Ho_match.PART_MATCH (snd o dest_imp) th
    in fn (asl,w) =>
	let val th1 = match_fn w
	    val (ant,con) = dest_imp(concl th1)
	in ([(asl,ant)],fn [t] => MATCH_MP th1 t)
	end
    end;;


fun MATCH_MP_TAC th = 
 let val sth =
     let val tm = concl th
         val (avs,bod) = strip_forall tm
         val (ant,con) = dest_imp bod
         val th1 = SPECL avs (ASSUME tm)
         val th2 = UNDISCH th1
         val evs = filter(fn v => free_in v ant andalso not(free_in v con)) avs
         val th3 = itlist liteLib.SIMPLE_CHOOSE evs (DISCH tm th2)
         val tm3 = hd(hyp th3)
     in MP (DISCH tm (GEN_ALL (DISCH tm3 (UNDISCH th3)))) th
     end handle HOL_ERR _ => ERR("MATCH_MP_TAC","Bad theorem")
     val match_fun = Ho_match.PART_MATCH (snd o dest_imp) sth
  in fn (asl,w) => 
        let val xth = match_fun w
            val lant = fst(dest_imp(concl xth))
        in ([(asl,lant)],MP xth o hd)
        end handle HOL_ERR _ => ERR("MATCH_MP_TAC","No match")
  end;;

(* ------------------------------------------------------------------------- 
 * Useful instance of more general higher order matching.                    
 * Taken directly from the GTT source code.
 *
 * val LOCAL_COND_ELIM_THM1 = prove
 *     ((--`!P:'a->bool. P(a => b | c) = (~a \/ P(b)) /\ (a \/ P(c))`--),
 *      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);
 *      
 * val conv = HIGHER_REWRITE_CONV[LOCAL_COND_ELIM_THM1];
 * val x = conv (--`(P:'a -> bool) (a => b | c)`--);
 * val x = conv (--`(a + (f x => 0 | n) + m) = 0`--) handle e => Raise e;
 * ------------------------------------------------------------------------- *)


val HIGHER_REWRITE_CONV =
  let fun GINST th =
      let val fvs = subtract (free_vars(concl th)) (free_varsl (hyp th))
          val gvs = map (genvar o type_of) fvs
      in INST (map2 (curry op |->) fvs gvs) th
      end
  in fn ths =>
      let val thl = map (GINST o SPEC_ALL) ths
          val concs = map concl thl
          val lefts = map lhs concs
          val (preds,pats) = unzip(map dest_comb lefts)
          val beta_fns = map2 Ho_match.BETA_VAR preds concs
          val ass_list = zip pats (zip preds (zip thl beta_fns))
          val mnet = itlist (fn p => fn n => enter([],p,p) n) pats empty_net
          fun look_fn t =
              mapfilter (fn p => if can (Ho_match.match_term [] p) t then p 
                                 else fail())
                        (lookup t mnet)
      in fn tm =>
          let val ts = find_terms (fn t => not (look_fn t = []) 
				   andalso free_in t tm) tm
              val stm = Lib.trye hd (sort free_in ts)
              val pat = Lib.trye hd (look_fn stm)
              val (tmin,tyin) = Ho_match.match_term [] pat stm
              val (pred,(th,beta_fn)) = assoc pat ass_list
              val gv = genvar(type_of stm)
              val abs = mk_abs(gv,subst[stm |-> gv] tm)
              val (tmin0,tyin0) = Ho_match.match_term [] pred abs
          in CONV_RULE beta_fn (INST tmin (INST tmin0 (INST_TYPE tyin0 th)))
          end
      end
  handle e as (HOL_ERR _) => WRAP_ERR("HIGHER_REWRITE_CONV",e)
  end;;

end (* struct *)
