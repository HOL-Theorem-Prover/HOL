structure reachTools =
struct

local

open Globals HolKernel Parse

open bossLib pairTheory pred_setTheory pred_setLib stringLib
     listTheory simpLib pairSyntax pairLib PrimitiveBddRules
     DerivedBddRules Binarymap PairRules pairTools setLemmasTheory
     muSyntax muSyntaxTheory muTheory boolSyntax Drule Tactical Conv
     Rewrite Tactic boolTheory listSyntax stringTheory stringBinTree
     boolSimps pureSimps listSimps numLib reachTheory bddTools ksTools

fun t2tb vm t = DerivedBddRules.GenTermToTermBdd (!DerivedBddRules.termToTermBddFun) vm t

in


fun RiterRep n b = List.app print ["Depth: ", term_to_string n, ", ", Int.toString(bdd.nodecount b), " nodes, ", Real.toString(statecount b), " states\n"];

fun RiterComputeReachable tbR tbS  s sp2s n state state' Rname Iname etqcth =
    let val tbS2 = BddOp(bdd.Or,tbS, (BddReplace sp2s (BddAppex s (bdd.And,tbR,tbS))))
	val rcth =  ISPECL [Rname,Iname,n,state] reachTheory.ReachableRecSimp
	val rcth' = PURE_ONCE_REWRITE_RULE [GEN_PALPHA_CONV state' (snd(dest_disj(rhs(concl rcth))))] rcth
	val rcth'' = PURE_ONCE_REWRITE_RULE [SPEC n etqcth] rcth'
	val tbS2' = BddEqMp (SYM rcth'') tbS2
	val _ =  RiterRep n (getBdd tbS)
    in if (bdd.equal (getBdd tbS) (getBdd tbS2'))
       then let val eqth = PairRules.PGEN state (BddThmOracle (BddOp(bdd.Biimp,tbS,tbS2')))
	        val feqth = ISPECL [fst(dest_comb(getTerm tbS)),fst(dest_comb(getTerm tbS2'))] (GSYM FUN_EQ_THM)
		val eqth2 = REWRITE_RULE [REWRITE_RULE [GEN_PALPHA_CONV state (lhs (concl feqth))] feqth] eqth
	    in BddEqMp (AP_THM (SYM (MATCH_MP (ISPECL [Rname,Iname,n] reachTheory.ReachableFP) eqth2)) state) tbS end
       else RiterComputeReachable tbR tbS2' s sp2s ``SUC ^n`` state state' Rname Iname etqcth end;

fun computeReachable_aux R1 I1 tbR tbI vm =
    let	val state = rand(lhs(concl(SPEC_ALL I1)))
	val state' = mk_primed_state state
	val (s,s') = (strip_pair ## strip_pair) (state,state')
	val Iname = rator(lhs(concl(SPEC_ALL I1)))
	val Rname = rator(lhs(concl(SPEC_ALL R1)))
	val tbI' =  BddEqMp (SYM (REWRITE_RULE [I1] (AP_THM (REWRITE_CONV [reachTheory.ReachableRec_def]
									  ``ReachableRec (^Rname) (^Iname) (0:num)``) state))) tbI
        (*val _ = List.app (print o term_to_string) s*)
	val lFvLhsR = free_vars(lhs(concl(SPEC_ALL(R1))))
	val sp = List.drop(rev(lFvLhsR),length(lFvLhsR) div 2)
        (*val _ = List.app (print o term_to_string) sp*)
	val sp2s = ListPair.map (fn (vp,v) => (BddVar true vm vp,BddVar true vm v)) (sp,s)
	val etqcgl = mk_forall(``n:num``,mk_eq(mk_pexists(state',mk_conj(mk_comb(Rname,mk_pair(state',state)),
					 list_mk_comb(inst [alpha |-> type_of state] ``ReachableRec``,[Rname,Iname,``n:num``,state']))),
					       list_mk_exists(s',mk_conj(mk_comb(Rname,mk_pair(state',state)),
					 list_mk_comb(inst [alpha |-> type_of state] ``ReachableRec``,[Rname,Iname,``n:num``,state'])))))
	(*val _ = print_term etqcgl
	val _ = print " h3\n"*)
	val etqcth = prove(etqcgl,REWRITE_TAC [ELIM_TUPLED_QUANT_CONV (lhs(snd(dest_forall etqcgl)))])
	(*val _ = print "h4\n"*)
    in RiterComputeReachable tbR tbI' s sp2s ``0:num`` state state' Rname Iname etqcth end;

(* ASSERT: R1 and I1 are equational predicate definitions of HOL type thm *)
fun RcomputeReachable I1 R1 Ric vm =
    let val tbR = BddEqMp (SYM (SPEC_ALL R1)) (t2tb vm (rhs(concl(SPEC_ALL(R1)))))
	val tbI = t2tb vm (rhs(concl(SPEC_ALL(I1))))
    in computeReachable_aux R1 I1 tbR tbI vm end

(* same as RcomputeReachable but in this case the tb's have already been computed *)
fun computeReachable R1 I1 tbRl tbI vm Ric =
let val tbR = if Ric then BddListConj vm (List.map snd tbRl) else BddListDisj vm (List.map snd tbRl)
in computeReachable_aux R1 I1 (BddEqMp (SYM (SPEC_ALL R1)) tbR) tbI vm end
 end
end