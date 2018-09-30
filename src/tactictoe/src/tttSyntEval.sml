(* ========================================================================== *)
(* FILE          : tttSyntEval.sml                                            *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSyntEval :> tttSyntEval =
struct

open HolKernel boolLib Abbrev tttTools tttSynt tttPredict 
  tttExec tttTermData tttFeature

val ERR = mk_HOL_ERR "tttSyntEval"

(* --------------------------------------------------------------------------
   Tools
   -------------------------------------------------------------------------- *) 

fun success_rate l1 l2 =
  let val rate = approx 2 (int_div (length l1) (length l2) * 100.0) in
    log_synt (Real.toString rate ^ " success rate")
  end

fun fea_of x = tttFeature.fea_of_goal ([],x)

(* --------------------------------------------------------------------------
   Metis prover. Should call metis from the future as
   tactictoe is in the build sequence.
   -------------------------------------------------------------------------- *) 

fun time_mprove prover tmax premises tm =
  let
    fun mk_goal x = ([],x)
    val thml = map (mk_thm o mk_goal) premises
    val tac = prover thml
    val (r,t) = add_time (tttExec.app_tac tmax tac) (mk_goal tm)
  in
    if r = SOME [] then SOME (tm,t) else NONE
  end

fun minimize_aux prover t l1 l2 tm = case l2 of
    []     => l1
  | a :: m => 
    if isSome (time_mprove prover t (l1 @ m) tm)
    then minimize_aux prover t l1 m tm
    else minimize_aux prover t (a :: l1) m tm
    
fun miniprove prover t tml tm = 
  if isSome (time_mprove prover t tml tm) 
  then SOME (minimize_aux prover t [] tml tm)
  else NONE

(* --------------------------------------------------------------------------
   Evaluation
   -------------------------------------------------------------------------- *) 

val proofdict = ref (dempty Term.compare)
  
fun expprove proofdict prover axl target =
  let val ro = miniprove prover 0.2 (shuffle axl) target in
    if dmem target (!proofdict) 
    then ()
    else proofdict := dadd target ro (!proofdict)
  end
 
fun expprovel pdict prover axl targetl =
  let 
    val proofdict = ref pdict
    val i = ref 0
    fun f target = 
      (incr i; 
       log_synt (int_to_string (!i)); 
       expprove proofdict prover axl target)
  in
    app f targetl;
    !proofdict
  end

fun calc_reward depl =
  let 
    val depl0 = rev (topo_sort depl)
    val d = dnew Term.compare depl
    val depl1 = map (fn x => (x, dfind x d)) depl0   

    val reward = ref (dempty Term.compare)
    fun f (tm,tml) =
      let fun g dep =
        let val oldn = dfind dep (!reward) handle NotFound => 0 in
          reward := dadd dep (oldn + 1) (!reward)
        end
      in
        app g tml
      end  
  in
    app f depl1; !reward
  end

end (* struct *)

(*
load "tttSyntEval";
open tttTools tttSynt tttSyntEval;

(* Initialization *)
val run_id = "conjecturing";
val _ = ttt_synt_dir := tactictoe_dir ^ "/log_synt/" ^ run_id;
val _ = cleanDir_rec (!ttt_synt_dir);
val _ = mlibUseful.trace_level := 0;
val _ = show_assums := true;

(* Axioms *)
val ax1 = ``~(SUC x = 0)``;
val ax2 = ``~(x = 0) ==> ?y. (SUC y = x)``;
val ax3 = ``(SUC x = SUC y) ==> (x = y)``;
val ax4 = ``x + 0 = x``;
val ax5 = ``x + SUC y = SUC (x + y)``;
val ax6 = ``x * 0 = 0``;
val ax7 = ``x * (SUC y) = (x * y) + x``;
val ax8 = concl numTheory.INDUCTION;
val symbtm = ``(y = 0) \/ (z=0) <=> (z = 0) /\ (x = 0)``;
fun closify x = list_mk_forall (free_vars_lr x, x);
val axl0 = map closify [ax1,ax2,ax3,ax4,ax5,ax6,ax7];

(* Conjecturing *)
fun is_vc x = is_var x orelse is_const x
val vcl = List.concat (map (find_terms is_vc) [ax1,ax3,ax4,ax5,ax6,ax7]);
val vcset = mk_fast_set Term.compare vcl;
fun filterf n tml = first_n n (shuffle tml)
val (cjl,_) = cjenum 0 numTheory.INDUCTION 10 1000 filterf vcset;

(* Proving *)
fun by2 pdict = 
  let 
    fun is2 (_,x) = case x of 
      NONE => false
    | SOME depl => length depl >= 2
  in
    filter is2 (dlist pdict)
  end

val prover   = metisTools.FO_METIS_TAC;
val pdict0 : (term, term list option) Redblackmap.dict  = dnew Term.compare (map (fn x => (x,SOME [])) axl0);
val targetl0 = filter (fn x => not (dmem x pdict0)) cjl;
val pdict1   = expprovel pdict0 prover axl0 targetl0;
val pdict1l = mapfilter (fn (x,y) => (x, valOf y)) (dlist pdict1)
val reward1  = dict_sort compare_imax (dlist (calc_reward pdict1l));

val axl1     = axl0 @ map fst (by2 pdict1);
val (provenl1, targetl1) = 
  partition (fn x => isSome (dfind x pdict1)) targetl0;
val pdict2   = expprovel pdict1 prover axl1 targetl1;
val pdict2l = mapfilter (fn (x,y) => (x, valOf y)) (dlist pdict2);
val reward2  = dict_sort compare_imax (dlist (calc_reward pdict2l));

val (provenl2, targetl2) = 
  partition (fn x => isSome (dfind x pdict1)) targetl1;

val subtml = List.concat (map (fn x => find_terms (fn _ => true) x) provenl1);
val subtmln = 
  dict_sort compare_imax (dlist (count_dict (dempty Term.compare) subtml));

*)

