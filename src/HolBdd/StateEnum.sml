(*****************************************************************************)
(* StateEnum.sml                                                             *)
(* -------------                                                             *)
(*                                                                           *)
(* First implementation of reachability tools for HolBddLib. Now partly      *)
(* obsoleted by BddRules.sml                                                 *)
(*****************************************************************************)

(* structure StateEnum :> StateEnum = struct *)

(*
load "bossLib";
load "pairLib";
load "liteLib";
load "Ho_Rewrite";
load "Num_conv";
load "unwindLib";
load "HolBdd";
load "HolBddTheory";
*)

val _ = 
 print 
  "\nComputeReachable is obsolete.\n\
   \It uses an inefficient coding style.\n\
   \Use BddRules.ComputeReachableBdd instead.\n";

open HolBdd;
open HolBddTheory;

local 

open HolKernel Parse boolLib 
     BasicProvers pairSyntax pairTools numLib HolBdd;

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

val num = ``:num``;

in

(* open bossLib;          *)
(* open arithmeticTheory; *)
(* open pairTheory;       *)
(* open Ho_Rewrite;       *)
(* open Num_conv;         *)
(* open HolBddTheory;     *)

(* Def superceded by bossLib.Define ******************************************
(*****************************************************************************)
(*    Def ``Foo ... = ...``                                                  *)
(*                                                                           *)
(* expands to                                                                *)
(*                                                                           *)
(*    new_definition("Foo_def",``Foo ... = ...``)                            *)
(*****************************************************************************)

fun Def tm = 
 let val (lhs,_) = dest_eq tm
     val (opr,_) = strip_comb lhs
     val name    = fst((dest_var opr)handle _ => (dest_const opr))
 in
  new_definition((name ^ "_def"),tm)
 end;
 *****************************************************************************)


(*****************************************************************************)
(* Convert an ML integer to a HOL numerical constant                         *)
(*****************************************************************************)

fun intToTerm n = numSyntax.mk_numeral(Arbnum.fromInt n);

(*****************************************************************************)
(*    |- t2(v1,...,vn) = t2(v1,...,vn)                                       *)
(*    --------------------------------                                       *)
(*             |- t1 = t2                                                    *)
(*****************************************************************************)

fun PGEN_EXT th =
 let val vars = rand(rand(concl th))
 in
  EXT(pairTools.PGEN (genvar(type_of vars)) vars th)
 end

val DEPTH_EXISTS_CONV = unwindLib.DEPTH_EXISTS_CONV
and EXPAND_AUTO_CONV  = unwindLib.EXPAND_AUTO_CONV;

(*****************************************************************************)
(* Some utility functions for examples                                       *)
(*****************************************************************************)

fun mk_bool_var s = mk_var(s,bool);

fun mk_primed_bool_var s = mk_bool_var(s^"'");


(*****************************************************************************)
(* Tool to compute a BDD for ``Reachable R B state'', where:                 *)
(*                                                                           *)
(*    Reachable R B state = ?n. ReachIn R B n state                          *)
(*                                                                           *)
(* given explicit BDDs for R and B and a state vector of                     *)
(* boolean variables for state.                                              *)
(* Works by finding the smallest n such that:                                *)
(*                                                                           *)
(*    ReachBy R B n = ReachBy R B (SUC n)                                    *)
(*                                                                           *)
(* and then using ReachBy_fixedpoint                                         *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* If ithm is:                                                               *)
(*                                                                           *)
(*     |- ReachBy R B tm1 state = <rhs>                                      *)
(*                                                                           *)
(* then ReachBy_CONV cnv ithm applies cnv to tm to prove:                    *)
(*                                                                           *)
(*     |- ReachBy R B tm2 state = <rhs>                                      *)
(*                                                                           *)
(* where cnv tm1 --> |- tm1 = tm2                                            *)
(*****************************************************************************)

val ReachBy_CONV = CONV_RULE o RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV;

(*****************************************************************************)
(* If ithm is:                                                               *)
(*                                                                           *)
(*     |- ReachBy R B (SUC n) state = <rhs>                                  *)
(*                                                                           *)
(* then ReachBy_SUC_CONV n ithm uses num_CONV to prove:                      *)
(*                                                                           *)
(*     |- ReachBy R B n+1 state = <rhs>                                      *)
(*                                                                           *)
(* where "n+1" denotes the numeral constant one greater than the numeral n   *)
(*****************************************************************************)

fun ReachBy_SUC_CONV n =
 ReachBy_CONV(REWR_CONV(SYM(Num_conv.num_CONV(intToTerm(n+1)))));

(*****************************************************************************)
(* Flag (default true) to determine whether to delete BDDs                   *)
(*****************************************************************************)

val deleteBdd_flag = ref false;

(*****************************************************************************)
(* Suppose Bthm defines an initial set of states B and Rthm defines a        *)
(* transition relation R:                                                    *)
(*                                                                           *)
(*    B state = ...                                                          *)
(*                                                                           *)
(*    R (state, state') = ...                                                *)
(*                                                                           *)
(* then ComputeReachable (Rthm,Bthm) attempts                                *)
(* to construct a BDD of ``Reachable R B state``.                            *)
(*                                                                           *)
(* A "." is printed for each iteration. Currently there is no upper bound    *)
(* on the number of iterations.                                              *)
(*****************************************************************************)

fun ComputeReachable (Rthm,Bthm) =
 let val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')            = dest_pair st_st'
     val _                   = (can (match_term st) st_b andalso
                                can (match_term st_b) st) orelse
                               hol_err "R & B mismatch" "ComputeReachable"
     val ntm                 = ``n:num``
     val [CITER0,CITER_SUC]  = CONJUNCTS ReachBy_rec
     val ci0                 = ISPECL[R,B,st]CITER0
     val cisuc               = GEN ntm 
                                (Ho_Rewrite.REWRITE_RULE
                                  [Next_def,pairTheory.EXISTS_PROD]
                                  (ISPECL[R,B,ntm,st]CITER_SUC))
     val (Rdescr,Rbdd)       = addEquation Rthm
     val (Bdescr,Bbdd)       = addEquation Bthm
     fun iterate n (cidescr,cibdd) = 
      let val _                 = print "."
          val (cidescr',cibdd') = 
               addEquation (ReachBy_SUC_CONV n (SPEC (intToTerm n) cisuc))
          val test              = is_taut(bdd.BIIMP(cibdd,cibdd'))
      in
       if test
        then n
        else if !deleteBdd_flag 
              then (HolBdd.deleteBdd cidescr;iterate (n+1) (cidescr',cibdd'))
              else iterate (n+1) (cidescr',cibdd')
      end
 in
  let val n       = iterate 0 (addEquation ci0)
      val ntm     = intToTerm n
      val ntm'    = intToTerm(n+1)
      val th1     = bddOracle ``ReachBy ^R ^B ^ntm' ^st =
                                  ReachBy ^R ^B ^ntm ^st``
      val th2     = MATCH_MP
                     ReachBy_fixedpoint
                      (MATCH_MP
                        EQ_EXT
                        (pairTools.PGEN 
                          (genvar(type_of st))
                          st
                          (SYM(ReachBy_CONV Num_conv.num_CONV th1))))
      val th3     = AP_THM th2 st
  in
   addEquation th3;
   {ReachThm=th3,iterations=n}
  end
 end;


(* Version using  ReachBy_ReachIn

fun Make_Reachable_ReachIn_Bdd (Rthm,Bthm) =
 let val (R,st_st')             = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)               = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')               = dest_pair st_st'
     val _                      = (can (match_term st) st_b andalso
                                   can (match_term st_b) st) orelse
                                  hol_err "R & B mismatch" "Make_Reachable_ReachIn_Bdd"
     val ntm                    = ``n:num``
     val [ReachIn0,ReachIn_SUC] = CONJUNCTS ReachIn_def
     val i0                     = AP_THM(ISPECL[R,B]ReachIn0)st
     val isuc                   = Ho_Rewrite.REWRITE_RULE (* needs Ho_Rewrite *)
                                   [Next_def,pairTheory.EXISTS_PROD]
                                   (GEN ntm (AP_THM(ISPECL[R,B,ntm]ReachIn_SUC)st))
     val [CITER0,CITER_SUC]     = CONJUNCTS ReachBy_ReachIn
     val ci0                    = ISPECL[R,B,st]CITER0
     val cisuc                  = GEN ntm (ISPECL[R,B,ntm,st]CITER_SUC)
     val (Rdescr,Rbdd)          = addEquation Rthm
     val (Bdescr,Bbdd)          = addEquation Bthm
     val (i0_descr,ibdd0)       = addEquation i0
     fun iterate n idescr (cidescr,cibdd) = 
      let val _                 = print "."
          val (idescr' ,ibdd')  = addEquation (SPEC (intToTerm n) isuc)
          val (cidescr',cibdd') = 
               addEquation (ReachBy_SUC_CONV n (SPEC (intToTerm n) cisuc))
          val test              = is_taut(bdd.BIIMP(cibdd,cibdd'))
      in
       if test
        then n
        else let val (idescr'',_) = addEquation (ReachBy_SUC_CONV n (REFL idescr'))
             in
              if !deleteBdd_flag 
               then(HolBdd.deleteBdd idescr; 
                    HolBdd.deleteBdd cidescr; 
                    HolBdd.deleteBdd idescr';
                    iterate (n+1) idescr'' (cidescr',cibdd'))
               else iterate (n+1) idescr'' (cidescr',cibdd')
              end
      end
 in
  let val n       = iterate 0 i0_descr (addEquation ci0)
      val ntm     = intToTerm n
      val ntm'    = intToTerm(n+1)
      val th1     = bddOracle ``ReachBy ^R ^B ^ntm' ^st =
                                  ReachBy ^R ^B ^ntm ^st``
      val th2     = MATCH_MP
                     ReachBy_fixedpoint
                      (MATCH_MP
                        EQ_EXT
                        (pairTools.PGEN 
                          (genvar(type_of st))
                          st
                          (SYM(ReachBy_CONV Num_conv.num_CONV th1))))
      val th3     = AP_THM th2 st
  in
   addEquation th3;
   {Thm=th3,iterations=n}
  end
 end;
*)



(*****************************************************************************)
(* Suppose Bthm defines an initial set of states B and Rthm defines a        *)
(* transition relation R:                                                    *)
(*                                                                           *)
(*    B state = ...                                                          *)
(*                                                                           *)
(*    R (state, state') = ...                                                *)
(*                                                                           *)
(* then MakeReachableChecker (Rthm,Bthm) creates the BDD of the set of       *)
(* reachable states and returns a function that checks whether a term        *)
(* holds in this set.                                                        *)
(*****************************************************************************)

(*
fun MakeReachableChecker (Rthm,Bthm) =
 let val _                   = print "Making checker: "
     val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')            = dest_pair st_st'
     val {Thm=_,iterations=m}= Make_Reachable_ReachBy_Bdd (Rthm,Bthm)
     val _ = print("\n" ^ (int_to_string m) ^" iterations")
 in
  fn tm => bddOracle ``Reachable ^R ^B ^st ==> ^tm``
 end;
*)

(*****************************************************************************)
(* Use MakeReachableChecker to make a checker for properties                 *)
(* in all stable reachable states                                            *)
(*****************************************************************************)

(*
fun MakeStableChecker (Rthm,Bthm) =
 let val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')            = dest_pair st_st'
     val rcheck              = MakeReachableChecker (Rthm,Bthm)
     val stbthm =
      Ho_Rewrite.REWRITE_RULE 
       [pairTheory.FORALL_PROD,pairTheory.PAIR_EQ] 
       (ISPECL [``DFF``,st] Stable_def)
     val _ = addEquation stbthm
 in
  fn tm => rcheck ``Stable ^R ^st ==> ^tm``
 end;
*)

(*****************************************************************************)
(* Bespoke construction of a checker for properties in all stable            *)
(* reachable states based on Reachable_Stable                                *)
(*****************************************************************************)

fun MakeStableChecker2 (Rthm,Bthm) =
 let val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')            = dest_pair st_st'
     val _                   = (st=st_b) orelse
                               hol_err "R & B mismatch" "MakeStableChecker2"
     val ntm                 = ``n:num``
     val [ReachIn0,ReachIn_SUC]    = CONJUNCTS ReachIn_def
     val i0                  = AP_THM(ISPECL[R,B]ReachIn0)st
     val isuc                = Ho_Rewrite.REWRITE_RULE (* needs Ho_Rewrite *)
                                [Next_def,pairTheory.EXISTS_PROD]
                                (GEN ntm (AP_THM(ISPECL[R,B,ntm]ReachIn_SUC)st))
     val stbthm              = Ho_Rewrite.REWRITE_RULE (* needs Ho_Rewrite *)
                                [Next_def,pairTheory.FORALL_PROD]
                                (ISPECL[R,st]Stable_def)
     val (Rdescr,Rbdd)       = addEquation Rthm
     val (Bdescr,Bbdd)       = addEquation Bthm
     val (stb_descr,stbbdd)  = addEquation stbthm
     val (i0_descr,ibdd0)    = addEquation i0
     fun iterate n ibdd      = 
      let val _                 = print "."
      in
       if is_taut(bdd.IMP(ibdd,stbbdd))
        then n
        else 
         let val (idescr' ,ibdd') = 
          addEquation (ReachBy_SUC_CONV n (SPEC (intToTerm n) isuc))
         in
          iterate (n+1) ibdd'
         end
      end
     val n       = iterate 0 ibdd0
     val ntm     = intToTerm n
     val th1     = bddOracle ``ReachIn ^R ^B ^ntm ^st ==> ^stb_descr``
     val st_var  = mk_var("state",type_of st)
     val th2     = pairTools.PGEN st_var st th1
     val Live_th = Ho_Rewrite.REWRITE_RULE
                     [pairTheory.EXISTS_PROD,pairTheory.FORALL_PROD]
                     (ISPEC R Live_def)
     val (ldescr,lbdd)  = addEquation Live_th
     val th3 = bddOracle ``Live ^R``
     val th4 = SPEC st (MATCH_MP Reachable_Stable (CONJ th3 th2))
     val _   = addEquation th4
 in
  fn tm => 
     bddOracle ``Reachable ^R ^B ^st /\ Stable ^R ^st ==> ^tm``
 end;

(*****************************************************************************)
(* Tool for simplifying the iteration of ReachBy                             *)
(*****************************************************************************)

(*****************************************************************************)
(* SYM an equation of the form ``t=v`` where v in supplied term list;        *)
(* identity on other terms                                                   *)
(*****************************************************************************)

fun COND_SYM_CONV tml tm =
 if is_eq tm andalso mem (rhs tm) tml
  then SYM_CONV tm
  else ALL_CONV tm;

(*****************************************************************************)
(* Apply a conversion to all leaves of a disjunction tree                    *)
(*****************************************************************************)

fun LIST_DISJ_CONV cnv tm =
 if is_disj tm
  then let val (d1,d2) = dest_disj tm
           val d1thm = LIST_DISJ_CONV cnv d1
           val d2thm = LIST_DISJ_CONV cnv d2
       in
        liteLib.MK_DISJ d1thm d2thm
       end
  else cnv tm;

(*****************************************************************************)
(* Apply a conversion to all leaves of a conjunction tree                    *)
(*****************************************************************************)

fun LIST_CONJ_CONV cnv tm =
 if is_conj tm
  then let val (d1,d2) = dest_conj tm
           val d1thm = LIST_CONJ_CONV cnv d1
           val d2thm = LIST_CONJ_CONV cnv d2
       in
        liteLib.MK_CONJ d1thm d2thm
       end
  else cnv tm;

(*****************************************************************************)
(* ``?x1...xn. t1 /\ ... /\ tm`` --> ``?x1...xn. t1' /\ ... /\ tn'``         *)
(*                                                                           *)
(* where if ti has the form ``tm = xj`` then ti' is ``xj = tm``              *)
(*****************************************************************************)

fun UNWIND_SYM_CONV tm = 
 DEPTH_EXISTS_CONV (LIST_CONJ_CONV(COND_SYM_CONV(fst(strip_exists tm)))) tm;

(*****************************************************************************)
(* LIST_MK_CONJ [|- u1=v1, |- u2=v2,...,|- un=vn] =                          *)
(*              |- u1/\u2/\.../\un = v1/\v2/\.../\vn                         *)
(*****************************************************************************)

fun LIST_MK_CONJ [th] = th
 |  LIST_MK_CONJ (th::thl) = liteLib.MK_CONJ th (LIST_MK_CONJ thl);

(*****************************************************************************)
(* LIST_ELIM_LHS_CONV:                                                       *)
(* Gather together equations with the same lhs and then                      *)
(* when there are more than one with same lhs perform                        *)
(* transformations (called NORM_LHS) like:                                   *)
(*                                                                           *)
(*    x=t1 /\ x=t2 /\ x=t3  /\ x=t4  -->  x=t1 /\ t1=t2 /\ t1=t3 /\ t1=t4    *)
(*                                                                           *)
(* This transformation ensures that                                          *)
(* unwindLib.EXPAND_AUTO_CONV doesn't fail                                   *)
(*****************************************************************************)

val IMP_DISCH_EQN = 
 bossLib.DECIDE ``!w u v:bool. (w ==> (u = v)) ==> (w /\ u = w /\ v)``;

fun ELIM_LHS_CONV l =
 if length l <= 1 orelse not(is_eq(hd l))
  then ALL_CONV(list_mk_conj l)
  else
   let val (w::tml) = l
       val th = ASSUME w
       val thl = map (RATOR_CONV(RAND_CONV(REWR_CONV th))) tml 
       val th' = LIST_MK_CONJ thl
       val (u,v) = dest_eq(concl th')
   in
    MP (SPECL[w,u,v]IMP_DISCH_EQN) (DISCH w th')
   end;

fun eq_lhs tm1 tm2 =
 is_eq tm1 andalso is_eq tm2 andalso (fst(dest_eq tm1) = fst(dest_eq tm2));

(*****************************************************************************)
(* Code from Konrad Slind                                                    *)
(*****************************************************************************)

fun split p alist =
   itlist (fn x => fn (L,R) => if (p x) then (x::L, R) else (L, x::R))
          alist ([],[]);


(*---------------------------------------------------------------------------
 * Partitions a list on the basis of a two-place predicate, which is moved
 * through the list.
 *
 *     fun curry f x y = f (x,y)
 *      partition (curry (op =)) [1,2,3,1,1,2,2,3,4,5,4,4,3,2,1];
 *     val it = [[1,1,1,1],[2,2,2,2],[3,3,3],[4,4,4],[5]] : int list list
 *---------------------------------------------------------------------------*)

fun partition p =
   let fun break [] = []
         | break (a::b) =
             let val (class,rst) = split (p a) b
             in (a::class)::(break rst)
             end
   in break
   end;


fun LIST_ELIM_LHS_CONV tm =
 let val conjl = strip_conj tm 
     val conjll = partition eq_lhs conjl
     val th1 = LIST_MK_CONJ(map ELIM_LHS_CONV conjll)
     val th2 = CONJUNCTS_CONV(tm, lhs(concl th1))
 in
  TRANS th2 th1
 end;

val AND_OR = bossLib.DECIDE ``A /\ (B \/ C) = (A /\ B) \/ (A /\ C)``;

val OR_AND = bossLib.DECIDE ``(A \/ B) /\ C = (A /\ C) \/ (B /\ C)``;

(*****************************************************************************)
(* Generate a simplified instantion of ReachBy_rec:                          *)
(*                                                                           *)
(*     |- (!R B state. ReachBy R B 0 state = B state) /\                     *)
(*        (!R B n state.                                                     *)
(*          ReachBy R B (SUC n) state =                                      *)
(*          ReachBy R B n state \/                                           *)
(*          (?state_. ReachBy R B n state_ /\ R(state_,state)))              *)
(*                                                                           *)
(* The simplification assumes R is of the form:                              *)
(*                                                                           *)
(*  R((x,y,z),(x',y',z'))=                                                   *)
(*   ((x' = E1(x,y,z)) /\ (y' = y)         /\ (z' = z))                      *)
(*    \/                                                                     *)
(*   ((x' = x)         /\ (y' = E2(x,y,z)) /\ (z' = z))                      *)
(*    \/                                                                     *)
(*   ((x' = x)         /\ (y' = y)         /\ (z' = E3(x,y,z)))              *)
(*                                                                           *)
(* The SUC case is simplified from:                                          *)
(*                                                                           *)
(*   ReachBy R B (SUC n) (x,y,z) =                                           *)
(*     ReachBy R B n (x,y,z)                                                 *)
(*     \/                                                                    *)
(*     (?x_ y_ z_. ReachBy n R B (x_,y_,z_) /\ R((x_,y_,z_),(x,y,z))))       *)
(*                                                                           *)
(* to                                                                        *)
(*                                                                           *)
(*   ReachBy R B (SUC n) (x,y,z) =                                           *)
(*     ReachBy R B n (x,y,z)                                                 *)
(*     \/                                                                    *)
(*     (?x_. ReachBy R B n (x_,y,z) /\ (x = E1(x_,y,z))                      *)
(*     \/                                                                    *)
(*     (?y_. ReachBy R B n (x,y_,z) /\ (y = E2(x,y_,z))                      *)
(*     \/                                                                    *)
(*     (?z_. ReachBy R B n (x,y,z_) /\ (z = E3(x,y,z_))                      *)
(*                                                                           *)
(* This avoids having to build the BDD of R((x,y,z),(x',y',z'))              *)
(*****************************************************************************)

fun MakeSimpReachByRecThm(Rthm,Bthm) =
 let val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')            = dest_pair st_st'
     val ntm                 = ``n:num``
     val [CITER0,CITER_SUC]  = CONJUNCTS ReachBy_rec
     val ci0                 = ISPECL[R,B,st]CITER0
     val cisuc               = Ho_Rewrite.REWRITE_RULE
                                [Next_def,pairTheory.EXISTS_PROD]
                                (ISPECL[R,B,ntm,st]CITER_SUC)
(*   val cisuc_simp          = time (simpLib.SIMP_RULE 
                                HOLSimps.hol_ss
                                [Rthm,AND_OR,EXISTS_OR_THM])
                                cisuc
*)
     val cisuc_simp          = RIGHT_CONV_RULE
                                (RAND_CONV
                                 (DEPTH_EXISTS_CONV (REWRITE_CONV[AND_OR])
                                   THENC TOP_DEPTH_CONV EX_OR_CONV
                                   THENC LIST_DISJ_CONV UNWIND_SYM_CONV
                                   THENC LIST_DISJ_CONV 
                                          (DEPTH_EXISTS_CONV LIST_ELIM_LHS_CONV)
                                   THENC LIST_DISJ_CONV (EXPAND_AUTO_CONV[])))
                                (Ho_Rewrite.REWRITE_RULE[Rthm] cisuc)
 in
  CONJ ci0 (GEN ntm cisuc_simp)
 end;

(* Version using ReachIn_rec instead of ReachBy_rec *)

fun MakeSimpReachInRecThm(Rthm,Bthm) =
 let val (R,st_st')             = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)               = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')               = dest_pair st_st'
     val ntm                    = ``n:num``
     val [ReachIn0,ReachIn_SUC] = CONJUNCTS ReachIn_rec
     val i0                     = ISPECL[R,B,st] ReachIn0
     val isuc                   = Ho_Rewrite.REWRITE_RULE
                                   [Next_def,pairTheory.EXISTS_PROD]
                                   (ISPECL[R,B,ntm,st]ReachIn_SUC)
     val isuc_simp             = time (simpLib.SIMP_RULE 
                                   boolSimps.bool_ss (* HOLSimps.hol_ss *)
                                   [Rthm,AND_OR,EXISTS_OR_THM])
                                   isuc
(* Code below won't work as it is tuned to ReachBy (EX_OR_CONV?)
     val isuc_simp           = RIGHT_CONV_RULE
                                (RAND_CONV
                                 (DEPTH_EXISTS_CONV (REWRITE_CONV[AND_OR])
                                   THENC TOP_DEPTH_CONV EX_OR_CONV
                                   THENC LIST_DISJ_CONV UNWIND_SYM_CONV
                                   THENC LIST_DISJ_CONV 
                                          (DEPTH_EXISTS_CONV LIST_ELIM_LHS_CONV)
                                   THENC LIST_DISJ_CONV (EXPAND_AUTO_CONV[])))
                                (Ho_Rewrite.REWRITE_RULE[Rthm] isuc)
*)
 in
  CONJ i0 (GEN ntm isuc_simp)
 end;

fun ComputeSimpReachable (Rthm,Bthm) =
 let val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')            = dest_pair st_st'
     val _                   = print "Simplifying transition relation..."
     val ci0_cisuc_simp      = time MakeSimpReachByRecThm(Rthm,Bthm)
     val _                   = print "done:\n"
     val _                   = Parse.print_term(concl ci0_cisuc_simp)
     val (ci0, cisuc_simp)   = CONJ_PAIR ci0_cisuc_simp
     val _                   = print "\nComputing fixedpoint: "
     val (Bdescr,Bbdd)       = addEquation Bthm
     fun iterate n (cidescr,cibdd) = 
      let val _                 = print "."
          val (cidescr',cibdd') = 
               addEquation (ReachBy_SUC_CONV n (SPEC (intToTerm n) cisuc_simp))
          val test              = is_taut(bdd.BIIMP(cibdd,cibdd'))
      in
       if test
        then n
        else if !deleteBdd_flag 
              then (HolBdd.deleteBdd cidescr;iterate (n+1) (cidescr',cibdd'))
              else iterate (n+1) (cidescr',cibdd')
      end
     val n       = time (iterate 0) (addEquation ci0)
     val ntm     = intToTerm n
     val ntm'    = intToTerm(n+1)
     val th1     = bddOracle ``ReachBy ^R ^B ^ntm' ^st =
                                 ReachBy ^R ^B ^ntm ^st``
     val th2     = MATCH_MP
                    ReachBy_fixedpoint
                     (MATCH_MP
                       EQ_EXT
                       (pairTools.PGEN 
                         (genvar(type_of st))
                         st
                         (SYM(ReachBy_CONV Num_conv.num_CONV th1))))
     val th3     = AP_THM th2 st
 in
  addEquation th3;
  {SimpTransThm=CONJ ci0 cisuc_simp, ReachThm=th3,iterations=n}
 end;

(*****************************************************************************)
(* FindRefutationTrace(Rthm,Bthm,Qthm) generates a sequence of               *)
(* states: s_n,s_n-1,...,s_0, together with a list of theorems:              *)
(*                                                                           *)
(*    |- B s_n                                                               *)
(*    |- Next R s_n s_n-1                                                    *)
(*    .                                                                      *)
(*    .                                                                      *)
(*    .                                                                      *)
(*    |- Next R s_1 s_0                                                      *)
(*    |- ~Q s_0                                                              *)
(*                                                                           *)
(* These theorems are generated in the reverse order to that shown above.    *)
(*                                                                           *)
(* The function works by iterating R from B (and recording a trace of        *)
(* sets of states) until a state is found for which Q fails. A               *)
(* counterexample s_0 to Q is then generated and Prev is iterated through    *)
(* the trace starting with Eq s_0 to get the sequence s_0, s_1,...,s_n.      *)
(*****************************************************************************)

(* Old version using ReachBy

fun Find_Refutation_ReachBy_Trace(Rthm,Bthm,Qthm) =
 let val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (Q,st_q)            = dest_comb(lhs(concl(SPEC_ALL Qthm)))
     val (st,st')            = dest_pair st_st'
     val _                   = print "Simplifying transition relation..."
     val (ci0, cisuc_simp)   = CONJ_PAIR(time MakeSimpReachByRecThm(Rthm,Bthm))
     val _                   = print "done.\n"
     val _                   = print "Computing counterexample trace: "
     val (Bdescr,Bbdd)       = addEquation Bthm
     val (Qdescr,Qbdd)       = addEquation Qthm
     fun find_refutation_trace n (cidescr,cibdd) trace = 
      let val _                 = print "."
          val test              = is_taut(bdd.IMP(cibdd,Qbdd))
      in
       if test
        then let val (cidescr',cibdd') =
                  addEquation (ReachBy_SUC_CONV n (SPEC (intToTerm n) cisuc_simp))
                 val _ = print "."
             in
              find_refutation_trace (n+1) (cidescr',cibdd') ((cidescr,cibdd)::trace)
             end
        else (cidescr,cibdd)::trace
      end
     val ((refute_descr,refute_bdd)::trace) = 
      time (find_refutation_trace 0 (addEquation ci0)) []
     val _          = print "done.\n"
     val _          = print "Simplifying Prev instance..."
     val prev_thm1  = Ho_Rewrite.REWRITE_RULE 
                       [pairTheory.EXISTS_PROD,Rthm] 
                       (ISPECL[R,``Q:^(type_of st)->bool``,st]Prev_def)

     val prev_thm2  = RIGHT_CONV_RULE
                       (DEPTH_EXISTS_CONV (REWRITE_CONV[OR_AND])
                         THENC TOP_DEPTH_CONV EX_OR_CONV
                         THENC LIST_DISJ_CONV UNWIND_SYM_CONV
                         THENC LIST_DISJ_CONV(DEPTH_EXISTS_CONV LIST_ELIM_LHS_CONV)
                         THENC LIST_DISJ_CONV (EXPAND_AUTO_CONV[]))
                       prev_thm1
     val prev_thm3 = GEN (mk_var("Q",type_of Q)) prev_thm2
     fun prev s = Ho_Rewrite.REWRITE_RULE
                   [Eq_def,pairTheory.PAIR_EQ](SPEC ``Eq ^s`` prev_thm3)
     val _          = print "done"
     fun get_st tm = 
      let val s = rhs(concl(REWRITE_CONV[ASSUME tm]st))
      in
       subst (map (fn v => (F|->v)) (free_vars s)) s
      end
     val s_0        = get_st(findModel ``^refute_descr /\ ~(^Qdescr)``)
     val s_0_thm    = bddOracle(mk_neg(mk_comb(Q,s_0)))
     fun get_sts [] s acc                   = acc
      |  get_sts ((descr,bdd)::trace) s acc =
          let val prev_th = prev s
              val (descr',bdd') = addEquation prev_th
              val s' = get_st(findModel(mk_conj(descr',descr)))
              val nxt_thm = 
               Ho_Rewrite.REWRITE_RULE
                [Prev_Next_Eq](bddOracle(mk_comb(rator descr',s')))
          in
           get_sts trace s' ((s',nxt_thm)::acc)
          end
     val sl = get_sts trace s_0 []
     val s_n_thm = bddOracle(mk_comb(B,fst(hd sl)))
 in
  [s_n_thm]@(map snd sl)@[s_0_thm]
 end;

*)

(* Version using MakeSimpReachInRecThm instead of MakeSimpReachByRecThm *)

fun FindRefutationTrace(Rthm,Bthm,Qthm) =
 let val (R,st_st')          = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)            = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (Q,st_q)            = dest_comb(lhs(concl(SPEC_ALL Qthm)))
     val (st,st')            = dest_pair st_st'
     val _                   = print "Simplifying transition relation..."
     val (i0, isuc_simp)     = CONJ_PAIR(time MakeSimpReachInRecThm(Rthm,Bthm))
     val _                   = print "done.\n"
     val _                   = print "Computing counterexample trace: "
     val (Bdescr,Bbdd)       = addEquation Bthm
     val (Qdescr,Qbdd)       = addEquation Qthm
     fun find_refutation_trace n (cidescr,cibdd) trace = 
      let val _                 = print "."
          val test              = is_taut(bdd.IMP(cibdd,Qbdd))
      in
       if test
        then let val (cidescr',cibdd') =
                  addEquation (ReachBy_SUC_CONV n (SPEC (intToTerm n) isuc_simp))
                 val _ = print "."
             in
              find_refutation_trace (n+1) (cidescr',cibdd') ((cidescr,cibdd)::trace)
             end
        else (cidescr,cibdd)::trace
      end
     val ((refute_descr,refute_bdd)::trace) = 
      time (find_refutation_trace 0 (addEquation i0)) []
     val _          = print "done.\n"
     val _          = print "Simplifying Prev instance..."
     val prev_thm1  = Ho_Rewrite.REWRITE_RULE 
                       [pairTheory.EXISTS_PROD,Rthm] 
                       (ISPECL[R,mk_var("Q",``:^(type_of st)->bool``),st]Prev_def)
     val prev_thm2  = RIGHT_CONV_RULE
                       (DEPTH_EXISTS_CONV (REWRITE_CONV[OR_AND])
                         THENC TOP_DEPTH_CONV EX_OR_CONV
                         THENC LIST_DISJ_CONV UNWIND_SYM_CONV
                         THENC LIST_DISJ_CONV(DEPTH_EXISTS_CONV LIST_ELIM_LHS_CONV)
                         THENC LIST_DISJ_CONV (EXPAND_AUTO_CONV[]))
                       prev_thm1
     val prev_thm3 = GEN (mk_var("Q",type_of Q)) prev_thm2
     fun prev s = Ho_Rewrite.REWRITE_RULE
                   [Eq_def,pairTheory.PAIR_EQ](SPEC ``Eq ^s`` prev_thm3)
     val _          = print "done"
     fun get_st tm = 
      let val s = rhs(concl(REWRITE_CONV[ASSUME tm]st))
      in
       subst (map (fn v => {redex=v,residue=F}) (free_vars s)) s
      end
     val s_0        = get_st(findModel ``^refute_descr /\ ~(^Qdescr)``)
     val s_0_thm    = bddOracle(mk_neg(mk_comb(Q,s_0)))
     fun get_sts [] s acc                   = acc
      |  get_sts ((descr,bdd)::trace) s acc =
          let val prev_th = prev s
              val (descr',bdd') = addEquation prev_th
              val s' = get_st(findModel(mk_conj(descr',descr)))
              val nxt_thm = 
               Ho_Rewrite.REWRITE_RULE
                [Prev_Next_Eq](bddOracle(mk_comb(rator descr',s')))
          in
           get_sts trace s' ((s',nxt_thm)::acc)
          end
     val sl = time (get_sts trace s_0) []
     val s_n_thm = bddOracle(mk_comb(B,fst(hd sl)))
 in
  [s_n_thm]@(map snd sl)@[s_0_thm]
 end;

(*****************************************************************************)
(* Tools for automatically representing enumerated datatypes as bit vectors  *)
(*****************************************************************************)


(*****************************************************************************)
(* Compute the number of bits needed to represent n items                    *)
(*****************************************************************************)

fun bits_needed n =
 let fun log n = if n<2 then 1 else 1 + log(Int.quot(n,2))
 in
  if n<=2 then 1 else log n
 end;

(*****************************************************************************)
(* Compute the m-bit representation of n as a term ``(bm-1,...,b0)``         *)
(*****************************************************************************)

fun num_to_bool n = if n=0 then F else T;

fun word_rep_aux n =
 if n<2 
  then [num_to_bool n]
  else num_to_bool(Int.rem(n,2))::word_rep_aux(Int.quot(n,2));

fun extendF l n =
 if n=0 then l else extendF (F::l) (n-1);

exception word_rep_error;

fun word_rep m n =
 let val l = rev(word_rep_aux n)
     val ex = m - length l
 in
  if ex<0 then raise word_rep_error else list_mk_pair(extendF l ex)
 end;

fun mk_bool_tuple_type n =
 if n<2 
  then bool 
  else Psyntax.mk_type("prod",[bool, mk_bool_tuple_type(n-1)]);

fun mk_disj1(t1,t2) =  (* Also defined in KLBDD.ml *)
 if t1 = F 
  then t2
  else 
  if t2 = F 
   then t1
   else 
   if t1 = T orelse t2 = T then T else Psyntax.mk_disj(t1,t2);

(*****************************************************************************)
(*     |- !P rep.                                                            *)
(*          TYPE_DEFINITION P rep ==>                                        *)
(*          (?abs. (!a. abs (rep a) = a) /\ (!r. P r = rep (abs r) = r))     *)
(*****************************************************************************)

val ABS_EXISTS_THM = HolBddTheory.ABS_EXISTS_THM;

(*****************************************************************************)
(* Generate the definition of abstraction and representation functions       *)
(* for encoding enumeration types as bit strings. Takes as argument the      *)
(* initiality theorem for the datatype.                                      *)
(*                                                                           *)
(* The names of the functions are the name of the type prefixed with         *)
(* "abs_" and "rep_".  For example, if:                                      *)
(*                                                                           *)
(*  Hol_datatype `altitude_vals                                              *)
(*                       = away                                              *)
(*                       | near_pre_selected                                 *)
(*                       | at_pre_selected`;                                 *)
(*                                                                           *)
(* then                                                                      *)
(*                                                                           *)
(*    define_rep "altitude_vals"                                             *)
(*                                                                           *)
(* returns the record:                                                       *)
(*                                                                           *)
(*     {abs_spec =                                                           *)
(*        |- (!a. abs_altitude_vals (rep_altitude_vals a) = a) /\            *)
(*           (!r.                                                            *)
(*             rep_altitude_vals_range r =                                   *)
(*             rep_altitude_vals (abs_altitude_vals r) =                     *)
(*             r),                                                           *)
(*      rep_range_def =                                                      *)
(*        |- !x.                                                             *)
(*             rep_altitude_vals_range x =                                   *)
(*             (x = (F,F)) \/ (x = (F,T)) \/ (x = (T,F)),                    *)
(*      rep_spec =                                                           *)
(*        |- (rep_altitude_vals away = (F,F)) /\                             *)
(*           (rep_altitude_vals near_pre_selected = (F,T)) /\                *)
(*           (rep_altitude_vals at_pre_selected = (T,F)),                    *)
(*      rep_type_def =                                                       *)
(*        |- TYPE_DEFINITION rep_altitude_vals_range rep_altitude_vals}      *)
(*     : {abs_spec : Thm.thm, rep_range_def : Thm.thm, rep_spec : Thm.thm,   *)
(*        rep_type_def : Thm.thm}                                            *)
(*****************************************************************************)
                
fun define_rep th =
 let val (vs,bdy) = strip_forall(concl th)
     val (qnt,lam) = dest_comb bdy
     val (lamv,cnj) = dest_abs lam
     val m = length vs
     val (_,[ty,tyvar]) = dest_type(type_of lamv)
     val (tyname,[]) = dest_type ty
     val rep_fun_name = "rep_" ^ tyname
     val range = List.tabulate(m,word_rep(bits_needed m))
     val th1 = ISPECL range th
     val th2 = CONJUNCT1(Ho_Rewrite.PURE_REWRITE_RULE [EXISTS_UNIQUE_THM] th1)
     val rep_spec = new_specification
                     {name    = rep_fun_name^"_def", 
                      sat_thm = th2,
                      consts  = [{const_name = rep_fun_name, fixity = Prefix}]}
     val induct_thm = Prim_rec.prove_induction_thm th
     val rep_fun_ty = snd(dest_var(fst(dest_exists(concl th2))))
     val rep_fun = mk_const(rep_fun_name,rep_fun_ty)
     val one_one_goal = ``!x' x''. (^rep_fun x' = ^rep_fun x'') ==> (x' = x'')``
     val one_one_thm = prove(one_one_goal, 
                             REPEAT(INDUCT_THEN induct_thm ASSUME_TAC)
                              THEN REWRITE_TAC[rep_spec,pairTheory.PAIR_EQ])
     val (_,[_,x_ty]) = dest_type rep_fun_ty
     val x_tm = mk_var("x",x_ty)
     val range_fun_var = mk_var(("range_" ^ tyname),``:^x_ty->bool``)
     val range_def = new_definition
                      (("range_" ^ tyname ^ "_def"),
                       mk_eq (mk_comb(range_fun_var,x_tm),
                         foldr 
                          (fn(tup,tm) => mk_disj1(mk_eq(x_tm,tup),tm)) 
                          F 
                          range))
     val range_fun_con = mk_const(("range_" ^ tyname),``:^x_ty->bool``)
     val range_goal = ``!x. ^range_fun_con x = (?x'. x = ^rep_fun x')``
     val range_thm = prove
                      (range_goal,
                       REWRITE_TAC[range_def]
                        THEN GEN_TAC
                        THEN EQ_TAC
                        THENL[PROVE_TAC[rep_spec],
                              Ho_Rewrite.REWRITE_TAC[HolBddTheory.EXISTS_IMP_EQ]
                               THEN INDUCT_THEN induct_thm ASSUME_TAC
                               THEN PROVE_TAC[rep_spec]])
     val ty_def_thm = EQ_MP
                       (SYM(ISPECL[range_fun_con,rep_fun]TYPE_DEFINITION))
                       (CONJ one_one_thm range_thm)
     val abs_exists = MATCH_MP ABS_EXISTS_THM  ty_def_thm
     val abs_fun_name = "abs_" ^ tyname
     val abs_spec = new_specification
                     {name    = abs_fun_name ^ "_def",
                      sat_thm = abs_exists,
                      consts  = [{const_name = abs_fun_name, fixity = Prefix}]}
 in
  {abs_spec  = abs_spec,
   rep_spec  = rep_spec,
   range_def = range_def}
 end;

fun PROVE_ABS_THMS abs_def rep_def =
 let val thl = CONJUNCTS rep_def
     val abs_eqn = CONJUNCT1 abs_def
     val (abs_fun, tm) = dest_comb(lhs(concl(SPEC_ALL abs_eqn)))
     val (rep_fun,_) = dest_comb tm
     val thl1 = map (AP_TERM abs_fun) thl
 in    
  LIST_CONJ(map (CONV_RULE(RATOR_CONV(RAND_CONV(REWRITE_CONV[abs_eqn])))) thl1)
 end;

(*****************************************************************************)
(* Tools to extract transition system from predicates on traces.             *)
(*****************************************************************************)

(*****************************************************************************)
(* ExtractTransitionSystem_CONV                                              *)
(*  ``u1,...,um,v1,...,vn``                                                  *)
(*  ``?vt1...vtn.                                                            *)
(*     INIT(ut1 0,...,utm 0,vt1 0,...,vtn 0)                                 *)
(*     /\                                                                    *)
(*     !t. STEP((ut1 t,...,utm t,vt1 t,...,vtn t),                           *)
(*              (ut1(t+1),...,utm(t+1),vt1(t+1),...,vtn(t+1)))``             *)
(* =                                                                         *)
(* ((\((u1,...,um,v1,...,vn),(u1',...,um',v1',...,vn')).                     *)
(*     STEP((u1,...,um,v1,...,vn),(u1',...,um',v1',...,vn'))),               *)
(*  (\(u1,...,um,v1,...,vn). INIT(u1,...,um,v1,...,vn))),                    *)
(*  |- (?vt1...vtn.                                                          *)
(*       INIT(ut1 0,...,utm 0,vt1 0,...,vtn 0)                               *)
(*       /\                                                                  *)
(*       !t. STEP((ut1 t,...,utm t,vt1 t,...,vtn t),                         *)
(*                (ut1(t+1),...,utm(t+1),vt1(t+1),...,vtn(t+1))))            *)
(*      =                                                                    *)
(*      ?vt1...vtn.                                                          *)
(*       (\(u1,...,um,v1,...,vn). INIT(u1,...,um,v1,...,vn))                 *)
(*        (ut1 0,...,utm 0,vt1 0,...,vtn 0)                                  *)
(*      /\                                                                   *)
(*      !t. (\((u1,...,um,v1,...,vn),(u1',...,um',v1',...,vn')).             *)
(*            STEP((u1,...,um,v1,...,vn),(u1',...,um',v1',...,vn')))         *)
(*          ((ut1 t,...,utm t,vt1 t,...,vtn t),                              *)
(*           (ut1(t+1),...,utm(t+1),vt1(t+1),...,vtn(t+1)))                  *)
(*                                                                           *)
(* [All values assumed boolean -- i.e. fully scalarized]                     *)
(*****************************************************************************)

(*****************************************************************************)
(* Remove repeated elements from a list                                      *)
(*****************************************************************************)

fun setify []     = []
 |  setify [x]    = [x]
 |  setify (x::l) = let val ls = setify l 
                    in 
                     if mem x ls then ls else x::ls 
                    end;

(*****************************************************************************)
(* Flatten a varstruct term into a list of variables.                        *)
(*****************************************************************************)

fun flatten_pair t =
if is_pair t
 then foldr (fn(t,l) => (flatten_pair t) @ l) [] (strip_pair t)
 else [t];

(*****************************************************************************)
(* Map over a tuple.                                                         *)
(*****************************************************************************)

fun map_tuple f tup =
 if is_pair tup
  then let val (t1,t2) = dest_pair tup
       in
        mk_pair(map_tuple f t1, map_tuple f t2)
       end
  else f tup;

(*
val statevec = 
 ``((clk:bool,(req_1:bool,req_2:bool),check:bool),
    (ack1_0:bool,ack2_0:bool,counter:bool,counter':bool))``;

val tm = rhs(concl(SPEC_ALL ArbiterTest_eqn));

val((R,B),RBth) = ExtractTransitionSystem_CONV statevec tm;
*)

fun ExtractTransitionSystem_CONV statevec tm =
 let val statevars = flatten_pair statevec
     val statevarnames = map (fst o dest_var) statevars
     val prime_sym = (* if a state variables ends with "'", use "+" instead *)
          if mem #"'" (map (last o explode) statevarnames) 
           then "+" 
           else "'"
     val (exvars,exbody) = strip_exists tm 
     val exvarnames = map (fst o dest_var) exvars
     val _ = if not(null(set_diff exvarnames statevarnames))
              then (print "local variable not in state vector:";
                    app (fn s => print(" "^s)) (set_diff exvarnames statevarnames);
                    print "\n")
              else ()
     val (initl,stepquant) = front_last(strip_conj exbody)
     val init = if null initl then T else list_mk_conj initl
     val (timevar,step) = dest_forall stepquant
     val num2bool_ty = ``:num->bool``
     fun mk_app0 s = mk_comb(mk_var(s,num2bool_ty),``0``)
     val B = pairSyntax.mk_pabs
              (statevec,
                subst
                  (map (fn v => (mk_var(v,bool) |-> mk_app0 v)) statevarnames)
                  init)
(*   val Bth = pairLib.PBETA_CONV(mk_comb(B,map_tuple (mk_app0 o fst o dest_var) statevec)) *)
     val Bth = pairLib.PAIRED_BETA_CONV(mk_comb(B,map_tuple (mk_app0 o fst o dest_var) statevec))
     fun mk_app s = mk_comb(mk_var(s,num2bool_ty),timevar)
     val timevar' = ``^timevar+1``
     fun mk_app' s = mk_comb(mk_var(s,num2bool_ty),timevar')
     fun mk_primevar s = mk_var((s^prime_sym),bool)
     val statevec' = map_tuple (mk_primevar o fst o dest_var) statevec
     val R = pairSyntax.mk_pabs
              (mk_pair(statevec,statevec'),
                subst
                 ((map (fn v => (mk_var(v,bool) |-> mk_app v)) statevarnames)
                  @
                  (map (fn v => (mk_primevar v |-> mk_app' v)) statevarnames))
                 step)
     val Rth = pairLib.PAIRED_BETA_CONV
                (mk_comb
                  (R,
                   mk_pair
                    (map_tuple (mk_app  o fst o dest_var) statevec,
                     map_tuple (mk_app' o fst o dest_var) statevec)))
     val Rth1 = FORALL_EQ timevar Rth
     val BRth1 = if init = T
                  then FORALL_EQ timevar Rth
                  else liteLib.MK_CONJ Bth (FORALL_EQ timevar Rth)
     val BRth2 = TRANS BRth1 (CONJUNCTS_CONV(rhs(concl BRth1), exbody))
 in
  ((R,B),LIST_MK_EXISTS exvars (SYM BRth2))
 end;

(*****************************************************************************)
(* FnPairTuple ``(f1,...,fn)`` =                                             *)
(*  ``(FnPair f1 (FnPair f2 ... (FnPair fn-1 fn) ...))``                     *)
(*****************************************************************************)

fun FnPairTuple v =
      if is_var v
 then let val (name,ty) = dest_var v in mk_var(name,``:num->^ty``) end 
 else if is_pair v
 then let val (v1,v2) = dest_pair v
      in
       ``FnPair ^(FnPairTuple v1) ^(FnPairTuple v2)``
      end 
 else v;

(*****************************************************************************)
(* LiftTuple raises all types in a varstruct (tuple of variables)            *)
(* to functions of ``:num``.                                                 *)
(*****************************************************************************)

val LiftTuple =
 map_tuple 
  (fn u => let val (nm,ty) = dest_var u in mk_var(nm,``:num->^ty``) end);

(*****************************************************************************)
(* If B is a binder (e.g. ``!`` or ``?``)                                    *)
(*                                                                           *)
(* LIST_GEN_ALPHA_CONV [``u1``,...,``un``] ``B v1...vn. t``                  *)
(* -->                                                                       *)
(* |- (B v1...vn. t) = (B u1...un. t)                                        *)
(*****************************************************************************)

fun LIST_GEN_ALPHA_CONV [] tm = REFL tm
 |  LIST_GEN_ALPHA_CONV (v::vl) tm = 
      (BINDER_CONV (LIST_GEN_ALPHA_CONV vl) 
        THENC GEN_ALPHA_CONV v) tm;

(*****************************************************************************)
(* Specialise FnPairForall to use variables from a supplied varstruct.       *)
(*                                                                           *)
(* SpecFnPairForall ``(f1,...,fn-1,fn)``                                     *)
(*                                                                           *)
(*  |- !P. (!tr. P tr) =                                                     *)
(*         !f1...fn. P(FnPair f1 (FnPair f2 ... (FnPair fn-1 fn) ...))       *)
(*****************************************************************************)

(*****************************************************************************)
(* MakeTupleType ``((v1:num->ty1),(v2:num->ty2))`` --> ``:ty1 # ty2``        *)
(*****************************************************************************)

fun MakeTupleType tup =
 type_of
  (map_tuple 
    (fn u => let val (v,vty) = dest_var u
                 val (c,[ty1,ty2]) = dest_type vty
                 val _ = not(c="fun" andalso ty1=num) andalso
                         hol_err ("bad var in tuple: "^v) "MakeTupleType"
              in 
               mk_var(v,last(snd(dest_type vty))) 
              end)
    tup);

fun SpecFnPairForall vf =
 let val ty = MakeTupleType vf
     val tr = mk_var("tr",``:num->^ty``)
     val Ptm = mk_forall(tr,mk_comb(mk_var("P",``:(num->^ty)->bool``),tr))
     val th = Ho_Rewrite.REWRITE_CONV[HolBddTheory.FnPairForall]Ptm
 in
  RIGHT_CONV_RULE (LIST_GEN_ALPHA_CONV(flatten_pair vf)) th
 end;

(*****************************************************************************)
(* Specialise FnPairExists to use variables from a supplied varstruct.       *)
(*                                                                           *)
(* SpecFnPairExists ``(f1,...,fn-1,fn)``                                     *)
(*                                                                           *)
(*  |- !P. (?tr. P tr) =                                                     *)
(*         ?f1...,fn. P(FnPair f1 (FnPair f2 ... (FnPair fn-1 fn) ...))      *)
(*****************************************************************************)

fun SpecFnPairExists vf =
 let val ty = MakeTupleType vf
     val tr = mk_var("tr",``:num->^ty``)
     val Ptm = mk_exists(tr,mk_comb(mk_var("P",``:(num->^ty)->bool``),tr))
     val th = Ho_Rewrite.REWRITE_CONV[HolBddTheory.FnPairExists]Ptm
 in
  RIGHT_CONV_RULE(LIST_GEN_ALPHA_CONV(flatten_pair vf) )th
 end;

(*****************************************************************************)
(* Conversion to scalarize quantifications                                   *)
(*                                                                           *)
(*   ``Q f. P f``                                                            *)
(*    -->                                                                    *)
(*    |- (Q f. P f) =                                                        *)
(*       Q f_1 ... f_n.                                                      *)
(*        P(FnPair f_1 (FnPair f_2 ... (FnPair f_n-1 f_n) ...))              *)
(*****************************************************************************)

(* Test data
val tm = ``?f g. !t:num. (f t = (T,F,T,T,F)) /\ (g t = (F,F,T))``;
val tm = ``!g. !t:num. g t = (T,F,T,T,F)``;
val tm = ``(!g. !t:num. g t = (T,F,T,T,F)) /\ (?f. !t:num. f t = (T,F))``;
*)

(* flatten a product type to a list of its leaf types *)

fun flatten_pair_type ty =
 let val (con,tyl) = dest_type ty
 in
  if con="prod"
   then flatten_pair_type(hd tyl)@flatten_pair_type(hd(tl tyl))
   else [ty]
 end;

(*****************************************************************************)
(* scalarizeTuple ``(f :num -> bool # bool # bool # bool # bool)``           *)
(* = ``((f_0 :num -> bool),(f_1 :num -> bool),(f_2 :num -> bool),            *)
(*      (f_3 :num -> bool),(f_4 :num -> bool))``                             *)
(*****************************************************************************)

fun scalarizeTuple v =
 let val ("fun",[ty1,ty2]) = dest_type(type_of v)
     val tyl = flatten_pair_type ty2
     val vname = fst(dest_var v)
 in
  list_mk_pair
   (map2
    (fn n => fn ty => mk_var((vname^"_"^(int_to_string n)),
                             mk_type("fun",[ty1,ty])))
    (List.rev(List.tabulate(length tyl,I)))  (* rev so LSB is rightmost *)
    tyl)
 end;

exception Error;

fun scalarize_CONV tm =
 (let val (v,_) = if is_forall tm then dest_forall tm else dest_exists tm
      val ("fun",[ty1,ty2]) = dest_type(snd(dest_var v))
  in
   if (ty1 = num) andalso (fst(dest_type ty2) = "prod")
    then
    (if is_exists tm
      then Ho_Rewrite.REWRITE_CONV
            [SpecFnPairExists(scalarizeTuple(fst(dest_exists tm))),FnPair_def]
            tm 
      else Ho_Rewrite.REWRITE_CONV
            [SpecFnPairForall(scalarizeTuple(fst(dest_forall tm))),FnPair_def]
            tm)
    else raise Error
  end)
  handle Interrupt => raise Interrupt 
    |    _         => hol_err "scalarization failure" "scalarize_CONV";

(*****************************************************************************)
(* MakeReachableChecker |- !u1...um. D tuple = ?v1...vn. tm                  *)
(*                                                                           *)
(* defines constants DTrans and DInit and proves                             *)
(*                                                                           *)
(*  Bth = |- DInit(tuple,(v1,...,vn)) = ...                                  *)
(*                                                                           *)
(*  Rth = |- DTrans((tuple,(v1,...,vn)),(tuple',(v1',...,vn'))) = ...        *)
(*                                                                           *)
(* and then proves th1 and the2 where                                        *)
(*                                                                           *)
(* th1 = |- !P. (!s1 s2. Reachable DTrans DInit (s1,s2) ==> P s1)            *)
(*              ==>                                                          *)
(*              !u1...um v1...vn. D tuple ==> !t. P(tuple<t>)                *)
(*                                                                           *)
(* th2 = |- !P. (!u1 ... um v1 ... vn.                                       *)
(*                 Reachable DTrans DInit ((u1,...,um),(v1,...,vn)))         *)
(*                 ==>                                                       *)
(*                 P(u1,...,um))                                             *)
(*              ==>                                                          *)
(*              !u1...um v1...vn. D tuple ==> !t. P(tuple<t>)                *)
(*                                                                           *)
(* The same variable names are used for traces (type num->bool) and state    *)
(* variables (type bool).  The notation "tuple<t>" denotes the tuple of      *)
(* applications to t.  For example                                           *)
(*                                                                           *)
(*  (clk,(req_1,req_0),check)<t> = (clk t, (req_1 t, req_0 t), check t)      *)
(*                                                                           *)
(* The pair of pairs ((Rth,Bth), (th1,th2)) is returned.                     *)
(*****************************************************************************)

fun MakeReachableChecker defth =
 let val (l,r) = dest_eq(concl(SPEC_ALL defth))
     val (con,tup) = dest_comb l
     val (name,ty) = dest_const con
     val (exvars,exbody) = strip_exists r
     val statetracevec = if null exvars then tup else mk_pair(tup,list_mk_pair exvars)
     val statevec = map_tuple (fn v => mk_var(fst(dest_var v),bool)) statetracevec
     val ((R,B),RBth) = ExtractTransitionSystem_CONV statevec r
     val InitName = name^"Init"
     val Bdef = new_definition(InitName, mk_eq(mk_var(InitName,type_of B),B))
     val Bcon = lhs(concl Bdef)
     val Bth = save_thm
                ((InitName ^ "_eqn"),
                 CONV_RULE(RHS_CONV pairLib.PAIRED_BETA_CONV)(AP_THM Bdef statevec))
     val TransName = name^"Trans"
     val Rdef = new_definition(TransName, mk_eq(mk_var(TransName,type_of R),R))
     val Rcon = lhs(concl Rdef)
     val statevec_statevec' = fst(pairSyntax.dest_pabs R)
     val Rth = save_thm
                ((TransName ^ "_eqn"),
                 CONV_RULE(RHS_CONV pairLib.PAIRED_BETA_CONV)(AP_THM Rdef statevec_statevec'))
     val RBth1 = (ONCE_REWRITE_RULE[SYM Bdef,SYM Rdef]RBth)
     val RBth2 = TRANS (SPEC_ALL defth) RBth1
     val th2 = if null exvars
                then ISPECL[Rcon,Bcon]HolBddTheory.ModelCheckAlways
                else ISPECL[Rcon,Bcon]HolBddTheory.ModelCheckAlwaysCor2
     val th3 = CONV_RULE
                (BINDER_CONV
                  (RAND_CONV
                    (HO_REWR_CONV(SpecFnPairForall tup))))
                th2
     val th4 = if null exvars
                then th3
                else
                 CONV_RULE
                 (BINDER_CONV
                  (RAND_CONV
                   (STRIP_QUANT_CONV
                    (RATOR_CONV
                     (RAND_CONV
                      (HO_REWR_CONV
                       (SpecFnPairExists(list_mk_pair exvars))))))))
                 th3
     val th5 = Ho_Rewrite.REWRITE_RULE [HolBddTheory.FnPair_def] th4
     val th6 = REWRITE_RULE [GSYM RBth2] th5
 in
  ((Rth,Bth),th6)
 end

val _ = Globals.priming := SOME "";

end

(* end *)





