structure StateEnum :> StateEnum = struct

open HolBdd;

(*
(* load "bossLib";  overkill *)
load "BasicProvers";
load "TotalDefn";
load "Ho_rewrite";
load "Num_conv";
load "unwindLib";
load "PGEN";
load "HolBdd";
load "HolBddTheory";
*)

type term = Term.term
type thm = Thm.thm;

local 

open Globals HolKernel Parse basicHol90Lib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open Psyntax BasicProvers;

in

(* open bossLib;          *)
(* open BasicProvers;     *)
(* open arithmeticTheory; *)
(* open pairTheory;       *)
(* open Ho_rewrite;       *)
(* open Num_conv;         *)
(* open PGEN;             *)
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
(*    |- t2(v1,...,vn) = t2(v1,...,vn)                                       *)
(*    --------------------------------                                       *)
(*             |- t1 = t2                                                    *)
(*****************************************************************************)

fun PGEN_EXT th =
 let val vars = rand(rand(concl th))
 in
  EXT(PGEN.PGEN (genvar(type_of vars)) vars th)
 end

val DEPTH_EXISTS_CONV = unwindLib.DEPTH_EXISTS_CONV
and EXPAND_AUTO_CONV  = unwindLib.EXPAND_AUTO_CONV;

(* 
  fun g tm = set_goal([],tm); 
*)

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
(* Convert an ML integer to a HOL numerical constant                         *)
(*****************************************************************************)

val num = ``:num``;

fun intToTerm n = Term.mk_numeral(Arbnum.fromInt n);

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
(* Delete a BDD from the BDD hash table                                      *)
(*****************************************************************************)

val deleteBdd = Polyhash.remove(fst(snd(!bdd_state)));

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
     val [CITER0,CITER_SUC]  = CONJUNCTS HolBddTheory.ReachBy_rec
     val ci0                 = ISPECL[R,B,st]CITER0
     val cisuc               = GEN ntm 
                                (Ho_rewrite.REWRITE_RULE
                                  [HolBddTheory.Next_def,pairTheory.EXISTS_PROD]
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
              then (deleteBdd cidescr;iterate (n+1) (cidescr',cibdd'))
              else iterate (n+1) (cidescr',cibdd')
      end
 in
  let val n       = iterate 0 (addEquation ci0)
      val ntm     = intToTerm n
      val ntm'    = intToTerm(n+1)
      val th1     = bddOracle ``ReachBy ^R ^B ^ntm' ^st =
                                  ReachBy ^R ^B ^ntm ^st``
      val th2     = MATCH_MP
                     HolBddTheory.ReachBy_fixedpoint
                      (MATCH_MP
                        EQ_EXT
                        (PGEN.PGEN 
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
     val [ReachIn0,ReachIn_SUC] = CONJUNCTS HolBddTheory.ReachIn_def
     val i0                     = AP_THM(ISPECL[R,B]ReachIn0)st
     val isuc                   = Ho_rewrite.REWRITE_RULE (* needs Ho_rewrite *)
                                   [HolBddTheory.Next_def,pairTheory.EXISTS_PROD]
                                   (GEN ntm (AP_THM(ISPECL[R,B,ntm]ReachIn_SUC)st))
     val [CITER0,CITER_SUC]     = CONJUNCTS HolBddTheory.ReachBy_ReachIn
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
               then(deleteBdd idescr; 
                    deleteBdd cidescr; 
                    deleteBdd idescr';
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
                     HolBddTheory.ReachBy_fixedpoint
                      (MATCH_MP
                        EQ_EXT
                        (PGEN.PGEN 
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
      Ho_rewrite.REWRITE_RULE 
       [pairTheory.FORALL_PROD,pairTheory.PAIR_EQ] 
       (ISPECL [``DFF``,st] HolBddTheory.Stable_def)
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
     val [ReachIn0,ReachIn_SUC]    = CONJUNCTS HolBddTheory.ReachIn_def
     val i0                  = AP_THM(ISPECL[R,B]ReachIn0)st
     val isuc                = Ho_rewrite.REWRITE_RULE (* needs Ho_rewrite *)
                                [HolBddTheory.Next_def,pairTheory.EXISTS_PROD]
                                (GEN ntm (AP_THM(ISPECL[R,B,ntm]ReachIn_SUC)st))
     val stbthm              = Ho_rewrite.REWRITE_RULE (* needs Ho_rewrite *)
                                [HolBddTheory.Next_def,pairTheory.FORALL_PROD]
                                (ISPECL[R,st]HolBddTheory.Stable_def)
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
     val th2     = PGEN.PGEN st_var st th1
     val Live_th = Ho_rewrite.REWRITE_RULE
                     [pairTheory.EXISTS_PROD,pairTheory.FORALL_PROD]
                     (ISPEC R HolBddTheory.Live_def)
     val (ldescr,lbdd)  = addEquation Live_th
     val th3 = bddOracle ``Live ^R``
     val th4 = SPEC st (MATCH_MP HolBddTheory.Reachable_Stable (CONJ th3 th2))
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
 PROVE [] ``!w u v. (w ==> (u = v)) ==> (w /\ u = w /\ v)``;

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
 *     partition (curry (op =)) [1,2,3,1,1,2,2,3,4,5,4,4,3,2,1];
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

val AND_OR = PROVE [] ``A /\ (B \/ C) = (A /\ B) \/ (A /\ C)``;
val OR_AND = PROVE [] ``(A \/ B) /\ C = (A /\ C) \/ (B /\ C)``;

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
     val [CITER0,CITER_SUC]  = CONJUNCTS HolBddTheory.ReachBy_rec
     val ci0                 = ISPECL[R,B,st]CITER0
     val cisuc               = Ho_rewrite.REWRITE_RULE
                                [HolBddTheory.Next_def,pairTheory.EXISTS_PROD]
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
                                (Ho_rewrite.REWRITE_RULE[Rthm] cisuc)
 in
  CONJ ci0 (GEN ntm cisuc_simp)
 end;

(* Version using ReachIn_rec instead of ReachBy_rec *)

fun MakeSimpReachInRecThm(Rthm,Bthm) =
 let val (R,st_st')             = dest_comb(lhs(concl(SPEC_ALL Rthm)))
     val (B,st_b)               = dest_comb(lhs(concl(SPEC_ALL Bthm)))
     val (st,st')               = dest_pair st_st'
     val ntm                    = ``n:num``
     val [ReachIn0,ReachIn_SUC] = CONJUNCTS HolBddTheory.ReachIn_rec
     val i0                     = ISPECL[R,B,st] ReachIn0
     val isuc                   = Ho_rewrite.REWRITE_RULE
                                   [HolBddTheory.Next_def,pairTheory.EXISTS_PROD]
                                   (ISPECL[R,B,ntm,st]ReachIn_SUC)
     val isuc_simp             = time (simpLib.SIMP_RULE 
                                   HOLSimps.hol_ss
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
                                (Ho_rewrite.REWRITE_RULE[Rthm] isuc)
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
              then (deleteBdd cidescr;iterate (n+1) (cidescr',cibdd'))
              else iterate (n+1) (cidescr',cibdd')
      end
     val n       = time (iterate 0) (addEquation ci0)
     val ntm     = intToTerm n
     val ntm'    = intToTerm(n+1)
     val th1     = bddOracle ``ReachBy ^R ^B ^ntm' ^st =
                                 ReachBy ^R ^B ^ntm ^st``
     val th2     = MATCH_MP
                    HolBddTheory.ReachBy_fixedpoint
                     (MATCH_MP
                       EQ_EXT
                       (PGEN.PGEN 
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
     val prev_thm1  = Ho_rewrite.REWRITE_RULE 
                       [pairTheory.EXISTS_PROD,Rthm] 
                       (ISPECL[R,``Q:^(type_of st)->bool``,st]HolBddTheory.Prev_def)
     val prev_thm2  = RIGHT_CONV_RULE
                       (DEPTH_EXISTS_CONV (REWRITE_CONV[OR_AND])
                         THENC TOP_DEPTH_CONV EX_OR_CONV
                         THENC LIST_DISJ_CONV UNWIND_SYM_CONV
                         THENC LIST_DISJ_CONV(DEPTH_EXISTS_CONV LIST_ELIM_LHS_CONV)
                         THENC LIST_DISJ_CONV (EXPAND_AUTO_CONV[]))
                       prev_thm1
     val prev_thm3 = GEN (mk_var("Q",type_of Q)) prev_thm2
     fun prev s = Ho_rewrite.REWRITE_RULE
                   [HolBddTheory.Eq_def,pairTheory.PAIR_EQ](SPEC ``Eq ^s`` prev_thm3)
     val _          = print "done"
     fun get_st tm = 
      let val s = rhs(concl(REWRITE_CONV[ASSUME tm]st))
      in
       subst (map (fn v => (F,v)) (free_vars s)) s
      end
     val s_0        = get_st(findModel ``^refute_descr /\ ~(^Qdescr)``)
     val s_0_thm    = bddOracle(mk_neg(mk_comb(Q,s_0)))
     fun get_sts [] s acc                   = acc
      |  get_sts ((descr,bdd)::trace) s acc =
          let val prev_th = prev s
              val (descr',bdd') = addEquation prev_th
              val s' = get_st(findModel(mk_conj(descr',descr)))
              val nxt_thm = 
               Ho_rewrite.REWRITE_RULE
                [HolBddTheory.Prev_Next_Eq](bddOracle(mk_comb(rator descr',s')))
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
     val prev_thm1  = Ho_rewrite.REWRITE_RULE 
                       [pairTheory.EXISTS_PROD,Rthm] 
                       (ISPECL[R,``Q:^(type_of st)->bool``,st]HolBddTheory.Prev_def)
     val prev_thm2  = RIGHT_CONV_RULE
                       (DEPTH_EXISTS_CONV (REWRITE_CONV[OR_AND])
                         THENC TOP_DEPTH_CONV EX_OR_CONV
                         THENC LIST_DISJ_CONV UNWIND_SYM_CONV
                         THENC LIST_DISJ_CONV(DEPTH_EXISTS_CONV LIST_ELIM_LHS_CONV)
                         THENC LIST_DISJ_CONV (EXPAND_AUTO_CONV[]))
                       prev_thm1
     val prev_thm3 = GEN (mk_var("Q",type_of Q)) prev_thm2
     fun prev s = Ho_rewrite.REWRITE_RULE
                   [HolBddTheory.Eq_def,pairTheory.PAIR_EQ](SPEC ``Eq ^s`` prev_thm3)
     val _          = print "done"
     fun get_st tm = 
      let val s = rhs(concl(REWRITE_CONV[ASSUME tm]st))
      in
       subst (map (fn v => (F,v)) (free_vars s)) s
      end
     val s_0        = get_st(findModel ``^refute_descr /\ ~(^Qdescr)``)
     val s_0_thm    = bddOracle(mk_neg(mk_comb(Q,s_0)))
     fun get_sts [] s acc                   = acc
      |  get_sts ((descr,bdd)::trace) s acc =
          let val prev_th = prev s
              val (descr',bdd') = addEquation prev_th
              val s' = get_st(findModel(mk_conj(descr',descr)))
              val nxt_thm = 
               Ho_rewrite.REWRITE_RULE
                [HolBddTheory.Prev_Next_Eq](bddOracle(mk_comb(rator descr',s')))
          in
           get_sts trace s' ((s',nxt_thm)::acc)
          end
     val sl = get_sts trace s_0 []
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

val ABS_EXISTS_THM = (* Adapted from Hol sources *)
   let val th1 = ASSUME (--`?rep:'b->'a. TYPE_DEFINITION P rep`--)
       and th2 = MK_EXISTS (SPEC (--`P:'a->bool`--) TYPE_DEFINITION)
       val def = EQ_MP th2 th1
       val asm = ASSUME (#Body(Rsyntax.dest_exists(concl def)))
       val (asm1,asm2)  = CONJ_PAIR asm
       val rep_eq =
         let val th1 = DISCH (--`a:'b=a'`--)
                         (AP_TERM (--`rep:'b->'a`--) (ASSUME (--`a:'b=a'`--)))
         in IMP_ANTISYM_RULE (SPECL [(--`a:'b`--),(--`a':'b`--)] asm1) th1
         end
       val ABS = (--`\r:'a. @a:'b. r = rep a`--)
       val absd =  RIGHT_BETA (AP_THM (REFL ABS) (--`rep (a:'b):'a`--))
       val lem = SYM(SELECT_RULE(EXISTS ((--`?a':'b.a=a'`--),(--`a:'b`--))
                                        (REFL (--`a:'b`--))))
       val TH1 = GEN (--`a:'b`--)
                     (TRANS(TRANS absd (SELECT_EQ (--`a':'b`--) rep_eq)) lem)
       val t1 = SELECT_RULE(EQ_MP (SPEC (--`r:'a`--) asm2)
                                  (ASSUME (--`(P:'a->bool) r`--)))
       val absd2 =  RIGHT_BETA (AP_THM (REFL ABS) (--`r:'a`--))
       val imp1 = DISCH (--`(P:'a->bool) r`--) (SYM (SUBS [SYM absd2] t1))
       val t2 = EXISTS ((--`?a:'b. r:'a = rep a`--), (--`^ABS r`--))
                       (SYM(ASSUME (--`rep(^ABS (r:'a):'b) = r`--)))
       val imp2 = DISCH (--`rep(^ABS (r:'a):'b) = r`--)
                        (EQ_MP (SYM (SPEC (--`r:'a`--) asm2)) t2)
       val TH2 = GEN (--`r:'a`--) (IMP_ANTISYM_RULE imp1 imp2)
       val CTH = CONJ TH1 TH2
       val ath = Rsyntax.subst [ABS |-> Term`abs:'a->'b`] (concl CTH)
       val eth1 = EXISTS ((--`?abs:'a->'b. ^ath`--), ABS) CTH
   in
    Ho_rewrite.REWRITE_RULE[GSYM TYPE_DEFINITION](GEN_ALL (DISCH_ALL eth1))
   end;


(*****************************************************************************)
(* Generate the definition of abstraction and representation functions       *)
(* for encoding enumeration types as bit strings. Takes as argument the      *)
(* initiality theorem for the datatype.                                      *)
(*                                                                           *)
(* The names of the functions are the name of the type prefixed with         *)
(* "abs_" and "rep_".  For example, if:                                      *)
(*                                                                           *)
(* altitude_vals =                                                           *)
(*     |- !e0 e1 e2.                                                         *)
(*          ?!fn.                                                            *)
(*            (fn away = e0) /\                                              *)
(*            (fn near_pre_selected = e1) /\                                 *)
(*            (fn at_pre_selected = e2)                                      *)
(*                                                                           *)
(* then                                                                      *)
(*                                                                           *)
(*    define_rep altitude_vals                                               *)
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
     val (qnt,lam) = Psyntax.dest_comb bdy
     val (lamv,cnj) = Psyntax.dest_abs lam
     val m = length vs
     val (_,[ty,tyvar]) = Psyntax.dest_type(type_of lamv)
     val (tyname,[]) = Psyntax.dest_type ty
     val rep_fun_name = "rep_" ^ tyname
     val range = List.tabulate(m,word_rep(bits_needed m))
     val th1 = ISPECL range th
     val th2 = CONJUNCT1
                (Ho_rewrite.PURE_REWRITE_RULE 
                  [Ho_theorems.EXISTS_UNIQUE_THM] 
                  th1)
     val rep_spec = Rsyntax.new_specification
                     {name    = rep_fun_name ^ "_def", 
                      sat_thm = th2,
                      consts  = [{const_name = rep_fun_name, fixity = Prefix}]}
     val induct_thm = Prim_rec.prove_induction_thm th
     val rep_fun_ty = snd(Psyntax.dest_var(fst(Psyntax.dest_exists(concl th2))))
     val rep_fun = Psyntax.mk_const(rep_fun_name,rep_fun_ty)
     val one_one_goal = ``!x' x''. (^rep_fun x' = ^rep_fun x'') ==> (x' = x'')``
     val one_one_thm = prove(one_one_goal, 
                             REPEAT(INDUCT_THEN induct_thm ASSUME_TAC)
                              THEN REWRITE_TAC[rep_spec,pairTheory.PAIR_EQ])
     val (_,[_,x_ty]) = Psyntax.dest_type rep_fun_ty
     val x_tm = Psyntax.mk_var("x",x_ty)
     val range_fun_var = Psyntax.mk_var(("range_" ^ tyname),``:^x_ty->bool``)
     val range_def = new_definition
                      (("range_" ^ tyname ^ "_def"),
                       Psyntax.mk_eq
                        (Psyntax.mk_comb(range_fun_var,x_tm),
                         foldr 
                          (fn(tup,tm) => mk_disj1(Psyntax.mk_eq(x_tm,tup),tm)) 
                          F 
                          range))
     val range_fun_con = Psyntax.mk_const(("range_" ^ tyname),``:^x_ty->bool``)
     val range_goal = ``!x. ^range_fun_con x = (?x'. x = ^rep_fun x')``
     val range_thm = prove
                      (range_goal,
                       REWRITE_TAC[range_def]
                        THEN GEN_TAC
                        THEN EQ_TAC
                        THENL[PROVE_TAC[rep_spec],
                              Ho_rewrite.REWRITE_TAC[HolBddTheory.EXISTS_IMP]
                               THEN INDUCT_THEN induct_thm ASSUME_TAC
                               THEN PROVE_TAC[rep_spec]])
     val ty_def_thm = EQ_MP
                       (SYM(ISPECL[range_fun_con,rep_fun]TYPE_DEFINITION))
                       (CONJ one_one_thm range_thm)
     val abs_exists = MATCH_MP ABS_EXISTS_THM  ty_def_thm
     val abs_fun_name = "abs_" ^ tyname
     val abs_spec = Rsyntax.new_specification
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

val _ = Globals.priming := SOME "";

end
end
