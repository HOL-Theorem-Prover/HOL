
(*****************************************************************************)
(* DerivedBddRules.sml                                                       *)
(* -------------------                                                       *)
(*                                                                           *)
(* Some BDD utilities and derived rules using MuDDy and PrimitiveBddRules    *)
(* (builds on some of Ken Larsen's code)                                     *)
(*****************************************************************************)
(*                                                                           *)
(* Revision history (major events only):                                     *)
(*                                                                           *)
(*   Mon Oct  8 10:27:40 BST 2001 -- created file                            *)
(*   Thu Nov  1 21:04:27 GMT 2001 -- updated for judgement assumptions       *)
(*   Mon Nov  5 11:15:51 GMT 2001 -- updated documentation in comments       *)
(*   Wed Nov  7 11:38:19 GMT 2001 -- changed to MachineTransitionTheory      *)
(*   Tue Nov 27 15:42:00 GMT 2001 -- added findTrace and BddRhsOracle        *)
(*   Thu Mar 28 09:40:05 GMT 2002 -- added signature file                    *)
(*                                                                           *)
(*****************************************************************************)

structure DerivedBddRules :> DerivedBddRules = struct

(*
load "pairLib";
load "PairRules";
load "numLib";
load "PrimitiveBddRules";
load "MachineTransitionTheory";

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();
*)

(*
local
*)

open pairSyntax;
open pairTools;
open PairRules;
open numLib;
open PrimitiveBddRules;
open bdd;
open Varmap;
open Thm;
open PrimitiveBddRules;

open HolKernel Parse boolLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

fun hol_err msg func = 
 (print "DerivedBddRules: hol_err \""; print msg; 
  print "\" \""; print func; print "\"\n";
  raise mk_HOL_ERR "HolBdd" func msg);

(*****************************************************************************)
(* Ken Larsen writes:                                                        *)
(* In the current mosml release List.foldl is tail recursive but             *)
(* List.foldr isn't.  In the upcomming mosml release foldr might be tail     *)
(* recursive.  But a tail recursive version of foldr is easy to uptain       *)
(* (as Michael notes):                                                       *)
(*****************************************************************************)

fun foldr f start ls = List.foldl f start (rev ls);

(*
in
*)

(*****************************************************************************)
(* Test equality of BDD component of two term_bdds and return true or false  *)
(*****************************************************************************)

fun BddEqualTest tb1 tb2 = bdd.equal (getBdd tb1) (getBdd tb2);

(*****************************************************************************)
(* Test if the BDD part is TRUE or FALSE                                     *)
(*****************************************************************************)

fun isTRUE  tb = bdd.equal (getBdd tb) bdd.TRUE
and isFALSE tb = bdd.equal (getBdd tb) bdd.FALSE;

(*****************************************************************************)
(* Count number of states (code from Ken Larsen)                             *)
(*****************************************************************************)

fun statecount b =
 let val sat    = bdd.satcount b
     val total  = Real.fromInt(bdd.getVarnum())
     val sup    = bdd.scanset(bdd.support b)
     val numsup = Real.fromInt(Vector.length sup)
     val free   = total - numsup
 in  if bdd.equal b bdd.TRUE
      then 0.0
      else sat / Math.pow(2.0, free)
 end;

(*****************************************************************************)
(* Destruct a term corresponding to a BuDDY BDD binary operation (bddop).    *)
(* Fail if not such a term.                                                  *)
(*****************************************************************************)

exception dest_BddOpError;

fun dest_BddOp tm =
 if is_neg tm
  then
   let val t = dest_neg tm
   in
    if is_conj t 
     then let val (t1,t2) = dest_conj t in (Nand, t1, t2) end else
    if is_disj t
     then let val (t1,t2) = dest_disj t in (Nor, t1, t2) end
     else raise dest_BddOpError
   end 
  else
   case strip_comb tm of
      (opr, [t1,t2]) => (case fst(dest_const opr) of
                            "/\\"  => if is_neg t1 
                                       then (Lessth, dest_neg t1, t2) else
                                      if is_neg t2
                                       then (Diff, t1, dest_neg t2)
                                       else (And, t1, t2)
                          | "\\/"  => (Or, t1, t2)
                          | "==>"  => (Imp, t1, t2)
                          | "="    => (Biimp, t1, t2)
                          | _      => raise dest_BddOpError)
    | _              => raise dest_BddOpError;


(*****************************************************************************)
(* Function that always raises exception fail                                *)
(* (useful as argument (leaffn) to GenTermToTermBdd)                         *)
(*****************************************************************************)

exception fail;

fun failfn _ = raise fail;

(*****************************************************************************)
(* Scan a term and construct a term_bdd using the primitive operations       *)
(* when applicable, and a supplied function otherwise                        *)
(*****************************************************************************)

local
fun fn3(f1,f2,f3)(x1,x2,x3) = (f1 x1, f2 x2, f3 x3)
in
fun GenTermToTermBdd leaffn vm tm =
 let fun recfn tm = 
  if tm = T 
   then BddCon true vm else
  if tm = F 
   then BddCon false vm else
  if is_var tm 
   then BddVar true vm tm else
  if is_neg tm 
   then let val tm' = dest_neg tm
        in
         if is_var tm' then BddVar false vm tm' else BddNot(recfn tm')
        end else
  if is_cond tm 
   then (BddIte o fn3(recfn,recfn,recfn) o dest_cond) tm else
  if is_forall tm 
   then let val (vars,bdy) = strip_forall tm
        in
         (BddAppall vars o fn3(I,recfn,recfn) o dest_BddOp) bdy
          handle dest_BddOpError => (BddForall vars o recfn) bdy
        end else
  if is_exists tm 
   then let val (vars,bdy) = strip_exists tm
        in
         (BddAppex  vars o fn3(I,recfn,recfn) o dest_BddOp) bdy
         handle dest_BddOpError => (BddExists vars o recfn) bdy
        end
   else ((BddOp o fn3(I,recfn,recfn) o dest_BddOp) tm
         handle dest_BddOpError => leaffn tm)
 in
  recfn tm
 end
end;

(*****************************************************************************)
(* Extend a varmap with a list of variables                                  *)
(*****************************************************************************)

fun extendVarmap [] vm = vm
 |  extendVarmap (v::vl) vm =
     case Varmap.peek vm (name v) of
        SOME _ => extendVarmap vl vm
      | NONE   => let val n   = getVarnum()
                      val _   = bdd.setVarnum(n+1)
                  in 
                   extendVarmap vl (Varmap.insert (name v, n) vm)
                  end;

(*****************************************************************************)
(* Convert a BDD to a nested conditional term with respect to a varmap       *)
(*****************************************************************************)

exception bddToTermError;

fun bddToTerm varmap =
 let val pairs = Varmap.dest varmap
     fun get_node_name n =
      case assoc2 n pairs of
         SOME(str,_) => str
       | NONE        => (print("Node "^(Int.toString n)^" has no name");
                         raise bddToTermError)
     fun bddToTerm_aux bdd =
      if (bdd.equal bdd bdd.TRUE)
       then T
       else
        if (bdd.equal bdd bdd.FALSE)
         then F
         else Psyntax.mk_cond(mk_var(get_node_name(bdd.var bdd),bool),
                              bddToTerm_aux(bdd.high bdd),
                              bddToTerm_aux(bdd.low bdd))
 in
  bddToTerm_aux
 end;

(*****************************************************************************)
(*               ass vm tm |--> b                                            *)
(*  -----------------------------------------------                          *)
(*  [oracles: HolBdd] ass |- tm = ^(bddToTerm vm b)                          *)
(*****************************************************************************)

fun TermBddToEqThm tb =
 let val (_,_,vm,tm,b) = dest_term_bdd tb
     val tm' = bddToTerm vm b
     val tb' = GenTermToTermBdd failfn vm tm'
 in
  BddThmOracle(BddOp(bdd.Biimp,tb,tb'))
 end;

(*****************************************************************************)
(* Global assignable varmap                                                  *)
(*****************************************************************************)

val global_varmap = ref(Varmap.empty);

fun showVarmap () = Varmap.dest(!global_varmap);

(*****************************************************************************)
(* Add variables to global_varmap and then call GenTermToTermBdd             *)
(* using the global function !termToTermBddFun on leaves                     *)
(*****************************************************************************)

exception termToTermBddError;

val termToTermBddFun = 
 ref(fn (tm:term) => (raise termToTermBddError));

fun termToTermBdd tm =
 let val vl = rev(all_vars tm)     (* all_vars returns vars in reverse order *)
     val vm = extendVarmap vl (!global_varmap)
     val _  = global_varmap := vm
 in
  GenTermToTermBdd (!termToTermBddFun) vm tm
 end;

(*****************************************************************************)
(*  MkPrevThm (|- R((v1,...,vn),(v1',...,vn')) = ...) =                      *)
(*                                                                           *)
(*    |- Prev R (Eq (v1',...,vn'))) (v1,...,vn) = ...                        *)
(*****************************************************************************)

fun MkPrevThm Rth =
 let val (Rcon, s_s') = Term.dest_comb(lhs(concl(SPEC_ALL Rth)))
     val (s,s') = pairSyntax.dest_pair s_s'
     val _ = print "\nProving simplified backward image theorem ...\n"
     val PrevTh =
       (simpLib.SIMP_RULE
        boolSimps.bool_ss
        [pairTheory.EXISTS_PROD,MachineTransitionTheory.Eq_def,pairTheory.PAIR_EQ,Rth])
       (ISPECL[Rcon,``Eq ^s'``,s]MachineTransitionTheory.Prev_def)
 in
  PrevTh
 end;

(*****************************************************************************)
(* Flatten a varstruct term into a list of variables (also in StateEnum).    *)
(*****************************************************************************)

fun flatten_pair t =
if is_pair t
 then List.foldr (fn(t,l) => (flatten_pair t) @ l) [] (strip_pair t)
 else [t];

(*****************************************************************************)
(* MkIterThms ReachBy_rec``R((v1,...,vn),(v1',...,vn'))`` ``B(v1,...,vn)`` = *)
(*  ([|- ReachBy R B 0 (v1,...,vn) = B(v1,...,vn),                           *)
(*    |- !n. ReachBy R B (SUC n) (v1,...,vn) =                               *)
(*                ReachBy R B n (v1,...,vn)                                  *)
(*                \/                                                         *)
(*                ?v1'...vn'. ReachBy R B n (v1',...,vn')                    *)
(*                            /\                                             *)
(*                            R ((v1',...,vn'),(v1,...,vn))]                 *)
(*                                                                           *)
(*                                                                           *)
(* MkIterThms ReachIn_rec``R((v1,...,vn),(v1',...,vn'))`` ``B(v1,...,vn)`` = *)
(*  ([|- ReachIn R B 0 (v1,...,vn) = B(v1,...,vn),                           *)
(*    |- !n. ReachIn R B (SUC n) (v1,...,vn) =                               *)
(*                ?v1'...vn'. ReachIn R B n (v1',...,vn')                    *)
(*                            /\                                             *)
(*                            R ((v1',...,vn'),(v1,...,vn))]                 *)
(*****************************************************************************)

fun MkIterThms reachth Rtm Btm =
 let val (R,st_st') = dest_comb Rtm
     val (st,st') = dest_pair st_st'
     val (B,st0) = dest_comb Btm
     val _ = Term.aconv st st0 
             orelse hol_err "R and B vars not consistent" "MkReachByIterThms"
     val ty     = type_of st
     val th = INST_TYPE[(``:'a`` |-> ty),(``:'b`` |-> ty)]reachth
     val (th1,th2) = (CONJUNCT1 th, CONJUNCT2 th)
     val ntm = mk_var("n",num)
     val th3 = SPECL[R,B,st]th1
     val th4 = CONV_RULE 
                (RHS_CONV
                 (ONCE_DEPTH_CONV
                  (Ho_Rewrite.REWRITE_CONV[pairTheory.EXISTS_PROD]
                    THENC RENAME_VARS_CONV 
                           (List.map (fst o dest_var) (flatten_pair st')))))
                (SPECL[R,B,ntm,st]th2)

 in
  (th3, GEN ntm th4)
 end;

(*****************************************************************************)
(* Perform disjunctive partitioning                                          *)
(* The simplification assumes R is of the form:                              *)
(*                                                                           *)
(*  R((x,y,z),(x',y',z'))=                                                   *)
(*   ((x' = E1(x,y,z)) /\ (y' = y)         /\ (z' = z))                      *)
(*    \/                                                                     *)
(*   ((x' = x)         /\ (y' = E2(x,y,z)) /\ (z' = z))                      *)
(*    \/                                                                     *)
(*   ((x' = x)         /\ (y' = y)         /\ (z' = E3(x,y,z)))              *)
(*                                                                           *)
(* Then, for example, the equation:                                          *)
(*                                                                           *)
(*   ReachBy R B (SUC n) (x,y,z) =                                           *)
(*     ReachBy R B n (x,y,z)                                                 *)
(*     \/                                                                    *)
(*     (?x_ y_ z_. ReachBy n R B (x_,y_,z_) /\ R((x_,y_,z_),(x,y,z))))       *)
(*                                                                           *)
(* is simplified to:                                                         *)
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

val MakeSimpRecThm =
 time 
  (simpLib.SIMP_RULE boolSimps.bool_ss [LEFT_AND_OVER_OR,EXISTS_OR_THM]);

(*****************************************************************************)
(* ASSUME for term_bdd                                                       *)
(*****************************************************************************)

fun BddAssume tm =
    BddEqMp ((SYM o EQT_INTRO o ASSUME) tm) (BddCon true Varmap.empty)       

(*****************************************************************************)
(* Convert a theorem to a term_bdd                                           *)
(*****************************************************************************)

fun thmToTermBdd th = 
    BddEqMp ((SYM o EQT_INTRO) th) (BddCon true Varmap.empty)

(*****************************************************************************)
(*  asl |- t1 = t2   ass vm t1' |--> b                                       *)
(*  ----------------------------------                                       *)
(*      (asl U ass) vm t2' |--> b'                                           *)
(*                                                                           *)
(* where t1 can be instantiated to t1' and t2' is the corresponding          *)
(* instance of t2                                                            *)
(*****************************************************************************)

fun BddApThm th tb =
 let val (_,_,vm,t1',b) = dest_term_bdd tb
 in
  BddEqMp (REWR_CONV th t1') tb 
   handle HOL_ERR _ => hol_err "REWR_CONV failed" "BddApthm"
 end;

(*****************************************************************************)
(*  BddApRestrict : term_bdd -> term -> term_bdd                             *)
(*                                                                           *)
(*   ass vm t  |--> b                                                        *)
(*   -----------------                                                       *)
(*   ass vm tm |--> b'                                                       *)
(*                                                                           *)
(* Generates the BDD of a supplied term if it can be obtained by restricting *)
(* a given term_bdd                                                          *)
(*****************************************************************************)

exception BddApRestrictError;

fun BddApRestrict tb tm =
 let val (_,_,vm,t,_) = dest_term_bdd tb
     val (sub_tm,sub_ty) = match_term t tm
     val _ = if null sub_ty 
              then () 
              else (print "match produced a non-empty type instasntiation\n";
                    raise BddApRestrictError)
     val sub_tb = List.map 
                   (fn {redex = v, residue = c} => 
                    (BddVar true vm v, 
                     if c=T then BddCon true  vm else 
                     if c=F then BddCon false vm 
                            else (print_term c;
                                  print " not a boolean constant\n";
                                  raise BddApRestrictError)))
                   sub_tm
 in
  BddRestrict sub_tb tb
 end;

(*****************************************************************************)
(*  ass vm t |--> b                                                          *)
(*  ----------------                                                         *)
(*  ass vm tm |--> b'                                                        *)
(*                                                                           *)
(* where boolean variables in t can be renamed to get tm and b' is           *)
(* the corresponding replacement of BDD variables in b                       *)
(*****************************************************************************)

exception BddApReplaceError;

fun BddApReplace tb tm =
 let val (_,_,vm,t,b) = dest_term_bdd tb
     val (tml,tyl)  = match_term t tm
     val _          = if null tyl then () else raise BddApReplaceError
     val tbl        = (List.map 
                        (fn{redex=old,residue=new}=> 
                          (BddVar true vm old, BddVar true vm new))
                        tml 
                       handle BddVarError => raise BddApReplaceError)
 in
   BddReplace tbl tb
 end;

(*
** BddSubst defined below applies a substitution
** 
**  [(oldtb1,newtb1),...,(oldtni,newtbi)]
** 
** to a term_bdd, where oldtbp (1 <= p <= i) must be of the form 
**
**   vm vp |--> bp 
**
** where vp is a variable, and v1,...,vp,...,vi are all distinct.
** 
** The preliminary version below separates the substitution
** into a restriction (variables mapped to T or F) followed
** by a variable renaming (replacement).
** 
** A more elaborate scheme will be implemented after
** BuDDy's bdd_veccompose is available in MuDDy.
*)

(*****************************************************************************)
(* Split a substitution                                                      *)
(*                                                                           *)
(*   [(oldtb1,newtb1),...,(oldtni,newtbi)]                                   *)
(*                                                                           *)
(* into a restriction and variable renaming,                                 *)
(* failing if this isn't possible                                            *)
(*****************************************************************************) 

val split_subst =
 List.partition 
  (fn (tb,tb')=>
    let val tm' = getTerm tb'
    in
     (tm'=T) orelse (tm'=F)
    end);

(*****************************************************************************)
(*                    [(ass1 vm v1 |--> b1 , ass1' vm tm1 |--> b1'),         *)
(*                                    .                                      *)
(*                                    .                                      *)
(*                                    .                                      *)
(*                     (assi vm vi |--> bi , assi' vm tmi |--> bi')]         *)
(*                    ass vm tm |--> b                                       *)
(*  ------------------------------------------------------------------------ *)
(*   (as1 U ass1' U ... U assi U assi' U ass)                                *)
(*   vm                                                                      *)
(*   (subst[v1 |-> tm1, ... , vi |-> tmi]tm)                                 *)
(*   |-->                                                                    *)
(*   <appropriate BDD>                                                       *)
(*****************************************************************************)

fun BddSubst tbl tb =
 let val (res,rep) = split_subst tbl
 in
  BddReplace rep (BddRestrict res tb)
 end;

(*****************************************************************************)
(*  ass vm t |--> b                                                          *)
(*  -----------------                                                        *)
(*  ass vm tm |--> b'                                                        *)
(*                                                                           *)
(* where boolean variables in t can be instantiated to get tm and b' is      *)
(* the corresponding replacement of BDD variables in b                       *)
(*****************************************************************************)

exception BddApSubstError;

fun BddApSubst tb tm =
 let val (_,_,vm,t,b) = dest_term_bdd tb
     val (tml,tyl)  = match_term t tm
     val _          = if null tyl then () else (print "type match problem\n";
                                                raise BddApSubstError)
     val tbl        = (List.map 
                        (fn{redex=old,residue=new}=> 
                          (BddVar true vm old, 
                           GenTermToTermBdd (!termToTermBddFun) vm new))
                        tml 
                       handle BddVarError => raise BddApSubstError)
 in
   BddSubst tbl tb
 end;

(* Test examples ==================================================================

val tb1 = termToTermBdd ``x /\ y /\ z``;

val tbx = termToTermBdd ``x:bool``
and tby = termToTermBdd ``y:bool``
and tbz = termToTermBdd ``z:bool``
and tbp = termToTermBdd ``p:bool``
and tbq = termToTermBdd ``q:bool``
and tbT = termToTermBdd T
and tbF = termToTermBdd F;

(* Repeat to sync all the varmaps! *)

val tbl = [(tbx,tbp),(tby,tbq),(tbz,tbF)];
val tb2 = BddSubst tbl tb1;

val tb3 = BddApSubst tb1 ``p /\ T /\ q``;
======================================================= End of test examples *)

(*****************************************************************************)
(*          asl |- t1 = t2                                                   *)
(*   ------------------------------                                          *)
(*   (addList ass [])  vm t1 |--> b                                          *)
(*                                                                           *)
(* Fails if t2 is not built from variables using bddops                      *)
(*****************************************************************************)

fun eqToTermBdd leaffn vm th =
 let val th' = SPEC_ALL th
     val tm  = rhs(concl th')
 in
  BddEqMp (SYM th') (GenTermToTermBdd leaffn vm tm)
 end;

(*****************************************************************************)
(* Convert an ml positive integer to a HOL numeral                           *)
(*****************************************************************************)

fun intToTerm n = numSyntax.mk_numeral(Arbnum.fromInt n);

(*****************************************************************************)
(*  ass vm tm |--> b   conv tm  =  asl |- tm = tm'                           *)
(*  ----------------------------------------------                           *)
(*         (addList ass asl) vm tm' |--> b                                   *)
(*****************************************************************************)

fun BddApConv conv tb = BddEqMp (conv(getTerm tb)) tb;

(*****************************************************************************)
(*   |- t1 = t2                                                              *)
(*   ----------                                                              *)
(*     |- t1                                                                 *)
(*                                                                           *)
(* if the BDD of t2 (using GenTermToTermBdd) is TRUE                         *)
(*****************************************************************************)

fun BddRhsOracle leaffn vm eqth =
 let val (t1,t2) = dest_eq(concl(SPEC_ALL eqth))
 in
  EQ_MP (SYM eqth) (BddThmOracle(GenTermToTermBdd leaffn vm t2))
 end;

(*****************************************************************************)
(* Iterate a function                                                        *)
(*                                                                           *)
(*   f : int -> 'a -> 'a                                                     *)
(*                                                                           *)
(* from an initial value, applying it successively to 0,1,2,... until        *)
(*                                                                           *)
(*   p : 'a -> bool                                                          *)
(*                                                                           *)
(* is true (at least one iteration is always performed)                      *)
(*                                                                           *)
(*****************************************************************************)

fun iterate p f =
 let fun iter n x =
      let val x'  = f n x
      in
       if p x' then x' else iter (n+1) x'
      end
 in
  iter 0
 end;

(*****************************************************************************)
(*   |- f 0 s = ... s ...     |- !n. f (SUC n) s = ... f n ... s ...         *)
(*   ---------------------------------------------------------------         *)
(*       (vm ``f i s`` |--> bi, vm ``f (SUC i) s`` |--> bsuci)               *)
(*                                                                           *)
(* where i is the first number such that |- f (SUC i) s = f i s              *)
(* and the function                                                          *)
(*                                                                           *)
(*  report : int -> term_bdd -> 'a                                           *)
(*                                                                           *)
(* is applied to the iteration level and current term_bdd and can be used    *)
(* for tracing.                                                              *)
(*                                                                           *)
(* A state of the iteration is a pair (tb,tb') consisting of the             *)
(* previous term_bdd tb and the current one tb'. The initial state           *)
(* is (somewhat arbitarily) taken to be (tb0,tb0).                           *)
(*****************************************************************************)

exception computeFixedpointError;

fun computeFixedpoint report vm (th0,thsuc) =
 let val tb0 = eqToTermBdd (fn tm => raise computeFixedpointError) vm th0
     fun f n (tb,tb') =  
      let val tb'simp = BddApConv reduceLib.REDUCE_CONV tb'
          val _ = report n tb'simp
          val tb'' = 
           eqToTermBdd (BddApSubst tb'simp) vm (SPEC (intToTerm n) thsuc)
      in
       (tb'simp,tb'')
      end
 in
  iterate (uncurry BddEqualTest) f (tb0,tb0)
 end;

(*****************************************************************************)
(*              ass vm tm |--> b                                             *)
(*  ----------------------------------------------                           *)
(*  [((ass1 vm v1 |--> b1),(ass1' vm c1 |--> b1')),                          *)
(*                        .                                                  *)
(*                        .                                                  *)
(*                        .                                                  *)
(*   ((assi vm vi |--> bi),(assi' vm ci |--> bi')]                           *)
(*                                                                           *)
(* with the property that                                                    *)
(*                                                                           *)
(* BddRestrict [((ass1 vm v1 |--> b1),(ass1' vm c1 |--> b1')),               *)
(*                                   .                                       *)
(*                                   .                                       *)
(*                                   .                       ,               *)
(*              ((assi vm vi |--> bi),(assi' vm ci |--> bi'))]               *)
(*             (ass vm tm |--> b)                                            *)
(* =                                                                         *)
(* (ass1 U ass1' U ... U assi U assi' U ass)                                 *)
(* vm                                                                        *)
(* (subst[v1|->ci,...,vi|->ci]tm)                                            *)
(* |-->                                                                      *)
(* TRUE                                                                      *)
(*****************************************************************************)

exception BddSatoneError;

fun BddSatone tb =
 let val (_,_,vm,tm,b) = dest_term_bdd tb
     val assl        = bdd.getAssignment(bdd.satone b)
     val vml         = Varmap.dest vm
 in
  List.map 
   (fn (n,tv) => ((case assoc2 n vml of 
                      SOME(s,_) => BddVar true vm (mk_var(s,bool))
                    | NONE      => (print "this should not happen!\n";
                                    raise BddSatoneError)),
                  BddCon tv vm))
   assl
 end;

(*****************************************************************************)
(*                                                                           *)
(*         |- p s = ... s ...                                                *)
(*         |- f 0 s  = ... s ...                                             *)
(*         |- f (SUC n) s = ... f n ... s ...                                *)
(*  ---------------------------------------------------------                *)
(*  [{} vm ``f i s`` |--> bi,  ... , {} vm ``f 0 s`` |--> b0]                *)
(*                                                                           *)
(* where i is the first number such that |- f i s ==> p s                    *)
(*****************************************************************************)

exception computeTraceError;

fun computeTrace report vm pth (th0,thsuc) =
 let val ptb = eqToTermBdd (fn tm => raise computeFixedpointError) vm pth
     val tb0 = eqToTermBdd (fn tm => raise computeFixedpointError) vm th0
     fun p tbl = not(isFALSE(BddOp(bdd.And, hd tbl, ptb)))
     fun f n tbl =  
      (report n (hd tbl);
       let val tb =
        BddApConv
         reduceLib.REDUCE_CONV
         (eqToTermBdd (BddApSubst(hd tbl)) vm (SPEC (intToTerm n) thsuc))
       in
        tb :: tbl
       end)
 in
  if p[tb0] then [tb0] else iterate p f [tb0]
 end;


(* Test example (Solitaire)

val vm = solitaire_varmap;

val pth = SolitaireFinish_def;

val (th0,thsuc) = (in_th0,in_thsuc);

val trl = computeTrace report vm pth (th0,thsuc);

*)

(*****************************************************************************)
(* Given a list                                                              *)
(*                                                                           *)
(*  [((vm v1 |--> bj1),(vm c1 |--> b1')),                                    *)
(*                    .                                                      *)
(*                    .                                                      *)
(*                    .                ,                                     *)
(*   ((vm vn |--> bn),(vm cn |--> bn'))])                                    *)
(*                                                                           *)
(* in which not every vi is mapped to a constant, extend it                  *)
(* by mapping any unspecified variables to F. Used                           *)
(* to complete an assignment to generated by BddSatone                       *)
(*                                                                           *)
(*                                                                           *)
(*****************************************************************************)

fun extendSat varlist vm tbl =
 List.map
  (fn v => case List.find (fn (tb,tb') => getTerm tb = v) tbl of
              SOME tb_tb' => tb_tb'
            | NONE        => (BddVar true vm v, BddCon true vm))
  varlist;

(*****************************************************************************)
(*  traceBack                                                                *)
(*   vm                                                                      *)
(*   [{} vm ``f i s`` |--> bi,  ... , {} vm ``f 0 s`` |--> b0]               *)
(*   (|- p s = ... s ...)                                                    *)
(*   (|- R((v1,...,vn),(v1',...,vn')) = ...)                                 *)
(*                                                                           *)
(* computes a list of pairs of the form (with j = 0,1,...,i-1)               *)
(*                                                                           *)
(* ((vm ``ReachIn R B j s_vec /\ Prev R (Eq c_vec) s_vec`` |--> bdd),        *)
(*  [((vm v1 |--> bj1),(vm cj1 |--> bj1')),                                  *)
(*                   .                                                       *)
(*                   .                                                       *)
(*                   .                 ,                                     *)
(*   ((vm vn |--> bjn),(vm cjn |--> bjn'))])                                 *)
(*                                                                           *)
(*  where s_vec = (v1,...,vn) and c_vec = (c(j+1)1,...,c(i+1)n)              *)
(*                                                                           *)
(* where ci is T or F and the second element specifies a state satisfying    *)
(* the first element and in which state variable vj has value cj             *)
(* (where 0 <= j <= n).                                                      *)
(*                                                                           *)
(* The last element of the list has the form                                 *)
(* (({} vm ``ReachIn R B j s_vec /\ p(v1,...,vn)`` |--> bdd),                *)
(*  [(({} vm v1 |--> bi1),{} vm ci1 |--> bi1')),                             *)
(*                      .                                                    *)
(*                      .                                                    *)
(*                      .                   ,                                *)
(*   (({} vm vn |--> bin),({} vm cin |--> bin'))])                           *)
(*                                                                           *)
(* If [s0,...,si] is the sequence of states, then                            *)
(* R(s0,s1), R(s1,s2),...,R(s(i-1),si) and for j such that  1 <= j <= i      *)
(* sj satisfies bj and p si                                                  *)
(*****************************************************************************)

val traceBackPrevThm = ref TRUTH;

fun traceBack vm trl pth Rth =  
 let val svars = strip_pair(Term.rand(lhs(concl(SPEC_ALL pth))))
     val PrevTh = MkPrevThm Rth
     val _ = (traceBackPrevThm := PrevTh)
     val vl = filter (fn v => type_of v = bool) (all_vars(concl PrevTh)) @ svars
     val prime_var = mk_var o (prime ## I) o dest_var
     val vm' = extendVarmap (vl @ List.map prime_var vl) vm
     val trl' = map (BddExtendVarmap vm') trl
     val ptb = eqToTermBdd (fn tm => raise computeFixedpointError) vm' pth
     val PrevThTb = eqToTermBdd failfn vm' PrevTh
     val lasttb = BddOp(And, hd trl', ptb)
     val prime_ass = List.map (fn (tb,tb') => (BddVar true vm' (prime_var(getTerm tb)), tb'))
     fun satfn tb = extendSat svars vm' (BddSatone tb)
     fun stepback(tb, ass) =
      let val tb' = BddOp(And, tb, BddRestrict (prime_ass ass) PrevThTb)
      in
       (tb', satfn tb')
      end
     val _ = print "Computing trace: "
     val assl =
      List.foldl
       (fn (tb,assl) => (print "."; stepback(tb, snd(hd assl)) :: assl))
       [(lasttb, satfn lasttb)]
       (tl trl')
     val _ = print " done.\n"
in
 assl
end;

(*****************************************************************************)
(*  findTrace                                                                *)
(*   (|- R((v1,...,vn),(v1',...,vn')) = ...)                                 *)
(*   (|- P(v1,...,vn) = ...)                                                 *)
(*   (|- Q(v1,...,vn) = ...)                                                 *)
(*  =                                                                        *)
(*   ((|- P s_0), [(|- R(s_0,s_1)),...,(|- R(s_(n-1),s_n))], (|- Q s_n))     *)
(*****************************************************************************)

fun findTrace vm Rth Pth Qth =
 let val (in_th0,in_thsuc) = 
      (REWRITE_RULE[Pth,pairTheory.PAIR_EQ] ## REWRITE_RULE[Rth])
      (MkIterThms 
        MachineTransitionTheory.ReachIn_rec 
        (lhs(concl(SPEC_ALL Rth)))
        (lhs(concl(SPEC_ALL Pth))))
     val (Rcon, s_s') = Term.dest_comb(lhs(concl(SPEC_ALL Rth)))
     val (s,s') = pairSyntax.dest_pair s_s'
     val tr = computeTrace (fn n=>fn tb=>print".") vm Qth (in_th0,in_thsuc)
     val soln = traceBack vm tr Qth Rth
     val cl = 
      List.map 
       (fn(_,tbl)=> list_mk_pair(List.map (fn(_,tb)=> getTerm tb) tbl))
       soln
     val initth = BddRhsOracle 
                   failfn 
                   vm 
                   (SPECL (strip_pair(hd cl)) (GENL(strip_pair s)(SPEC_ALL Pth)))
     val transthl = 
      map 
       (fn (t,t') =>
         BddRhsOracle 
           failfn 
           vm 
           (SPECL 
             (strip_pair t @ strip_pair t') 
             (GENL(strip_pair s @ strip_pair s')(SPEC_ALL Rth))))
       (zip (List.take(cl, length cl - 1)) (tl cl))
     val finalth = BddRhsOracle failfn 
                    vm 
                    (SPECL (strip_pair(last cl)) 
                    (GENL(strip_pair s)(SPEC_ALL Qth)))
 in
  (initth, transthl, finalth)
 end;


(*****************************************************************************)
(* If t is satifiable (i.e. b is not FALSE)                                  *)
(*                                                                           *)
(*            a vm t |--> b                                                  *)
(*      --------------------------                                           *)
(*      a U {v1=c1,...,vn=cn} |- t                                           *)
(*                                                                           *)
(* Similar to BddFindModel followed by BddThmOracle, but checks the          *)
(* assignment found by satone using CBV_CONV, so is pure                     *)
(* (i.e. result not tagged with HolBdd)                                      *)
(*                                                                           *)
(*****************************************************************************)

exception findModelError;

local
open computeLib
val compset = bool_compset()
in
fun findModel tb = 
 let val (_,ass,vm,t,b) = dest_term_bdd tb
     val assl         = bdd.getAssignment(bdd.satone b)
     val vml          = Varmap.dest vm
     val setl         = List.map 
                         (fn (n,tv) => 
                           ((case assoc2 n vml of 
                                SOME(s,_) => mk_var(s,bool)
                              | NONE      => (print "This should not happen!\n";
                                              raise findModelError)),
                            if tv then T else F))
                        assl
 in
  EQT_ELIM
   (RIGHT_CONV_RULE 
     (CBV_CONV compset)
     (SUBST_CONV (List.map (fn(l,r) => (l |-> ASSUME(mk_eq(l,r)))) setl) t t))
 end
end;

(* 
end;
*)

end
