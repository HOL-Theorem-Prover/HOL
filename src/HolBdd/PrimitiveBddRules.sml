
(*****************************************************************************)
(* PrimitiveBddRules.sml                                                     *)
(* ---------------------                                                     *)
(*                                                                           *)
(* Types and rules implementing primitive axioms and rules                   *)
(* of inference system for BDD representation judgements.                    *)
(*                                                                           *)
(*****************************************************************************)
(*                                                                           *)
(* BddThmOracle                                                              *)
(* BddExtendVarmap                                                           *)
(* BddSupportContractVarmap                                                  *)
(* BddFreevarsContractVarmap                                                 *)
(* BddEqMp                                                                   *)
(* BddReplace                                                                *)
(* BddCompose                                                                *)
(* BddListCompose                                                            *)
(* BddRestrict                                                               *)
(* BddT                                                                      *)
(* BddF                                                                      *)
(* BddVar                                                                    *)
(* BddNot                                                                    *)
(* BddOp                                                                     *)
(* BddIte                                                                    *)
(* BddForall                                                                 *)
(* BddExists                                                                 *)
(* BddAppall                                                                 *)
(* BddAppex                                                                  *)
(*                                                                           *)
(*****************************************************************************)
(*                                                                           *)
(* Revision history:                                                         *)
(*                                                                           *)
(*   Tue Oct  2 15:03:11 BST 2001 -- created file                            *)
(*   Fri Oct  5 17:23:09 BST 2001 -- revised file                            *)
(*                                                                           *)
(*****************************************************************************)

(*
load "bdd";
load "pairLib";
load "Pair_basic";
load "numLib";
load "Binarymap";
load "Varmap";

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();
*)

local

open pairSyntax;
open pairTools;
open Pair_basic;
open numLib;
open Binarymap;
open Varmap;
open bdd;

open HolKernel Parse boolLib BasicProvers

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

in

(*****************************************************************************)
(* The constructor TermBdd is like mk_thm and is only used                   *)
(* to create primitive term_bdd values.                                      *)
(*                                                                           *)
(* TermBdd should not be exported from this module.                          *)
(*****************************************************************************)

(*
local
*)

datatype term_bdd = TermBdd of varmap * term * bdd.bdd;

(*
in
*)

(*****************************************************************************)
(* Destructors for term_bdd                                                  *)
(*****************************************************************************)

fun dest_term_bdd(TermBdd(vm,tm,b)) = (vm,tm,b);

fun getVarmap(TermBdd(vm,tm,b)) = vm
and getTerm(TermBdd(vm,tm,b))   = tm
and getBdd(TermBdd(vm,tm,b))    = b;

(*****************************************************************************)
(* Name of a boolean variable (raises nameError on non boolean variables)    *)
(*****************************************************************************)

exception nameError;

fun name v = 
 if is_var v andalso type_of v = bool
  then fst(dest_var v)
  else (print_term v; print "is not a boolean variable\n"; raise nameError);

(*****************************************************************************)
(* Oracle function                                                           *)
(*                                                                           *)
(*    vm t |--> TRUE                                                         *)
(*    --------------                                                         *)
(*         |- t                                                              *)
(*****************************************************************************)

val HolBddTag = Tag.read "HolBdd";

exception BddThmOracleError;

fun BddThmOracle(TermBdd(_,tm,bdd)) =
 if bdd.equal bdd bdd.TRUE 
  then mk_oracle_thm HolBddTag ([],tm) 
  else raise BddThmOracleError;

(*****************************************************************************)
(*   vm1 tm |--> b   Varmap.extends vm1 vm2                                  *)
(*   --------------------------------------                                  *)
(*             vm2 tm |--> b                                                 *)
(*****************************************************************************)

exception BddExtendVarmapError;

fun BddExtendVarmap (TermBdd(vm1,tm,b)) vm2 =
 if Varmap.extends vm1 vm2 
  then TermBdd(vm2,tm,b) 
  else raise BddExtendVarmapError;

(*****************************************************************************)
(* Test if a BDD variable is in the support of a bdd                         *)
(*****************************************************************************)

fun inSupport n b =
 Vector.foldl
  (fn (m,bv) => (m=n) orelse bv)
  false
  (bdd.scanset(bdd.support b));

(*****************************************************************************)
(*   vm tm |--> b   Varmap.peek vm (name v) = SOME n   not(inSupport n b)    *)
(*   --------------------------------------------------------------------    *)
(*                      Varmap.remove(name v)vm |--> b                       *)
(*                                                                           *)
(* Raises BddContractVarmapError if vm maps v to a BDD variable in b,        *)
(* and is the idenetity of v is not mapped to anything by vm                 *)
(*                                                                           *)
(*****************************************************************************)

exception BddSupportContractVarmapError;

fun BddSupportContractVarmap v (tb as (TermBdd(vm,tm,b))) =
 let val s = name v
 in
   case Varmap.peek vm s of
      SOME n => if inSupport n b 
                 then raise BddSupportContractVarmapError
                 else TermBdd(Varmap.remove s vm, tm, b)
    | NONE   => tb
 end;


(*****************************************************************************)
(*   |- t1 = t2   vm t1 |--> b                                               *)
(*   --------------------------                                              *)
(*          vm t2 |--> b                                                     *)
(*****************************************************************************)

exception BddEqMpError;

fun BddEqMp th (TermBdd(vm,t1,b)) =
 let val (a,c) = dest_thm th
     val (l,r) = dest_eq c
 in
  if not((a=[]) andalso (aconv l t1)) 
   then raise BddEqMpError 
   else TermBdd(vm,r,b)
 end;

(*****************************************************************************)
(*                    [(vm v1 |--> b1 , vm v1' |--> b1'),                    *)
(*                                    .                                      *)
(*                                    .                                      *)
(*                                    .                                      *)
(*                     (vm vi |--> bi , vm vi' |--> bi')]                    *)
(*                    vm tm |--> b                                           *)
(*  ------------------------------------------------------------------------ *)
(*   vm (subst[v1 |-> v1', ... , vi |-> vi']tm)                              *)
(*   |-->                                                                    *)
(*   replace b (makepairSet(map (var ## var) [(b1,b1'), ... , (bi,bi')]))    *)
(*****************************************************************************)

exception BddReplaceError;

fun BddReplace tbl (TermBdd(vm,tm,b)) =
 let val (_,(l,l'),replacel) = 
       List.foldr
        (fn(((TermBdd(vm,tm,b)),(TermBdd(vm',tm',b'))), (vm_,(l,l'),replacel))
           =>
           if not(Varmap.eq(vm_,vm) andalso Varmap.eq(vm,vm'))
            then (                print "unequal varmaps\n";       raise BddReplaceError) else
           if not(is_var tm)
            then (print_term tm ; print " should be a variable\n"; raise BddReplaceError) else
           if not(is_var tm')
            then (print_term tm'; print " should be a variable\n"; raise BddReplaceError) else
           if mem tm l
            then (print_term tm ; print" repeated\n";              raise BddReplaceError) else
           if mem tm' l'
            then (print_term tm'; print" repeated\n";              raise BddReplaceError) 
            else (vm', 
                  (tm :: l, tm' :: l'),
                  ((bdd.var b, bdd.var b')::replacel)))
        (vm, ([],[]), [])
        tbl
 in
  TermBdd(vm, 
          subst (ListPair.map (fn(v,v')=>(v|->v')) (l,l')) tm, 
          bdd.replace b (bdd.makepairSet replacel))
 end;

(* Test examples ==================================================================

val tb1 = termToTermBdd ``x /\ y /\ z``;

val tbx = termToTermBdd ``x:bool``
and tby = termToTermBdd ``y:bool``
and tbz = termToTermBdd ``z:bool``
and tbp = termToTermBdd ``p:bool``
and tbq = termToTermBdd ``q:bool``;

(* Repeat to sync all the varmaps! *)

val tb = tb1 and tbl = [(tbx,tbp),(tby,tbq)];
val tb = BddReplace tbl tb;

val tb = tb1 and tbl = [(tbx,tby),(tby,tbz),(tbz,tbx)];
val tb = BddReplace tbl tb;

val tb = tb1 and tbl = [(tbx,tby),(tby,tbz)];
val tb = BddReplace tbl tb;
(* ! Fail  "Trying to replace with variables already in the bdd" *)

val tb = tb1 and tbl = [(tbx,tby),(tby,tbx)];
val tb = BddReplace tbl tb;

val tb = tb1 and tbl = [(tbx,tbp),(tby,tbp)];
val tb4 = BddReplace tbl tb;
(* p repeated *)

======================================================= End of test examples *)

(*****************************************************************************)
(*    (vm v |--> b, vm tm1 |--> b1)    vm tm2 |--> b2                        *)
(*  ------------------------------------------------------                   *)
(*  vm (subst [v |-> tm1] tm2) |--> compose (var b, b1) b2                   *)
(*****************************************************************************)

exception BddComposeError;

fun BddCompose (TermBdd(vm,v,b), TermBdd(vm1,tm1,b1)) (TermBdd(vm2,tm2,b2)) =
 if Varmap.eq(vm,vm1) andalso Varmap.eq(vm1,vm2)
  then TermBdd(vm, subst[v |-> tm1]tm2, compose (var b, b1) b2)
  else (print "different varmaps\n"; raise BddComposeError);

(*****************************************************************************)
(*                    [(vm v1 |--> b1 , vm v1' |--> b1'),                    *)
(*                                    .                                      *)
(*                                    .                                      *)
(*                                    .                                      *)
(*                     (vm vi |--> bi , vm vi' |--> bi')]                    *)
(*                    vm tm |--> b                                           *)
(*  ------------------------------------------------------------------------ *)
(*   vm (subst[v1 |-> v1', ... , vi |-> vi']tm)                              *)
(*   |-->                                                                    *)
(*   veccompose (composeSet (map (var ## I) [(b1,b1'), ... , (bi,bi')])) b   *)
(*****************************************************************************)

exception BddListComposeError;

fun BddListCompose tbl (TermBdd(vm,tm,b)) =
 let val (_,(l,l'),composel) = 
       List.foldr
        (fn(((TermBdd(vm,tm,b)),(TermBdd(vm',tm',b'))), (vm_,(l,l'),composel))
           =>
           if not(Varmap.eq(vm_,vm) andalso Varmap.eq(vm,vm'))
            then (                print "unequal varmaps\n";
                                  raise BddListComposeError) else
           if not(is_var tm)
            then (print_term tm ; print " should be a variable\n";
                                  raise BddListComposeError) else
           if mem tm l
            then (print_term tm ; print" repeated\n";
                                  raise BddListComposeError) 
            else (vm', 
                  (tm :: l, tm' :: l'),
                  ((bdd.var b, b')::composel)))
        (vm, ([],[]), [])
        tbl
 in
  TermBdd(vm, 
          subst (ListPair.map (fn(v,v')=>(v|->v')) (l,l')) tm, 
          bdd.veccompose (bdd.composeSet composel) b)
 end;


(* Test examples ==================================================================

val tb1 = termToTermBdd ``x /\ y /\ z``;

val tbx = termToTermBdd ``x:bool``
and tby = termToTermBdd ``y:bool``
and tbz = termToTermBdd ``z:bool``
and tbp = termToTermBdd ``p:bool``
and tbq = termToTermBdd ``q:bool``;

(* Repeat to sync all the varmaps! *)

val tb = tb1 and tbl = [(tbx,tbp),(tby,tbq)];
val tb = BddListCompose tbl tb;

val tb = tb1 and tbl = [(tbx,tby),(tby,tbz),(tbz,tbx)];
val tb = BddListCompose tbl tb;

val tb = tb1 and tbl = [(tbx,tby),(tby,tbz)];
val tb = BddListCompose tbl tb;
(* ! Fail  "Trying to replace with variables already in the bdd" *)

val tb = tb1 and tbl = [(tbx,tby),(tby,tbx)];
val tb = BddListCompose tbl tb;

val tb = tb1 and tbl = [(tbx,tbp),(tby,tbp)];
val tb4 = BddListCompose tbl tb;
(* p repeated *)

======================================================= End of test examples *)


(*****************************************************************************)
(* BddRestrict [((vm v1 |--> b1),c1),...,(vm vi |--> bi),ci)] (vm tm |--> b) *)
(* (where c1,...,ci are T or F)                                              *)
(*                                                                           *)
(*       vm v1 |--> b1   ...   vm vi |-> bi    vm tm |--> b                  *)
(*  --------------------------------------------------------------------     *)
(*  vm (subst[v1|->ci,...,vi|->ci]tm)                                        *)
(*  |-->                                                                     *)
(*  restrict b (assignment[(var b1,mlval c1),...,(var i, mlval ci)]          *)
(*****************************************************************************)

exception BddRestrictError;

local

fun mlval tm =
 if tm=T 
  then true 
  else if tm=F then false else raise BddRestrictError

in

fun BddRestrict tbcl tb =
 let val TermBdd(vm,tm,b) = tb
     val (vml,substl,restrictl) = 
       List.foldr
        (fn(((TermBdd(vm,tm,b)),c), (vml,substl,restrictl))
           =>
           if not(Varmap.eq(hd vml,vm))
            then (print "unequal varmaps\n"; raise BddRestrictError) 
            else ((vm::vml), 
                  ((tm |-> c)::substl), 
                  ((bdd.var b, mlval c)::restrictl)))
        ([vm],[],[])
        tbcl
 in
  TermBdd(vm, subst substl tm, bdd.restrict b (bdd.assignment restrictl))
 end

end;

(*****************************************************************************)
(*   vm tm |--> b   not(mem (name v) (free_vars tm))                         *)
(*   -----------------------------------------------                         *)
(*           Varmap.remove(name v)vm |--> b                                  *)
(*                                                                           *)
(* Raises BddFreevarsContractVarmapError if v is free in tm,                 *)
(* and is the identity otherwise                                             *)
(*****************************************************************************)

exception BddFreevarsContractVarmapError;

fun BddFreevarsContractVarmap v (TermBdd(vm,tm,b)) =
 if mem v (free_vars tm)
  then (print_term v; print " not in free_vars of\n"; print_term tm; print "\n";
        raise BddFreevarsContractVarmapError)
  else TermBdd(Varmap.remove (name v) vm, tm, b);

(*****************************************************************************)
(* Rules for T and F                                                         *)
(*****************************************************************************)

fun BddT vm = TermBdd(vm,T,TRUE)
and BddF vm = TermBdd(vm,F,FALSE);

(*****************************************************************************)
(*                                                                           *)    
(*     Varmap.peek vm (name v) = SOME n                                      *)
(*    ---------------------------------   BddVar true                        *)
(*           vm v |--> ithvar n                                              *)
(*                                                                           *)
(*     Varmap.peek vm (name v) = SOME n                                      *)
(*    ---------------------------------   BddVar false                       *)
(*           vm v |--> nithvar n                                             *)
(*                                                                           *)
(*****************************************************************************)

exception BddVarError;

fun BddVar tv vm v =
 case Varmap.peek vm (name v) of
    SOME n => if tv 
               then TermBdd(vm, v,        bdd.ithvar n)
               else TermBdd(vm, mk_neg v, bdd.nithvar n)
  | NONE   => (print_term v; print " not in varmap\n"; raise BddVarError);

(*****************************************************************************)
(*   vm  t |--> b                                                            *)
(*   ----------------                                                        *)
(*   vm ~t |--> NOT b                                                        *)
(*****************************************************************************)

fun BddNot(TermBdd(vm,t,b)) =  TermBdd(vm, mk_neg t, NOT b);

(*****************************************************************************)
(* Auxiliary function to perform on two terms the operation corresponding    *)
(* to a bddop                                                                *)
(*****************************************************************************)

fun termApply t1 t2 bddop =
 case bddop of
    And    => mk_conj(t1,t2)         
  | Biimp  => mk_eq(t1,t2)           
  | Diff   => mk_conj(t1, mk_neg t2) 
  | Imp    => mk_imp(t1,t2)          
  | Invimp => mk_imp(t2,t1)          
  | Lessth => mk_conj(mk_neg t1, t2) 
  | Nand   => mk_neg(mk_conj(t1,t2)) 
  | Nor    => mk_neg(mk_disj(t1,t2)) 
  | Or     => mk_disj(t1,t2)         
  | Xor    => mk_neg(mk_eq(t1,t2)); 

(*****************************************************************************)
(*    vm t1 |--> b1     vm t2 |--> b2                                        *)
(*  -----------------------------------                                      *)
(*  vm (t1 <bddop> t2) |--> b1 bddop b2                                      *)
(*                                                                           *)
(* where <bddop> is an operation of terms corresponding to the BDD           *)
(* binary operatiobn bddop (N.B. can't use "op" as it's an SML keyword)      *)
(*****************************************************************************)

exception BddOpError;

fun BddOp (bddop, TermBdd(vm1,t1,b1), TermBdd(vm2,t2,b2)) =
if Varmap.eq(vm1,vm2)
 then TermBdd(vm1, termApply t1 t2 bddop, bdd.apply b1 b2 bddop)
 else (print "different varmaps\n"; raise BddOpError);

(*****************************************************************************)
(*  vm t |--> b   vm t1 |--> b1   vm t2 |--> b2                              *)
(*  -------------------------------------------                              *)
(*  vm (if t then t1 else t2) |--> ITE b b1 b2                               *)
(*****************************************************************************)

exception BddIteError;

fun BddIte(TermBdd(vm,t,b), TermBdd(vm1,t1,b1), TermBdd(vm2,t2,b2)) = 
 if Varmap.eq(vm,vm1) andalso Varmap.eq(vm1,vm2)
  then TermBdd(vm, mk_cond(t,t1,t2), ITE b b1 b2)
  else (print "different varmaps\n"; raise BddIteError);

(*****************************************************************************)
(*                   vm t |--> b                                             *)
(* ---------------------------------------------------                       *)
(* vm (!v1...vi. t) |--> forall (makeset[n1,...,ni]) b                       *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers and     *)
(* vm is assumed to contain v1,...,vi                                        *)
(*****************************************************************************)

exception BddForallError;

fun BddForall vl (TermBdd(vm,t,b)) =
 let val bddvars = 
       List.map 
        (fn v => case Varmap.peek vm (name v) of
                    SOME n => n
                  | NONE   => raise BddForallError) 
        vl
 in
  TermBdd(vm, list_mk_forall(vl,t), bdd.forall (bdd.makeset bddvars) b)
 end;

(*****************************************************************************)
(*                   vm t |--> b                                             *)
(* --------------------------------------------------                        *)
(* vm (?v1...vi. t) |--> exist (makeset[n1,...,ni]) b                        *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers and     *)
(* vm is assumed to contain v1,...,vi                                        *)
(*****************************************************************************)

exception BddExistsError;

fun BddExists vl (TermBdd(vm,t,b)) =
 let val bddvars = 
       List.map 
        (fn v => case Varmap.peek vm (name v) of
                    SOME n => n
                  | NONE   => raise BddExistsError) 
        vl
 in
  TermBdd(vm, list_mk_exists(vl,t), bdd.exist (bdd.makeset bddvars) b)
 end;

(*****************************************************************************)
(*                   vm t1 |--> b1    vm t2 |--> b2                          *)
(* ------------------------------------------------------------------------- *)
(* vm (!v1...vi. t1 <bddop> t2) |--> appall b1 b2 bddop (makeset[n1,...,ni]) *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers and     *)
(* vm is assumed to contain v1,...,vi                                        *)
(*****************************************************************************)

exception BddAppallError;

fun BddAppall vl (bddop, TermBdd(vm1,t1,b1), TermBdd(vm2,t2,b2)) =
 if Varmap.eq(vm1,vm2)
  then
   TermBdd
    (vm1, 
     list_mk_forall(vl, termApply t1 t2 bddop), 
     bdd.appall 
      b1 
      b2 
      bddop 
      (bdd.makeset
        (List.map (fn v => case Varmap.peek vm1 (name v) of
                              SOME n => n
                            | NONE   => raise BddAppallError) 
        vl)))
  else (print "different varmaps\n"; raise BddAppallError);

(*****************************************************************************)
(*                   vm t1 |--> b1    vm t2 |--> b2                          *)
(* ------------------------------------------------------------------------- *)
(* vm (?v1...vi. t1 <bddop> t2) |--> appall b1 b2 bddop (makeset[n1,...,ni]) *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers and     *)
(* vm is assumed to contain v1,...,vi                                        *)
(*****************************************************************************)

exception BddAppexError;

fun BddAppex vl (bddop, TermBdd(vm1,t1,b1), TermBdd(vm2,t2,b2)) =
 if Varmap.eq(vm1,vm2)
  then
   TermBdd
    (vm1, 
     list_mk_exists(vl, termApply t1 t2 bddop), 
     appex
      b1 
      b2 
      bddop 
      (bdd.makeset
        (List.map (fn v => case Varmap.peek vm1 (name v) of
                              SOME n => n
                            | NONE   => raise BddAppallError) 
        vl)))
  else (print "different varmaps\n"; raise BddAppallError);

end;

(*
end;
*)
