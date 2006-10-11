
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
(* BddCon                                                                    *)
(* BddVar                                                                    *)
(* BddNot                                                                    *)
(* BddOp                                                                     *)
(* BddIte                                                                    *)
(* BddForall                                                                 *)
(* BddExists                                                                 *)
(* BddAppall                                                                 *)
(* BddAppex                                                                  *)
(* BddSimplify                                                               *)
(* BddFindModel                                                              *)
(*                                                                           *)
(*****************************************************************************)
(*                                                                           *)
(* Revision history:                                                         *)
(*                                                                           *)
(*   Tue Oct  2 15:03:11 BST 2001 -- created file                            *)
(*   Fri Oct  5 17:23:09 BST 2001 -- revised file                            *)
(*   Thu Nov  1 14:18:41 GMT 2001 -- added assumptions to term_bdd values    *)
(*   Mon Mar 11 11:01:53 GMT 2002 -- added BddFindModel                      *)
(*   Thu Mar 28 09:40:05 GMT 2002 -- added signature file                    *)
(*                                                                           *)
(*****************************************************************************)

structure PrimitiveBddRules :> PrimitiveBddRules = struct

(*
load "bdd";
load "pairLib";
load "PairRules";
load "numLib";
load "Binarymap";
load "Varmap";

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();
*)

local

open pairSyntax;
open pairTools;
open PairRules;
open numLib;
open Binarymap;
open Varmap;
open bdd;

open HolKernel Parse boolLib BasicProvers Tag Feedback

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

(*****************************************************************************)
(* Ken Larsen writes:                                                        *)
(* In the current mosml release List.foldl is tail recursive but             *)
(* List.foldr isn't.  In the upcomming mosml release foldr might be tail     *)
(* recursive.  But a tail recursive version of foldr is easy to uptain       *)
(* (as Michael notes):                                                       *)
(*****************************************************************************)

fun foldr f start ls = List.foldl f start (rev ls);

(*****************************************************************************)
(* To enable HolBdd to track tags. HolBddTag:TermBdd :: empty_tag:THM        *)
(*****************************************************************************)

val HolBddTag_string = "HolBdd"
val HolBddTag = Tag.read HolBddTag_string

(*****************************************************************************)
(* Setup trace variable for controlling debug output                         *)
(*****************************************************************************)

val trace_level = ref 0

val _ = register_trace("HolBdd",trace_level,5)

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

type assums = term HOLset.set;
type varmap = Varmap.varmap;
datatype term_bdd = TermBdd of tag * assums * varmap * term * bdd.bdd;

(*
in
*)

(*****************************************************************************)
(* Destructors for term_bdd                                                  *)
(*****************************************************************************)

fun dest_term_bdd(TermBdd(tg,ass,vm,tm,b)) = (tg,ass,vm,tm,b);

fun getTag(TermBdd(tg,ass,vm,tm,b)) = tg
and getAssums(TermBdd(tg,ass,vm,tm,b)) = ass
and getVarmap(TermBdd(tg,ass,vm,tm,b)) = vm
and getTerm(TermBdd(tg,ass,vm,tm,b))   = tm
and getBdd(TermBdd(tg,ass,vm,tm,b))    = b;

(*****************************************************************************)
(* Name of a boolean variable (raises nameError on non boolean variables)    *)
(*****************************************************************************)

exception nameError;

fun name v =
 if is_var v andalso type_of v = bool
  then fst(dest_var v)
  else (print_term v; print " is not a boolean variable\n"; raise nameError);

(*****************************************************************************)
(* Oracle function                                                           *)
(*                                                                           *)
(*   ass vm t |--> TRUE                                                      *)
(*   ------------------                                                      *)
(*       ass |- t                                                            *)
(*****************************************************************************)

exception BddThmOracleError;

fun BddThmOracle(TermBdd(tg,ass,_,tm,bdd)) =
 if bdd.equal bdd bdd.TRUE
  then add_tag(tg, mk_oracle_thm HolBddTag_string (HOLset.listItems ass, tm))
  else raise BddThmOracleError;

(*****************************************************************************)
(*   Varmap.extends vm1 vm2   ass vm1 tm |--> b                              *)
(*   ------------------------------------------                              *)
(*             ass vm2 tm |--> b                                             *)
(*****************************************************************************)

exception BddExtendVarmapError;

fun BddExtendVarmap vm2 (TermBdd(tg,ass,vm1,tm,b)) =
 if Varmap.extends vm1 vm2
  then TermBdd(tg,ass,vm2,tm,b)
  else raise BddExtendVarmapError;

(*****************************************************************************)
(*   ass vm tm |--> b   not(mem (name v) (free_vars tm))                     *)
(*   ---------------------------------------------------                     *)
(*         ass Varmap.remove(name v)vm |--> b                                *)
(*                                                                           *)
(* Raises BddFreevarsContractVarmapError if v is free in tm,                 *)
(* and is the identity otherwise                                             *)
(*****************************************************************************)

exception BddFreevarsContractVarmapError;

fun BddFreevarsContractVarmap v (TermBdd(tg,ass,vm,tm,b)) =
 if mem v (free_vars tm)
  then (print_term v; print " not in free_vars of\n"; print_term tm; print "\n";
        raise BddFreevarsContractVarmapError)
  else TermBdd(tg,ass,Varmap.remove (name v) vm, tm, b);

(*****************************************************************************)
(* Test if a BDD variable is in the support of a bdd                         *)
(*****************************************************************************)

fun inSupport n b =
 Vector.foldl
  (fn (m,bv) => (m=n) orelse bv)
  false
  (bdd.scanset(bdd.support b));

(*****************************************************************************)
(*  ass vm tm |--> b   Varmap.peek vm (name v) = SOME n   not(inSupport n b) *)
(*  ------------------------------------------------------------------------ *)
(*               ass (Varmap.remove(name v)vm) tm |--> b                     *)
(*                                                                           *)
(* Raises BddSupportContractVarmapError if vm maps v to a BDD variable in b, *)
(* and is the idenetity of v is not mapped to anything by vm                 *)
(*                                                                           *)
(*****************************************************************************)

exception BddSupportContractVarmapError;

fun BddSupportContractVarmap v (tb as (TermBdd(tg,ass,vm,tm,b))) =
 let val s = name v
 in
   case Varmap.peek vm s of
      SOME n => if inSupport n b
                 then raise BddSupportContractVarmapError
                 else TermBdd(tg,ass,Varmap.remove s vm, tm, b)
    | NONE   => tb
 end;

(*****************************************************************************)
(*  asl |- t1 = t2   ass vm t1 |--> b                                        *)
(*  ---------------------------------                                        *)
(*   (addList ass asl) vm t2 |--> b                                          *)
(*****************************************************************************)

exception BddEqMpError;

fun BddEqMp th (TermBdd(tg,ass,vm,t1,b)) =
 let val (asl,c) = dest_thm th
     val (l,r)   = dest_eq c
 in
   if aconv l t1
    then TermBdd(Tag.merge tg (Thm.tag th),HOLset.addList(ass,asl),vm,r,b)
   else if (!trace_level)>=1 then
       let val _ = print "BddEqMp Error\n"
	   val _ = print "Theorem:\n"
	   val _ = print_thm th
	   val _ = print "\n"
	   val _ = print "Term:\n"
	   val _ = print_term t1
	   val _ = print "\n"
       in raise BddEqMpError end
	else raise BddEqMpError
 end;

(*****************************************************************************)
(*         [(ass1 vm v1 |--> b1  , ass1' vm v1' |--> b1'),                   *)
(*                               .                                           *)
(*                               .                                           *)
(*                               .                                           *)
(*           (assi vm vi |--> bi , assi' vm vi' |--> bi')]                   *)
(*           ass vm tm |--> b                                                *)
(*  ------------------------------------------------------------------------ *)
(*   (ass1 U ass1' ... assi U assi' U ass)                                   *)
(*   vm                                                                      *)
(*   (subst[v1 |-> v1', ... , vi |-> vi']tm)                                 *)
(*   |-->                                                                    *)
(*   replace b (makepairSet[(var b1, var b1'), ... , (var bi, var bi')])     *)
(*****************************************************************************)

exception BddReplaceError;

fun BddReplace tbl (TermBdd(tg,ass,vm,tm,b)) =
 let val (tg',ass_union,(l,l'),replacel) =
       foldr
        (fn(((TermBdd(tg1,ass1,vm1,v,b)), (TermBdd(tg2,ass2,vm2,v',b'))),
            (tg,ass, (l,l'), replacel))
           =>
           if not(Varmap.eq(vm,vm1) andalso Varmap.eq(vm,vm2))
            then (                print "unequal varmaps\n";
                                  raise BddReplaceError) else
           if not(is_var v)
            then (print_term v  ; print " should be a variable\n";
                                  raise BddReplaceError) else
           if not(is_var v')
            then (print_term v' ; print " should be a variable\n";
                                  raise BddReplaceError) else
           if mem v l
            then (print_term v  ; print" repeated\n";
                                  raise BddReplaceError) else
           if mem v' l'
            then (print_term v' ; print" repeated\n";
                                  raise BddReplaceError)
            else (Tag.merge tg (Tag.merge tg1 tg2),
		  HOLset.union(ass,HOLset.union(ass1,ass2)),
                  (v :: l, v' :: l'),
                  ((bdd.var b, bdd.var b')::replacel)))
        (tg,ass, ([],[]), [])
        tbl
 in
  TermBdd(tg',
	  ass_union,
          vm,
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
(*  (ass vm v |--> b, ass1 vm tm1 |--> b1)    ass2 vm tm2 |--> b2            *)
(*  -------------------------------------------------------------            *)
(*  (ass U ass1 U ass2) vm                                                   *)
(*  (subst [v |-> tm1] tm2) |--> compose (var b, b1) b2                      *)
(*****************************************************************************)

exception BddComposeError;

fun BddCompose
     (TermBdd(tg,ass,vm,v,b), TermBdd(tg1,ass1,vm1,tm1,b1))
     (TermBdd(tg2,ass2,vm2,tm2,b2)) =
 if is_var v andalso Varmap.eq(vm,vm1) andalso Varmap.eq(vm1,vm2)
  then TermBdd(Tag.merge tg (Tag.merge tg1 tg2),
	       HOLset.union(ass,HOLset.union(ass1,ass2)),
               vm,
               subst[v |-> tm1]tm2,
               bdd.compose (bdd.var b, b1) b2)
  else (print "different varmaps\n"; raise BddComposeError);

(*****************************************************************************)
(*         [(ass1 vm v1 |--> b1  , ass1' vm tm1 |--> b1'),                   *)
(*                               .                                           *)
(*                               .                                           *)
(*                               .                                           *)
(*           (assi vm vi |--> bi , assi' vm tmi |--> bi')]                   *)
(*           ass vm tm |--> b                                                *)
(*  ------------------------------------------------------------------------ *)
(*   (ass1 U ass1' ... assi U assi' U ass)                                   *)
(*   vm                                                                      *)
(*   (subst[v1 |-> tm1, ... , vi |-> tmi]tm)                                 *)
(*   |-->                                                                    *)
(*   veccompose (composeSet (map (var ## I) [(b1,b1'), ... , (bi,bi')])) b   *)
(*****************************************************************************)

exception BddListComposeError;

fun BddListCompose tbl (TermBdd(tg,ass,vm,tm,b)) =
 let val (tg_merge,ass_union, (l,l') ,composel) =
       foldr
        (fn(((TermBdd(tg1,ass1,vm1,v,b)),(TermBdd(tg2,ass2,vm2,tm,b'))),
            (tg,ass, (l,l'), composel))
           =>
           if not(Varmap.eq(vm,vm1) andalso Varmap.eq(vm,vm2))
            then (                print "unequal varmaps\n";
                                  raise BddListComposeError) else
           if not(is_var v)
            then (print_term v  ; print " should be a variable\n";
                                  raise BddListComposeError) else
           if mem v l
            then (print_term v  ; print" repeated\n";
                                  raise BddListComposeError)
            else (Tag.merge tg (Tag.merge tg1 tg2),
		  HOLset.union(ass,HOLset.union(ass1,ass2)),
                  (v :: l, tm :: l'),
                  ((bdd.var b, b')::composel)))
        (tg,ass, ([],[]), [])
        tbl
 in
  TermBdd(tg_merge,
	  ass_union,
          vm,
          subst (ListPair.map (fn(v,tm)=>(v|->tm)) (l,l')) tm,
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

val tb = tb1 and tbl = [(tbx,tby),(tby,tbx)];
val tb = BddListCompose tbl tb;

val tb = tb1 and tbl = [(tbx,tbp),(tby,tbp)];
val tb4 = BddListCompose tbl tb;
(* p repeated *)

======================================================= End of test examples *)


(*****************************************************************************)
(* BddRestrict                                                               *)
(*  [((ass1 vm v1 |--> b1),(ass1' vm c1 |--> b1')),                          *)
(*                                                                           *)
(*   ((assi vm vi |--> bi),(assi' vm ci |--> bi'))]                          *)
(*  (ass vm tm |--> b)                                                       *)
(* (where c1,...,ci are T or F)                                              *)
(*                                                                           *)
(*       ass1 vm v1 |--> b1   ...   ass1' vm c1 |-> b1'                      *)
(*                             .                                             *)
(*                             .                                             *)
(*                             .                                             *)
(*       assi vm vi |--> bi   ...   assi' vm ci |-> bi'                      *)
(*       ass vm tm |--> b                                                    *)
(*  ---------------------------------------------------------------          *)
(*   (ass1 U ass1' ... assi U assi' U ass)                                   *)
(*   vm                                                                      *)
(*   (subst[v1 |-> c1, ... , vi |-> ci]tm)                                   *)
(*   |-->                                                                    *)
(*   restrict b (assignment[(var b1,mlval c1),...,(var i, mlval ci)])        *)
(*****************************************************************************)

exception BddRestrictError;

local

fun mlval tm =
 if tm=T
  then true
  else if tm=F then false else raise BddRestrictError

in

fun BddRestrict tbl tb =
 let val TermBdd(tg,ass,vm,tm,b) = tb
     val (tg_merge,ass_union, (l,l') ,restrictl) =
       foldr
        (fn(((TermBdd(tg1,ass1,vm1,v,b)),(TermBdd(tg2,ass2,vm2,c,_))),
            (tg,ass, (l,l'), restrictl))
           =>
           if not(Varmap.eq(vm,vm1) andalso Varmap.eq(vm,vm2))
            then (                print "unequal varmaps\n";
                                  raise BddRestrictError) else
           if not(is_var v)
            then (print_term v  ; print " should be a variable\n";
                                  raise BddRestrictError) else
           if mem v l
            then (print_term v  ; print" repeated\n";
                                  raise BddRestrictError)
            else (Tag.merge tg (Tag.merge tg1 tg2),
		  HOLset.union(ass,HOLset.union(ass1,ass2)),
                  (v :: l, c :: l'),
                  ((bdd.var b, mlval c)::restrictl)))
        (tg,ass, ([],[]), [])
        tbl
 in
  TermBdd(tg_merge,
	  ass_union,
          vm,
          subst (ListPair.map (fn(v,c)=>(v|->c)) (l,l')) tm,
          bdd.restrict b (bdd.assignment restrictl))
 end

end;

(*****************************************************************************)
(*   BddCon true  vm =  ({} vm ``T`` |--> TRUE)                              *)
(*   BddCon false vm =  ({} vm ``F`` |--> FALSE)                             *)
(*****************************************************************************)

fun BddCon tv vm =
 if tv then TermBdd(HolBddTag,Term.empty_tmset,vm,T,bdd.TRUE)
       else TermBdd(HolBddTag,Term.empty_tmset,vm,F,bdd.FALSE);

(*****************************************************************************)
(*                                                                           *)
(*     Varmap.peek vm (name v) = SOME n                                      *)
(*    ---------------------------------   BddVar true                        *)
(*         {} vm v |--> ithvar n                                             *)
(*                                                                           *)
(*     Varmap.peek vm (name v) = SOME n                                      *)
(*    ---------------------------------   BddVar false                       *)
(*        {} vm v |--> nithvar n                                             *)
(*                                                                           *)
(*****************************************************************************)

exception BddVarError;

fun BddVar tv vm v =
 case Varmap.peek vm (name v) of
    SOME n => if tv
               then TermBdd(HolBddTag,Term.empty_tmset,vm, v,        bdd.ithvar n)
               else TermBdd(HolBddTag,Term.empty_tmset,vm, mk_neg v, bdd.nithvar n)
  | NONE   => (print_term v; print " not in varmap\n"; raise BddVarError);

(*****************************************************************************)
(*     ass vm t |--> b                                                       *)
(*   --------------------                                                    *)
(*   ass vm ~t |--> NOT b                                                    *)
(*****************************************************************************)

fun BddNot(TermBdd(tg,ass,vm,t,b)) =  TermBdd(tg,ass,vm, mk_neg t, bdd.NOT b);

(*****************************************************************************)
(* Auxiliary function to perform on two terms the operation corresponding    *)
(* to a bddop                                                                *)
(*****************************************************************************)

fun termApply t1 t2 (bddop:bdd.bddop) =
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
(*       as1 vm t1 |--> b1    ass2 vm t2 |--> b2                             *)
(*  -------------------------------------------------                        *)
(*  (ass1 U ass2) vm (t1 <bddop> t2) |--> b1 bddop b2                        *)
(*                                                                           *)
(* where <bddop> is an operation of terms corresponding to the BDD           *)
(* binary operatiobn bddop (N.B. can't use "op" as it's an SML keyword)      *)
(*****************************************************************************)

exception BddOpError;

fun BddOp (bddop, TermBdd(tg1,ass1,vm1,t1,b1), TermBdd(tg2,ass2,vm2,t2,b2)) =
if Varmap.eq(vm1,vm2)
 then TermBdd(Tag.merge tg1 tg2,
	      HOLset.union(ass1,ass2),
              vm1,
              termApply t1 t2 bddop,
              bdd.apply b1 b2 bddop)
 else (print "different varmaps\n"; raise BddOpError);

(*****************************************************************************)
(* DISCH for term_bdd                                                        *)
(*****************************************************************************)

exception BddDischError;

fun BddDisch (TermBdd(tg1,ass1,vm1,tm1,b1))  (TermBdd(tg,ass,vm,tm,b)) =
    BddOp(Imp,
	  TermBdd(tg1,ass1,vm1,tm1,b1),
	  TermBdd(tg,HOLset.delete(ass,tm1) handle HOLset.NotFound => ass,vm,tm,b))

(*****************************************************************************)
(*    ass vm t |--> b   ass1 vm t1 |--> b1   ass2 vm t2 |--> b2              *)
(*  --------------------------------------------------------------           *)
(*  (ass U ass1 U ass2) vm (if t then t1 else t2) |--> ITE b b1 b2           *)
(*****************************************************************************)

exception BddIteError;

fun BddIte(TermBdd(tg,ass,vm,t,b),
           TermBdd(tg1,ass1,vm1,t1,b1),
           TermBdd(tg2,ass2,vm2,t2,b2)) =
 if Varmap.eq(vm,vm1) andalso Varmap.eq(vm1,vm2)
  then TermBdd(Tag.merge tg (Tag.merge tg1 tg2),
	       HOLset.union(ass,HOLset.union(ass1,ass2)),
               vm,
               mk_cond(t,t1,t2),
               bdd.ITE b b1 b2)
  else (print "different varmaps\n"; raise BddIteError);

(*****************************************************************************)
(*                  ass vm t |--> b                                          *)
(* -------------------------------------------------------                   *)
(* ass vm (!v1...vi. t) |--> forall (makeset[n1,...,ni]) b                   *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers in vm   *)
(* and vm is assumed to contain v1,...,vi.                                   *)
(* Raises BddForallError if any variable vj is not in the domain of vm or if *)
(* any of v1,...,vi occur free in any assumption                             *)
(*****************************************************************************)

exception BddForallError;

fun BddForall vl (TermBdd(tg,ass,vm,t,b)) =
 let open HOLset bdd
     val tml = intersection
                (addList(empty_tmset, vl),
                foldl (fn (t,s) => FVL [t] s) empty_tmset ass)
(* Possibly less efficient code:
     val tml = intersection
                (addList(empty_tmset, vl), FVL (listItems ass) empty_tmset)
*)
 in
  if isEmpty tml
   then
    let val bddvars =
          List.map
           (fn v => case Varmap.peek vm (name v) of
                       SOME n => n
                     | NONE   => raise BddForallError)
           vl
    in
     TermBdd(tg,ass,vm, list_mk_forall(vl,t), forall (makeset bddvars) b)
    end
   else
    (print_term(hd(listItems tml));
     print " free in assumptions";
     raise BddForallError)
 end;

(*****************************************************************************)
(*                  ass vm t |--> b                                          *)
(* ------------------------------------------------------                    *)
(* ass vm (?v1...vi. t) |--> exist (makeset[n1,...,ni]) b                    *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers in vm   *)
(* and vm is assumed to contain v1,...,vi.                                   *)
(* Raises BddExistsError if any variable vj is not in the domain of vm or if *)
(* any of v1,...,vi occur free in any assumption                             *)
(*****************************************************************************)

exception BddExistsError;

fun BddExists vl (TermBdd(tg,ass,vm,t,b)) =
 let open HOLset bdd
     val tml = intersection(ass, FVL vl empty_tmset)
 in
  if isEmpty tml
   then
    let val bddvars =
          List.map
           (fn v => case Varmap.peek vm (name v) of
                       SOME n => n
                     | NONE   => raise BddExistsError)
           vl
    in
     TermBdd(tg,ass,vm, list_mk_exists(vl,t), exist (makeset bddvars) b)
    end
   else
    (print_term(hd(listItems tml));
     print " free in assumptions";
     raise BddExistsError)
 end;

(*****************************************************************************)
(* ass1 vm t1 |--> b1    ass2 vm t2 |--> b2                                  *)
(* ----------------------------------------                                  *)
(* (ass1 U ass1)                                                             *)
(* vm                                                                        *)
(* (!v1...vi. t1 <bddop> t2)                                                 *)
(* |-->                                                                      *)
(* appall b1 b2 bddop (makeset[n1,...,ni])                                   *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers and     *)
(* vm is assumed to contain v1,...,vi                                        *)
(* Raises BddAppallError if any variable vj is not in the domain of vm or if *)
(* any of v1,...,vi occur free in any assumption                             *)
(*****************************************************************************)

exception BddAppallError;

fun BddAppall vl (bddop, TermBdd(tg1,ass1,vm1,t1,b1), TermBdd(tg2,ass2,vm2,t2,b2)) =
 let open HOLset bdd
     val tg = Tag.merge tg1 tg2
     val ass = union(ass1,ass2)
     val tml = intersection(ass, FVL vl empty_tmset)
 in
  if isEmpty tml
   then
    (if Varmap.eq(vm1,vm2)
      then
       TermBdd
        (tg,
	 ass,
         vm1,
         list_mk_forall(vl, termApply t1 t2 bddop),
         appall
          b1
          b2
          bddop
          (makeset
            (List.map (fn v => case Varmap.peek vm1 (name v) of
                                  SOME n => n
                                | NONE   => raise BddAppallError)
            vl)))
      else (print "different varmaps\n"; raise BddAppallError))
   else
    (print_term(hd(listItems tml));
     print " free in assumptions";
     raise BddAppallError)
 end;

(*****************************************************************************)
(* ass1 vm t1 |--> b1    ass2 vm t2 |--> b2                                  *)
(* ----------------------------------------                                  *)
(* (ass1 U ass1)                                                             *)
(* vm                                                                        *)
(* (?v1...vi. t1 <bddop> t2)                                                 *)
(* |-->                                                                      *)
(* appex b1 b2 bddop (makeset[n1,...,ni])                                    *)
(*                                                                           *)
(* where the list [v1,...,vi] of variables is supplied as a parameter,       *)
(* [n1,...,ni] is the list of the corresponding BDD variable numbers and     *)
(* vm is assumed to contain v1,...,vi                                        *)
(* Raises BddAppexError if any variable vj is not in the domain of vm or if *)
(* any of v1,...,vi occur free in any assumption                             *)
(*****************************************************************************)

exception BddAppexError;

fun BddAppex vl (bddop, TermBdd(tg1,ass1,vm1,t1,b1), TermBdd(tg2,ass2,vm2,t2,b2)) =
 let open HOLset bdd
     val tg = Tag.merge tg1 tg2
     val ass = union(ass1,ass2)
     val tml = intersection(ass, FVL vl empty_tmset)
 in
  if isEmpty tml
   then
    (if Varmap.eq(vm1,vm2)
      then
       TermBdd
        (tg,
	 ass,
         vm1,
         list_mk_exists(vl, termApply t1 t2 bddop),
         appex
          b1
          b2
          bddop
          (makeset
            (List.map (fn v => case Varmap.peek vm1 (name v) of
                                  SOME n => n
                                | NONE   => raise BddAppexError)
            vl)))
      else (print "different varmaps\n"; raise BddAppexError))
   else
    (print_term(hd(listItems tml));
     print " free in assumptions";
     raise BddAppexError)
 end;

(*****************************************************************************)
(*  Coudert, Berthet, Madre simplification                                   *)
(*                                                                           *)
(*       ass1 vm1 t1 |--> b1     ass2 vm2 t2 |--> b2                         *)
(*    ---------------------------------------------------                    *)
(*    (ass1 U ass2 U {t1}) vm1 t2 |--> bdd.simplify b1 b2                    *)
(*                                                                           *)
(* Raises BddSimplifyError if vm1 and vm2 are not pointer equal              *)
(*****************************************************************************)

exception BddSimplifyError;

fun BddSimplify (TermBdd(tg1,ass1,vm1,t1,b1), TermBdd(tg2,ass2,vm2,t2,b2)) =
 let open HOLset bdd
     val tg = Tag.merge tg1 tg2
     val ass = add(union(ass1,ass2), t1)
     val _   = if Varmap.eq(vm1,vm2) then () else raise BddSimplifyError
 in
  TermBdd(tg,ass,vm1,t2, simplify b1 b2)
 end;


(*****************************************************************************)
(* If t is satifiable (i.e. b is not FALSE)                                  *)
(*                                                                           *)
(*                  a vm t |--> b                                            *)
(*      --------------------------------------                               *)
(*      (a U {v1=c1,...,vn=cn}) vm t |--> TRUE                               *)
(*                                                                           *)
(*****************************************************************************)

(* Test data

val (TermBdd(ass,vm,t,b)) = termToTermBdd ``x /\ y /\ ~z /\ (p \/ q)``;

val (TermBdd(ass1,vm1,t1,b1)) = BddfindModel (TermBdd(ass,vm,t,b));

fun test t =
 let val (TermBdd(ass,vm,t,b)) = BddfindModel(termToTermBdd t)
 in
  (t,EVAL(subst (List.map  ((Lib.|->) o dest_eq) (HOLset.listItems ass)) t))
 end;

*)

exception BddfindModelError;

fun BddfindModel (TermBdd(tg,ass,vm,t,b)) =
 let val assl        = bdd.getAssignment(bdd.satone b)
     val vml         = Varmap.dest vm
     val setl        = List.map
                        (fn (n,tv) =>
                          mk_eq
                           ((case assoc2 n vml of
                                SOME(s,_) => mk_var(s,bool)
                              | NONE      => (print "This should not happen!\n";
                                              raise BddfindModelError)),
                            if tv then T else F))
                        assl
 in
  TermBdd(tg,HOLset.addList(ass,setl),vm,t,TRUE)
 end;

end;

(*
end;
*)

end
