(*****************************************************************************)
(* BddRules.sml                                                              *)
(* ------------                                                              *)
(*                                                                           *)
(* Types and rules implementing inference system for BDD representation      *)
(* judgements.                                                               *)
(*                                                                           *)
(* New version of reachability tools.                                        *)
(*                                                                           *)
(* Revision history:                                                         *)
(*                                                                           *)
(*  Tue Sep 12 2000:                                                         *)
(*   added missing definition of termToTermBdd                               *)
(*   (thanks to John Matthews <johnm@crl.dec.com> for supplying the fix)     *)
(*                                                                           *)
(*****************************************************************************)

(* structure BddRules :> BddRules = struct  *)

(*****************************************************************************)
(* Rules for deducing BDD representation judgements                          *)
(*****************************************************************************)

(*
load "HolBddLib";
load "pairLib";
*)

open HolBdd;
open StateEnum;
open bdd;
open pairSyntax;
open Pair_basic;

local 

(* Function to make arguments of subst work in Kananaskis *)

fun pair2recd (v,M) = {redex=v, residue=M};

open HolKernel Parse boolLib 
     BasicProvers pairSyntax pairTools numLib HolBdd;

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

in

(*****************************************************************************)
(* Flatten a varstruct term into a list of variables (also in StateEnum).    *)
(*****************************************************************************)

fun flatten_pair t =
if is_pair t
 then foldr (fn(t,l) => (flatten_pair t) @ l) [] (strip_pair t)
 else [t];

(*****************************************************************************)
(* Map over a tuple (also in StateEnum).                                     *)
(*****************************************************************************)

fun map_tuple f tup =
 if is_pair tup
  then let val (t1,t2) = dest_pair tup
       in
        mk_pair(map_tuple f t1, map_tuple f t2)
       end
  else f tup;


(* Also defined in StateEnum.sml *)

val ReachBy_CONV = CONV_RULE o RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV;
fun ReachBy_SUC_CONV n =
 ReachBy_CONV(REWR_CONV(SYM(Num_conv.num_CONV(intToTerm(n+1)))));


(*****************************************************************************)
(* A value of ML type term_bdd represents a judgement                        *)
(*                                                                           *)
(*    rho tm |--> bdd                                                        *)
(*                                                                           *)
(* Here rho is a variable map and can either be the global one               *)
(* forming the first component of the BDD state (i.e. snd(fst(!bdd_state)))  *)
(* or be given explicitly. The first case is modelled with                   *)
(* globalBddEnv and the second with BddEnv vm (where vm is a var_map).       *)
(* Thus                                                                      *)
(*                                                                           *)
(*   TermBdd (globalBddEnv, tm, bdd)  -- global variable map                 *)
(*   TermBdd (BddEnv vm,    tm, bdd)  -- local (explicit) variable map       *)
(*****************************************************************************)

(*
type var_map = (string, int) Binarymap.dict;
*)

(* General case (not yet supported)
datatype term_bdd = TermBdd of bdd_env * term * bdd.bdd
and      bdd_env  = globalBddEnv | BddEnv of var_map;
*)

(*****************************************************************************)
(* Currently only a single global variable map is supported. The             *)
(* motivation for local maps is that a goal might split into subgoals g1     *)
(* and g2 which need different variable reorderings for their                *)
(* solution. With the current BuDDy this can be implemented by mapping       *)
(* the variables into different segments of the integers and keeping         *)
(* track of the separate mappings via local variable maps in                 *)
(* judgements. The code for the judgement rules will need to check           *)
(* various variable consistency conditions, which will be a bit              *)
(* messy. For the time being judgements are restricted to having the form    *)
(* TermBdd(globalBddEnv,t,b) so environment combining case analysis          *)
(* isn't needed.                                                             *)
(*****************************************************************************)

(*****************************************************************************)
(* Simplified datatype for the case of just global variable maps.            *)
(*****************************************************************************)

datatype term_bdd = TermBdd of term * bdd.bdd;

(*****************************************************************************)
(* Test equality and return true or false                                    *)
(*****************************************************************************)

fun BddEqualTest (TermBdd(_,b1)) (TermBdd(_,b2)) = bdd.equal b1 b2;

(*****************************************************************************)
(* Add a term_bdd to the global BDD map.                                     *)
(*****************************************************************************)

fun addTermBdd (TermBdd(tm,bdd)) =
 let val (var_map,(htbl,term_net)) = !HolBdd.bdd_state
     val bdd_map'                  = ((Polyhash.insert htbl (tm,bdd);htbl),
                                      Net.insert(tm,tm)term_net)
 in
  HolBdd.bdd_state := (var_map,bdd_map'); ()  
 end;

(*****************************************************************************)
(* Oracle function                                                           *)
(*                                                                           *)
(*    t |--> TRUE                                                            *)
(*    -----------                                                            *)
(*       |- t                                                                *)
(*****************************************************************************)

exception TermBddOracleError;

fun TermBddOracle(TermBdd(tm,bdd)) =
 if bdd.equal bdd bdd.TRUE 
  then mk_oracle_thm HolBddTag ([],tm) 
  else raise TermBddOracleError;

(*****************************************************************************)
(* Look up the BDD variable corresponding to a HOL variable                  *)
(*****************************************************************************)

fun varToInt v = 
 Binarymap.find(snd(fst(!bdd_state)), fst(dest_var v))
  handle Binarymap.NotFound  
  => (pureTermToBdd v;                      (* Add variable to variable map *)
      Binarymap.find(snd(fst(!bdd_state)), fst(dest_var v)));  (* try again *)

(*****************************************************************************)
(* Use termToBdd to make a representation judgement.                         *)
(*****************************************************************************)

(*****************************************************************************)
(*                                                                           *)
(*         rho(v) = n                                                        *)
(*   ------------------------                                                *)
(*    v |--> termToTermBdd v                                                 *)
(*                                                                           *)
(* Implementation below should be optimised to avoid using                   *)
(* termToTermBdd.                                                            *)
(*****************************************************************************)

fun termToTermBdd t = TermBdd(t, termToBdd t);

exception BddVarError;

fun BddVar v = 
 if is_var v then termToTermBdd v else raise BddVarError;

val BddT = termToTermBdd T
and BddF = termToTermBdd F;

(*****************************************************************************)
(*     t |--> b                                                              *)
(*   -------------                                                           *)
(*   ~t |--> NOT b                                                           *)
(*****************************************************************************)

fun BddNot(TermBdd(t,b)) =  TermBdd(mk_neg t, NOT b);

(*****************************************************************************)
(*  t1 |--> b1  t2 |--> b2                                                   *)
(*  ----------------------                                                   *)
(*  t1 \/ t2 |--> b1 OR b2                                                   *)
(*****************************************************************************)

fun BddOr(TermBdd(t1,b1), TermBdd(t2,b2)) = 
 TermBdd(mk_disj(t1,t2), OR(b1,b2));

(*****************************************************************************)
(*  t1 |--> b1  t2 |--> b2                                                   *)
(*  ----------------------                                                   *)
(*  t1 /\ t2 |--> b1 AND b2                                                  *)
(*****************************************************************************)

fun BddAnd(TermBdd(t1,b1), TermBdd(t2,b2)) = 
 TermBdd(mk_conj(t1,t2), AND(b1,b2));

(*****************************************************************************)
(*   t1 |--> b1  t2 |--> b2                                                  *)
(*  ------------------------                                                 *)
(*  t1 ==> t2 |--> b1 IMP b2                                                 *)
(*****************************************************************************)

fun BddImp(TermBdd(t1,b1), TermBdd(t2,b2)) = 
 TermBdd(mk_imp(t1,t2), IMP(b1,b2));

(*****************************************************************************)
(*   t1 |--> b1  t2 |--> b2                                                  *)
(*  ------------------------                                                 *)
(*  t1 = t2 |--> b1 BIIMP b2                                                 *)
(*****************************************************************************)

fun BddEq(TermBdd(t1,b1), TermBdd(t2,b2)) = 
 TermBdd(mk_eq(t1,t2), BIIMP(b1,b2));

(*****************************************************************************)
(*          t |--> b   t1 |--> b1   t2 |--> b2                               *)
(* ------------------------------------------------------                    *)
(* if t then t1 else t2 |--> (b AND b1) OR (NOT b AND b2)                    *)
(*****************************************************************************)

fun BddCond(TermBdd(t,b), TermBdd(t1,b1), TermBdd(t2,b2)) = 
 TermBdd(mk_cond(t,t1,t2), OR(AND(b, b1), AND(NOT b, b2)));

(*****************************************************************************)
(*                   t |--> b                                                *)
(* ----------------------------------------------                            *)
(* !v1...vm. t |--> forall (makeset[w1,...,wn]) b                            *)
(*                                                                           *)
(* where the list [v1,...,vm] of varstructs is supplied as a parameter       *)
(* and [w1,...,wn] is the list of BDD variable numbers obtained by           *)
(* appending the flattened varstructs.                                       *)
(*                                                                           *)
(*****************************************************************************)

fun BddForall(vl, TermBdd(t,b)) =
 let val flatvl  = foldr (fn(v,vl) => append (flatten_pair v) vl) [] vl
     val varset  = bdd.makeset (List.map varToInt flatvl)
 in
  TermBdd(pairSyntax.list_mk_pforall(vl,t), bdd.forall varset b)
 end;

(*****************************************************************************)
(*                   t |--> b                                                *)
(* ----------------------------------------------                            *)
(* ?v1...vm. t |--> exists (makeset[w1,...,wn]) b                            *)
(*                                                                           *)
(* where the list [v1,...,vm] of varstructs is supplied as a parameter       *)
(* and [w1,...,wn] is the list of BDD variable numbers obtained by           *)
(* appending the flattened varstructs.                                       *)
(*                                                                           *)
(*****************************************************************************)

fun BddExists(vl, TermBdd(t,b)) =
 let val flatvl  = foldr (fn(v,vl) => append (flatten_pair v) vl) [] vl
     val varset  = bdd.makeset (List.map varToInt flatvl)
 in
  TermBdd(pairSyntax.list_mk_pexists(vl,t), bdd.exist varset b)
 end;

(*****************************************************************************)
(*               t1 |--> b1    t2 |--> b2                                    *)
(* ------------------------------------------------------                    *)
(* Q v1...vm. t |--> appall b1 b2 op (makeset[w1,...,wn])                    *)
(*                                                                           *)
(* where the list [v1,...,vm] of varstructs is supplied as a parameter       *)
(* and [w1,...,wn] is the list of variables obtained by appending the        *)
(* flattened varstructs.                                                     *)
(*                                                                           *)
(*****************************************************************************)

(* Test data

   BddAppQuant 
    (pairSyntax.list_mk_pforall, appall)
    [``x:bool``, ``(y:bool,z:bool)``,``w:bool``]
    (termToTermBdd ``x /\ y``, termToTermBdd ``z /\ w``)
    (mk_disj, Or)
*)

fun BddAppQuant 
     (quant,bddquant)
     (tmconstr,bddop)  
     vl 
     (TermBdd(t1,b1), TermBdd(t2,b2)) =
 let val flatvl  = foldr (fn(v,vl) => append (flatten_pair v) vl) [] vl
     val varset  = bdd.makeset (List.map varToInt flatvl)
 in
  TermBdd(quant(vl,tmconstr(t1,t2)), bddquant b1 b2 bddop varset)
 end;

val BddForallAnd = BddAppQuant(pairSyntax.list_mk_pforall,appall)(mk_conj,And);
val BddForallOr  = BddAppQuant(pairSyntax.list_mk_pforall,appall)(mk_disj,Or);
val BddForallImp = BddAppQuant(pairSyntax.list_mk_pforall,appall)(mk_imp,Imp);
val BddForallEq  = BddAppQuant(pairSyntax.list_mk_pforall,appall)(mk_eq,Biimp);

val BddExistsAnd = BddAppQuant(pairSyntax.list_mk_pexists,appex)(mk_conj,And);
val BddExistsOr  = BddAppQuant(pairSyntax.list_mk_pexists,appex)(mk_disj,Or);
val BddExistsImp = BddAppQuant(pairSyntax.list_mk_pexists,appex)(mk_imp,Imp);
val BddExistsEq  = BddAppQuant(pairSyntax.list_mk_pexists,appex)(mk_eq,Biimp);

(*****************************************************************************)
(*   |- t1 = t2   t1 |--> b                                                  *)
(*   ----------------------                                                  *)
(*         t2 |--> b                                                         *)
(*****************************************************************************)

exception BddEqMpError;

fun BddEqMp th (TermBdd(t1,b)) =
 let val (a,c) = dest_thm th
     val (l,r) = dest_eq c
 in
  if not((a=[]) andalso (aconv l t1)) 
   then raise BddEqMpError 
   else TermBdd(r,b)
 end;

(*****************************************************************************)
(*   |- t1 = t2   t2 |--> b                                                  *)
(*   ----------------------                                                  *)
(*         t1 |--> b                                                         *)
(*****************************************************************************)

val BddEqMpSYM = BddEqMp o SYM;


(*****************************************************************************)
(* Write BDD<t> to denote the BDD representing term t. It should always      *)
(* be the case for any value TermBdd(t,b) that BDD<t>=b. Also should be the  *)
(* case that termToBdd t = BDD<t>. This invariant is maintained by the       *)
(* LCF-style abstract type.                                                  *)
(*                                                                           *)
(* In code comments we shall sometimes write (t,b) to abbreviate             *)
(* TermBdd(t,b). The type should be clear from the code.                     *)
(*                                                                           *)
(* BddImage                                                                  *) 
(*  (``B(v1,...,vn)``, b1)                                                   *) 
(*  (``R(v1,...,vn,v1',...,vn'), b2)                                         *) 
(*  =                                                                        *) 
(*  (``?v1'...vn'. B(v1',...,vn') /\ R(v1',...,vn',v1,...,vn)``,             *) 
(*   BDD<?v1'...vn'. B(v1',...,vn') /\ R(v1',...,vn',v1,...,vn)>             *)
(*****************************************************************************)

fun BddImage (TermBdd(Btm,Bbdd)) (TermBdd(Rtm,Rbdd)) =
 let val (R,st_st') = dest_comb Rtm
     val (st,st')   = dest_pair st_st'
     val vs         = flatten_pair st
     val vs'        = flatten_pair st'
     val varset     = makeset(map varToInt vs)
     val pairs      = (map2 (fn v => fn v' => pair2recd(v',v)) vs vs' 
                       @
                       map2 (fn v => fn v' => pair2recd(v,v')) vs vs')
     val pairset    =  makepairSet
                        (map2 (fn v=>fn v'=>(varToInt v',varToInt v)) vs vs')
 in
  TermBdd
   (list_mk_exists(vs', subst pairs (mk_conj(Btm,Rtm))),
    replace (appex Bbdd Rbdd bdd.And varset) pairset)
 end;

(*****************************************************************************)
(* Write BDD<t> to denote the BDD representing term t. It should always      *)
(* be the case for any value TermBdd(t,b) that BDD<t>=b. Also should be the  *)
(* case that termToBdd t = BDD<t>. This invariant is maintained by the       *)
(* LCF-style abstract type.                                                  *)
(*                                                                           *)
(* In code comments we shall sometimes write (t,b) to abbreviate             *)
(* TermBdd(t,b). The type should be clear from the code.                     *)
(*                                                                           *)
(* BddPairedImage                                                            *) 
(*  (``B(v1,...,vn)``, b1)                                                   *) 
(*  (``R(v1,...,vn,v1',...,vn'), b2)                                         *) 
(*  =                                                                        *) 
(*  (``?(v1',...,vn'). B(v1',...,vn') /\ R(v1',...,vn',v1,...,vn)``,         *) 
(*   BDD<?(v1',...,vn'). B(v1',...,vn') /\ R(v1',...,vn',v1,...,vn)>         *)
(*****************************************************************************)

fun BddPairedImage (TermBdd(Btm,Bbdd)) (TermBdd(Rtm,Rbdd)) =
 let val (R,st_st') = dest_comb Rtm
     val (st,st')   = dest_pair st_st'
     val vs         = flatten_pair st
     val vs'        = flatten_pair st'
     val varset     = makeset(map varToInt vs)
     val pairs      = (map2 (fn v => fn v' => pair2recd(v',v)) vs vs'
                       @
                       map2 (fn v => fn v' => pair2recd(v,v')) vs vs')
     val pairset    =  makepairSet
                        (map2 (fn v=>fn v'=>(varToInt v',varToInt v)) vs vs')
 in
  TermBdd
   (pairSyntax.mk_pexists(st', subst pairs (mk_conj(Btm,Rtm))),
    replace (appex Bbdd Rbdd bdd.And varset) pairset)
 end;

(*****************************************************************************)
(* BddMatch (TermBdd(tm1,b)) tm2 matches tm1 to tm2 and if the match         *)
(* succeeds with a variable-to-variable substitution, returns                *)
(* TermBdd(tm2,b'), where b' is the BDD obtained by replacing variables      *)
(* in b.                                                                     *)
(*                                                                           *)
(* BddMatch (TermBdd(tm1,b)) tm2 =                                           *)
(*  TermBdd(tm2,                                                             *)
(*          subst_bdd                                                        *)
(*           var_map                                                         *)
(*           (match_to_pairs(fst(match_term tm1 tm2)))                       *)
(*           b)                                                              *)
(*                                                                           *)
(* where var_map is the current variable map                                 *)
(*****************************************************************************)


exception BddMatchError;

local

fun check_and_flip []             = []
 |  check_and_flip (({redex=new,residue=old})::l) =  (* WARNING: this could be wrong *)
     if not(exists (fn ({redex=new',residue=_}) => new=new') l) 
         andalso (type_of new = bool) andalso is_var new
         andalso (type_of old = bool) andalso is_var old
      then (old,new)::check_and_flip l
      else raise BddMatchError

in

fun BddMatch (TermBdd(tm1,b)) tm2 =
 TermBdd
  (tm2,
   bdd.replace 
    b 
    (bdd.makepairSet
      (List.map 
        (varToInt ## varToInt) 
        (check_and_flip(fst(match_term tm1 tm2))))))

end;


(*****************************************************************************)
(* Recurse through a term constructing a term_bdd. Apply f to leaves.        *)
(*****************************************************************************)

(* Test data
fun test (TermBdd(tm,bdd)) = bdd.equal (termToBdd tm) bdd;

val term2TermBdd = recTermBdd termToTermBdd;

val Foo_def = bossLib.Define `Foo x y = x /\ y`;

term2TermBdd ``x:bool``;
term2TermBdd ``~x``;
term2TermBdd ``x /\ y``;
term2TermBdd ``x \/ y``;
term2TermBdd ``x /\ y \/ (p /\ ~ q)``;
term2TermBdd ``x /\ y \/ (p /\ ~ (q = x) /\ r ==> y)``;
term2TermBdd ``!x y (p,q). x /\ y \/ (p /\ ~!(r,s) t. q /\ r /\ ~t)``;

val Foo_def = bossLib.Define `Foo x y = x /\ y`;

addEquation Foo_def;


recTermBdd 
 (BddMatch(termToTermBdd ``Foo a b``)) 
 ``!x y (p,q). x /\ y \/ (p /\ ~!(r,s) t. q /\ r /\ ~t)``;

*)

fun recTermBdd f tm =
 let fun recfn tm =
  if is_neg tm
   then BddNot(recfn(dest_neg tm)) else
  if is_conj tm
   then BddAnd((recfn ## recfn)(dest_conj tm)) else
  if is_disj tm
   then BddOr((recfn ## recfn)(dest_disj tm)) else
  if is_imp tm
   then BddImp((recfn ## recfn)(dest_imp tm)) else
  if is_eq tm
   then BddEq((recfn ## recfn)(dest_eq tm)) else
  if is_forall tm
   then 
    let val (vs,bdy) = strip_pforall tm
    in
     if is_conj bdy
      then BddForallAnd vs ((recfn ## recfn)(dest_conj bdy)) else
     if is_disj bdy
      then BddForallOr vs ((recfn ## recfn)(dest_disj bdy))  else
     if is_imp bdy
      then BddForallImp vs ((recfn ## recfn)(dest_imp bdy))  else
     if is_eq bdy andalso 
        (Term.type_of(Term.rand bdy) = Type.bool)
      then BddForallEq vs ((recfn ## recfn)(dest_eq bdy))    else
     BddForall(vs,recfn bdy)      
    end 
   else
  if is_exists tm
   then 
    let val (vs,bdy) = strip_pexists tm
    in
     if is_conj bdy
      then BddExistsAnd vs ((recfn ## recfn)(dest_conj bdy)) else
     if is_disj bdy
      then BddExistsOr vs ((recfn ## recfn)(dest_disj bdy))  else
     if is_imp bdy
      then BddExistsImp vs ((recfn ## recfn)(dest_imp bdy))  else
     if is_eq bdy andalso 
        (Term.type_of(Term.rand bdy) = Type.bool)
      then BddExistsEq vs ((recfn ## recfn)(dest_eq bdy))    else
     BddExists(vs,recfn bdy)      
    end 
   else
  f tm
 in
  recfn tm
 end;

(*****************************************************************************)
(* MkReachByRecThms ``R((v1,...,vn),(v1',...,vn'))`` ``B(v1,...,vn)`` =      *)
(*  ([|- ReachBy R B 0 (v1,...,vn) = B(v1,...,vn),                           *)
(*    |- !n. ReachBy R B (SUC n) (v1,...,vn) =                               *)
(*                ReachBy R B n (v1,...,vn)                                  *)
(*                \/                                                         *)
(*                ?(v1',...,vn'). ReachBy R B n (v1',...,vn')                *)
(*                                /\                                         *)
(*                                R ((v1',...,vn'),(v1,...,vn))]             *)
(*****************************************************************************)

val num = ``:num``;
val ntm = mk_var("n",num);

fun MkReachByRecThms Rtm Btm =
 let val (R,st_st') = dest_comb Rtm
     val (st,st') = dest_pair st_st'
     val (B,st0) = dest_comb Btm
     val _ = (st = st0) 
             orelse hol_err "R and B vars not consistent" "MkReachByRecThms"
     val ty     = type_of st
     val th = INST_TYPE
               [pair2recd(ty,``:'a``),pair2recd(ty,``:'b``)]
               HolBddTheory.ReachBy_rec
     val [th1,th2] = CONJUNCTS th
     val statevars = flatten_pair st
     val statevarnames = map (fst o dest_var) statevars
(* ------------------------- not sure why I did this! ------------------------
     val prime_sym = (* if a state variables ends with "'", use "+" instead *)
          if mem #"'" (map (last o explode) statevarnames) 
           then "+" 
           else "'"
     fun prime_var v = 
      let val (name,typ) = dest_var v in mk_var((name^prime_sym),typ) end
     val st' = map_tuple prime_var st
-----------------------------------------------------------------------------*)
 in
  (SPECL[R,B,st]th1,
   GEN ntm (CONV_RULE 
            (RHS_CONV(RAND_CONV(GEN_PALPHA_CONV st'))) 
            (SPECL[R,B,ntm,st]th2)))
 end;

(*****************************************************************************)
(* ReachByStep computes                                                      *)
(*                                                                           *)
(*  ReachByStep                                                              *)
(*   (|- A = ReachBy R B n (v1,...,vn) \/                                    *)
(*            ?(v1',...,vn'). ReachBy R B n (v1',...,vn')                    *)
(*                            /\                                             *)
(*                            R ((v1',...,vn'),(v1,...,vn)) )                *)
(*   (``ReachBy R B n (v1,...,vn)``, b1)                                     *)
(*   (``R(v1,...,vn,v1',...,vn'), b2)                                        *)
(*   =                                                                       *)
(*   (``A``,                                                                 *)
(*    BDD<ReachBy R B n (v1,...,vn) \/                                       *)
(*         ?(v1',...,vn').                                                   *)
(*          ReachBy R B n (v1',...,vn') /\ R ((v1',...,vn'),(v1,...,vn))>)   *)
(*****************************************************************************)

exception ReachByStepError;

fun ReachByStep th term_bdd R_term_bdd =
 let val (TermBdd(t,b)) = 
      BddOr(term_bdd, BddPairedImage term_bdd R_term_bdd)
     val (l,r) = dest_eq(concl th)
 in
  if (r=t) andalso null(hyp th) then TermBdd(l,b) else raise ReachByStepError
 end;

(*****************************************************************************)
(*  ComputeReachByFixedpoint                                                 *)
(*   report                                                                  *)
(*   (``R(v1,...,vn,v1',...,vn'), b2)                                        *)
(*   (``B(v1,...,vn)``, b1)                                                  *)
(*   =                                                                       *)
(*   ((``ReachBy R B n (v1,...,vn)``,   BDD<ReachBy R B n (v1,...,vn)>),     *)
(*    (``ReachBy R B n+1 (v1,...,vn)``, BDD<ReachBy R B n+1 (v1,...,vn)))    *)
(*                                                                           *)
(* where n is the first n such that                                          *)
(*                                                                           *)
(*    ReachBy R B n (v1,...,vn) = ReachBy R B (SUC n) (v1,...,vn)            *)
(*                                                                           *)
(* The function report is applied at each iteration to the iteration count   *)
(* and to the corresponding intermediate term_bdd.                           *)
(*                                                                           *)
(*****************************************************************************)

(* Clean and simple version 
   runtime: 7.480s,     gctime: 0.210s,   systime: 0.000s.  (HexSolitaire)
   runtime: 28487.510s, gctime: 407.360s, systime: 26.330s. (Solitaire)
    [nodecount: 1538740]
*)

(*
fun ComputeReachByFixedpoint report R_term_bdd B_term_bdd =
 let val (TermBdd(Rtm,_)) = R_term_bdd
     val (TermBdd(Btm,_)) = B_term_bdd
     val (th0,SUCth) = MkReachByRecThms Rtm Btm
     fun iter n (term_bdd as (TermBdd(_,bdd))) =
      let val _ = report n term_bdd
          val (term_bdd' as (TermBdd(_,bdd'))) = 
                ReachByStep 
                 (ReachBy_SUC_CONV n (SPEC (intToTerm n) SUCth))
                 term_bdd
                 R_term_bdd
      in
       if bdd.equal bdd bdd' 
        then (term_bdd,term_bdd')
        else iter (n+1) term_bdd'
      end
 in
  iter 0 (BddEqMpSYM th0 B_term_bdd)
 end;
*)

fun ComputeReachByFixedpoint report R_term_bdd B_term_bdd =
 let val (TermBdd(Rtm,_)) = R_term_bdd
     val (TermBdd(Btm,_)) = B_term_bdd
     val (th0,SUCth) = MkReachByRecThms Rtm Btm
     fun iter n term_bdd  =
      let val _ = report n term_bdd
          val term_bdd' = 
                ReachByStep 
                 (ReachBy_SUC_CONV n (SPEC (intToTerm n) SUCth))
                 term_bdd
                 R_term_bdd
      in
       if BddEqualTest term_bdd term_bdd' 
        then (term_bdd,term_bdd')
        else iter (n+1) term_bdd'
      end
 in
  iter 0 (BddEqMpSYM th0 B_term_bdd)
 end;

(*
fun ComputeSimpReachByFixedpoint report R_term_bdd B_term_bdd =
 let val (TermBdd(Rtm,_)) = R_term_bdd
     val (TermBdd(Btm,_)) = B_term_bdd
     val [th0,SUCth] = CONJUNCTS(MakeSimpReachByRecThm(Rth,Bth))
     fun iter n (term_bdd as (TermBdd(tm,bdd))) =
      let val _ = report n term_bdd
          val th = SPEC (intToTerm n) SUCth
          val (term_bdd' as (TermBdd(_,bdd'))) = 
              BddEqMpSYM
               th
               (recTermBdd (BddMatch term_bdd) (rhs(concl th)))
(*
                ReachByStep 
                 (ReachBy_SUC_CONV n (SPEC (intToTerm n) SUCth))
                 term_bdd
                 R_term_bdd
*)

      in
       if bdd.equal bdd bdd' 
        then (term_bdd,term_bdd')
        else iter (n+1) term_bdd'
      end
 in
  iter 0 (BddEqMpSYM th0 B_term_bdd)
 end;
*)

(*****************************************************************************)
(*  ComputeReachableBdd                                                      *)
(*   report                                                                  *)
(*   (|- R(v1,...,vn,v1',...,vn') = Rdef, |- B(v1,...,vn) = Bdef)            *)
(*   =                                                                       *)
(*   (|- Reachable R B (v1,...,vn) = ReachBy R B n (v1,...,vn),              *)
(*    BDD<Reachable R B (v1,...,vn)>)                                        *)
(*                                                                           *)
(* where n is the first n such that                                          *)
(*                                                                           *)
(*    ReachBy R B n (v1,...,vn) = ReachBy R B (SUC n) (v1,...,vn)            *)
(*                                                                           *)
(*****************************************************************************)

fun ComputeReachableBdd report (Rth,Bth) =
 let val Rth1                 = SPEC_ALL Rth
     val (Rtm,Rdef)           = dest_eq(concl Rth1)
     val R_term_bdd           = BddEqMpSYM Rth1 (termToTermBdd Rdef)
     val Bth1                 = SPEC_ALL Bth
     val (Btm,Bdef)           = dest_eq(concl Bth1)
     val B_term_bdd           = BddEqMpSYM Bth1 (termToTermBdd Bdef)
     val (term_bdd,term_bdd') = ComputeReachByFixedpoint 
                                 report 
                                 R_term_bdd 
                                 B_term_bdd
     val th1                  = TermBddOracle(BddEq(term_bdd, term_bdd'))
     val st                   = rand(lhs(concl th1))
     val th2                  = MATCH_MP
                                 HolBddTheory.ReachBy_fixedpoint
                                  (MATCH_MP
                                    EQ_EXT
                                    (pairTools.PGEN 
                                      (genvar(type_of st))
                                      st
                                      (SYM(ReachBy_CONV Num_conv.num_CONV(SYM th1)))))
     val th3                  = AP_THM th2 st
 in
  (th3, BddEqMpSYM th3 term_bdd)
 end;

end

(* end *)
