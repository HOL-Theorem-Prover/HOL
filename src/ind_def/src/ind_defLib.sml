(* ===================================================================== *)
(* FILE          : ind_defLib.sml                                     *)
(* DESCRIPTION   : Tom Melham's inductive definition package. Translated *)
(*                 from hol88, but some dependencies remain, see occs of *)
(*                 hol88Lib structure prefix.                            *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(*                                                                       *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* ===================================================================== *)

structure ind_defLib :> ind_defLib =
struct

open HolKernel Parse basicHol90Lib;

type term   = Term.term
type fixity = Term.fixity
type thm    = Thm.thm
type conv   = Abbrev.conv
type tactic = Abbrev.tactic
type thm_tactic = Abbrev.thm_tactic
type 'a quotation = 'a frag list


infix ## |->;
infix THEN THENL;

fun IND_DEF_ERR{function,message} = 
        HOL_ERR{origin_structure = "Library \"Ind_def\"",
                origin_function = function,
                message = message};

(* ===================================================================== *)
(* INDUCTIVE DEFINITIONS.						 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION: mk_predv						 *)
(*									 *)
(* The function mk_predv, given a list of terms:			 *)
(*									 *)
(*      ["t1:ty1";"t2:ty2";...;"tn:tyn"]				 *)
(*									 *)
(* returns a variable P of type:					 *)
(*									 *)
(*      P:ty1->ty2->...->tyn->bool					 *)
(*									 *)
(* The choice of name `P` is fixed.					 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let mk_predv =                                                        *)
(*    let itfn tm ty = mk_type(`fun`,[type_of tm;ty]) in                 *)
(*     \ts. mk_var(`P`,itlist itfn ts ":bool");;                         *)
(* --------------------------------------------------------------------- *)

local fun itfn tm ty = mk_type{Tyop="fun",Args=[type_of tm,ty]}
in
fun mk_predv ts = mk_var{Name="P",Ty=itlist itfn ts Type.bool}
end;

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION: checkfilter 					 *)
(*									 *)
(* The function checkfilter takes two lists "ps" and "as", where ps is a *)
(* sublist of as. A function is returned that that behaves as follows.   *)
(* When applied to a list l, the function checks that the elements of l  *)
(* exactly match the elements of "as" at those positions of this list at *)
(* which there occur elements of "ps".  The function furthermore checks  *)
(* that l has the same length as "as".					 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let checkfilter =                                                     *)
(*     letrec check ps as =                                              *)
(*        if (null as) then assert null else                             *)
(*        let cktl = check ps (tl as) in                                 *)
(*        if (mem (hd as) ps)                                            *)
(*           then let v = hd as in \(h.t). (h=v) => cktl t | fail        *)
(* 	  else \(h.t). h . cktl t in                                     *)
(*     \ps as. let f = check ps as in                                    *)
(*             \l. f l ? failwith `ill-formed membership assertion`;;    *)
(*									 *)
(* let checkside R tm =                                                  *)
(*     if (free_in R tm) then                                            *)
(*        failwith `"`^(fst(dest_var R))^`" free in side-condition(s)`   *)
(*     else                                                              *)
(*        tm;;                                                           *)
(* --------------------------------------------------------------------- *)


exception checkfilter_ERR of string;
local 
exception err
fun check ps [] = assert null
  | check ps (H :: T) =
      let val cktl = check ps T
      in if (mem H ps) 
         then fn (h::t) =>  if (H = h) then cktl t else raise err
         else fn (h::t) => (h :: (cktl t)) 
      end
in
fun checkfilter ps a =
   let val f = check ps a
   in fn l => (f l)
           handle _ => raise IND_DEF_ERR{function = "checkfilter",
                                   message = "ill-formed membership assertion"}
   end
end;

fun checkside R tm = 
   if (free_in R tm)
   then raise IND_DEF_ERR{function = "checkside",
           message = Lib.quote(#Name(dest_var R))^" free in side-condition(s)"}
   else tm;

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION : mk_mk_pred					 *)
(*									 *)
(* The arguments to this function are the user-supplied pattern pat, and *)
(* the list of global parameters ps (see below for a specification of 	 *)
(* required format of these inputs).  The pattern, pat, is expected to	 *)
(* have the form shown below:						 *)
(*									 *)
(*   pat = "R x1 ... xn"						 *)
(*									 *)
(* and mk_mk_pred fails (with an appropriate message) if:		 *)
(*									 *)
(*   1: pat is not a boolean term					 *)
(*   2: any one of R, x1, ... xn is not a variable			 *)
(*   3: the xi's are not all distinct					 *)
(*									 *)
(* The second argument, ps, is a list of global parameter variables:	 *)
(*									 *)
(*   ["y1",...,"ym"]							 *)
(*									 *)
(* where {"y1",...,"ym"} is expected to be a subset of {"x1",...,"xm"}.	 *)
(* Failure occurs if:							 *)
(*									 *)
(*   1: any one of "y1",...,"ym" is not a variable			 *)
(*   2: any "yi" is not an element of {"x1",...,"xm"}.			 *)
(*   3: the "yi"'s are not all distinct					 *)
(*									 *)
(* A successful call to mk_mk_pred pat ps, where the inputs pat and ps	 *)
(* are as described above, returns a function that maps applications of  *)
(* the form:								 *)
(*									 *)
(*   "R a1 ... an"							 *)
(*									 *)
(* to applications of the form:						 *)
(*									 *)
(*   "P ai ... aj"							 *)
(*									 *)
(* where ai,...,aj is the subsequence of a1, ..., an consisting of those *)
(* arguments to R whose positions correspond to the positions of the 	 *)
(* variables in the pattern "R x1 ... xn" that do NOT occur in the 	 *)
(* global paramter list ps. Furthermore, at all other positions (ie at 	 *)
(* those positions that correspond to global parameters) the a's must	 *)
(* be identical to the parameter variables "y1",...,"ym".		 *)
(*									 *)
(* For example, if:							 *)
(*									 *)
(*   pat = "R x1 x2 x3 x4"   and   ps = ["x1";"x3"]			 *)
(*									 *)
(* then the function returned by mk_mk_pred expects input terms of the 	 *)
(* form "R x1 a1 x3 a2" and maps these to "P a1 a2". Failure occurs if	 *)
(* the agument to this function does not have the correct form.		 *)
(*									 *)
(* For convenience, the function mk_mk_pred also returns the variables	 *)
(* R and P.								 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let mk_mk_pred =                                                      *)
(*     let chk p st = \x. (p x => x | failwith st) in                    *)
(*     let ckb = chk (\t. type_of t = ":bool") `pattern not boolean` in  *)
(*     let ckv = chk is_var `non-variable in pattern` in                 *)
(*     let ckp = chk is_var `non-variable parameter` in                  *)
(*     let itfn ck st v l = (mem (ck v) l => failwith st | v.l) in       *)
(*     let cka = C (itlist (itfn ckv `duplicate argument in pattern`))   *)
(*                 [] in                                                 *)
(*     let ckpa=C (itlist (itfn ckp `duplicate variable in parameters`)) *)
(*                [] in                                                  *)
(*     \(pat,ps,vs).                                                     *)
(*       let R,args = (ckv # cka) (strip_comb(ckb pat)) in               *)
(*       if (exists ($not o C mem args) (ckpa ps)) then                  *)
(*          failwith `spurious parameter variable` else                  *)
(*       let P = variant vs (mk_predv (subtract args ps)) in             *)
(*       let checkhyp = checkfilter ps args in                           *)
(*           R,P,\tm.                                                    *)
(*            let f,as = strip_comb tm in                                *)
(*            if (f = R) then                                            *)
(*              list_mk_comb (P, checkhyp as) else checkside R tm;;      *)
(* --------------------------------------------------------------------- *)

fun MK_MK_PRED_ERR s = IND_DEF_ERR{function = "mk_mk_pred",message = s};

local
val ERR1 = MK_MK_PRED_ERR "pattern not boolean"
val ERR2 = MK_MK_PRED_ERR "non-variable in pattern"
val ERR3 = MK_MK_PRED_ERR "non-variable parameter"
val ERR4 = MK_MK_PRED_ERR "duplicate argument in pattern"
val ERR5 = MK_MK_PRED_ERR "duplicate variable in parameters"
val ERR6 = MK_MK_PRED_ERR "spurious parameter variable"
fun chk p e x = if (p x) then x else raise e
val ckb = chk (fn t => type_of t = Type.bool) ERR1
val ckv = chk is_var ERR2
val ckp = chk is_var ERR3
fun itfn ck e v l = if (mem (ck v) l) 
                    then raise e
                    else (v::l)
val cka = C (itlist (itfn ckv ERR4)) []
val ckpa = C (itlist (itfn ckp ERR5)) []
in
fun mk_mk_pred (pat,ps,vs) =
   let val (R,args) = (ckv ## cka) (strip_comb(ckb pat)) 
   in
   if (exists ((op not) o (C mem args)) (ckpa ps)) 
   then raise ERR6
   else let val P = variant vs (mk_predv (set_diff args ps))
            val checkhyp = checkfilter ps args 
        in
        (R,P, fn tm => let val (f,a) = strip_comb tm 
                       in if (f = R) 
                          then list_mk_comb(P,checkhyp a) 
                          else checkside R tm
                       end)
        end
   end
end;

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION : make_rule 					 *)
(* 									 *)
(* The function make_rule takes a user-supplied rule specification:	 *)
(*									 *)
(*   (as, ss, c)   							 *)
(*									 *)
(* where as are the assumptions, ss are the side conditions and c is the *)
(* conclusion, and generates the logical representation of the assertion *)
(* that the predicate P closed under the rule.  The variable ps is the	 *)
(* global paramter list, and the function mkp is the mapping from	 *)
(* membership assertions:						 *)
(*									 *)
(*   R a1 ... an   							 *)
(*									 *)
(* which occur in as and as c, to membership assertions:		 *)
(*									 *)
(*   P ai ... aj							 *)
(*									 *)
(* where the global parameters ps are eliminated.			 *)
(*									 *)
(* For an axiom of the form:						 *)
(*									 *)
(*     ([],[],c)   the result is:  !ps. !xs. c"				 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let make_rule (P,R,ps,mkp) (as,c) =                                   *)
(*     if (not(fst(strip_comb c)) = R) then                              *)
(*        failwith `ill-formed rule conclusion` else                     *)
(*     let getvs tm = subtract (frees tm) (P.R.ps) in                    *)
(*     let con = mkp c in                                                *)
(*     if (null as) then                                                 *)
(*         list_mk_forall(getvs con,con) else                            *)
(*         let asm = list_mk_conj (map mkp as) in                        *)
(*         let pvs = getvs asm and cvs = getvs con in                    *)
(*         let qcon = list_mk_forall(subtract cvs pvs, con) in           *)
(*         let qasm = list_mk_exists(subtract pvs cvs, asm) in           *)
(*         let avs = intersect pvs cvs in                                *)
(*             list_mk_forall(avs,mk_imp(qasm,qcon));;                   *)
(* --------------------------------------------------------------------- *)

fun make_rule (P,R,ps,mkp) (ass,c) =
   if (not (fst(strip_comb c) = R)) 
   then raise IND_DEF_ERR{function = "make_rule", 
                          message = "ill-formed rule conclusion"}
   else let fun getvs tm = set_diff (hol88Lib.frees tm) (P::(R::ps))
            val con = mkp c 
        in
        if (null ass) 
        then list_mk_forall(getvs con,con)
        else let val asm = list_mk_conj (map mkp ass)
                 val pvs = getvs asm
                 val cvs = getvs con
                 val qcon = list_mk_forall(set_diff cvs pvs,con)
                 val qasm = list_mk_exists(set_diff pvs cvs,asm)
                 val avs = intersect pvs cvs 
             in
             list_mk_forall(avs,mk_imp{ant=qasm,conseq=qcon})
             end
        end;

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION : make_definition					 *)
(*									 *)
(* The function make_definition creates an appropriate non-recursive	 *)
(* defining equation for the user-specified inducively-defined predicate *)
(* described by the pattern pat, the parameter list ps and the rule list *)
(* rules. (See below for a description of the required format of these	 *)
(* input values).  Error checking of the user input is also done here.	 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let make_definition (pat,ps) rules =                                  *)
(*     let vs = freesl (flat (map (\(x,y). y.x) rules)) in               *)
(*     let R,P,mkp = mk_mk_pred (pat,ps,vs) in                           *)
(*     let frules = map ((flat o map conjuncts) # I) rules in            *)
(*     let crules = list_mk_conj(map (make_rule (P,R,ps,mkp)) frules) in *)
(*     let right = mk_forall(P,mk_imp (crules,mkp pat)) in               *)
(*     let eqn = mk_eq(pat,right) in                                     *)
(*     let args = subtract (snd(strip_comb pat)) ps in                   *)
(*         list_mk_forall(ps @ args, eqn);;                              *)
(* --------------------------------------------------------------------- *)

fun make_definition (pat,ps) rules =
   let val rules = map (fn {hypotheses,side_conditions,conclusion} =>
                              ((hypotheses@side_conditions),conclusion))
                       rules
       val vs = hol88Lib.freesl (flatten (map (fn (x,y) => (y::x)) rules)) 
       val (R,P,mkp) = mk_mk_pred(pat,ps,vs)
       val frules = map ((flatten o map strip_conj) ## I) rules
       val crules = list_mk_conj(map (make_rule (P,R,ps,mkp)) frules)
       val right = mk_forall{Bvar=P,Body=mk_imp{ant=crules,conseq=mkp pat}}
       val eqn = mk_eq{lhs=pat,rhs=right}
       val args = set_diff (snd(strip_comb pat)) ps 
   in list_mk_forall(ps @ args,eqn)
   end;

(* --------------------------------------------------------------------- *)
(* derive_induction : derive rule induction from the definition of an 	 *)
(* inductively-defined predicate PRED.					 *)
(*									 *)
(* The input, def, has the form:					 *)
(*									 *)
(*    "!v1...vn. PRED v1 ... vn = !REL. R[REL] ==> REL vi ... vj"	 *)
(*									 *)
(* where {vi,...,vj} is a subset of {v1,...,vn} and R[REL] states that	 *)
(* REL is closed under some set of rules R.				 *)
(*									 *)
(* The output is the rule induction theorem:				 *)
(*									 *)
(*    def |- !vk...vl. 							 *)
(*           !REL. R[REL] ==> !vi...vj. PRED v1 ... vn ==> REL vi ... vj *)
(*									 *)
(* where {vk,...,vl} = {v1,...,vn} - {vi,...,vj}			 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let derive_induction def =                                            *)
(*     let vs,(left,right) = (I # dest_eq) (strip_forall def) in         *)
(*     let rel,(As,Con) = (I # dest_imp) (dest_forall right) in          *)
(*     let rvs = snd(strip_comb Con) in                                  *)
(*     let th1 = UNDISCH (fst(EQ_IMP_RULE (SPECL vs (ASSUME def)))) in   *)
(*     let th2 = GENL rvs (DISCH left (UNDISCH (SPEC rel th1))) in       *)
(*         GENL (subtract vs rvs) (GEN rel (DISCH As th2));;             *)
(* --------------------------------------------------------------------- *)

fun derive_induction def =
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_forall def)
       val {Bvar,Body} = dest_forall rhs
       val {ant,conseq} = dest_imp Body
       val rvs = snd(strip_comb conseq)
       val th1 = UNDISCH (fst(EQ_IMP_RULE (SPECL vs (ASSUME def))))
       val th2 = GENL rvs (DISCH lhs (UNDISCH (SPEC Bvar th1))) 
   in
   GENL (set_diff vs rvs) (GEN Bvar (DISCH ant th2))
   end;

(* --------------------------------------------------------------------- *)
(* abbreviate : use the non-recursive definition of an inductively 	 *)
(* defined predicate P to abbreviate an application of P.		 *)
(*									 *)
(* The input term def has the form:					 *)
(*									 *)
(*   "!v1...vn. PRED v1 ... vn = !REL. R[REL] ==> REL vi ... vj"	 *)
(*									 *)
(* The input theorem th has the form:					 *)
(*									 *)
(*   |- !REL. R[REL] ==> REL x1 ... xn					 *)
(*									 *)
(* The result is:							 *)
(*									 *)
(*   def |- PRED x1 ... xn						 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let usedef (rvs,th) =                                                 *)
(*     let left,right = EQ_IMP_RULE th in                                *)
(*     let ante,v = (I # (fst o dest_forall)) (dest_imp (concl left)) in *)
(*     let lth=GENL rvs (DISCH ante(UNDISCH(SPEC v (UNDISCH left)))) in  *)
(*     let as tm = SPECL (snd(strip_comb tm)) lth in                     *)
(*     let rth = GENL rvs right in                                       *)
(*     let ab th =                                                       *)
(*         let ts = snd(strip_comb(rand(snd(dest_forall(concl th))))) in *)
(* 	     MP (SPECL ts rth) th in                                     *)
(*         (ab,as);;                                                     *)
(* --------------------------------------------------------------------- *)

fun usedef (rvs,th) =
   let val (left,right) = EQ_IMP_RULE th 
       val {ant,conseq} = dest_imp (concl left)
       val {Bvar,...} = dest_forall conseq
       val lth = GENL rvs (DISCH ant (UNDISCH(SPEC Bvar (UNDISCH left)))) 
       fun ass tm = SPECL (snd(strip_comb tm)) lth
       val rth = GENL rvs right
       fun ab th =
            let val ts = snd(strip_comb(rand(#Body(dest_forall(concl th))))) 
            in MP (SPECL ts rth) th 
            end
   in (ab,ass) 
   end;

(* --------------------------------------------------------------------- *)
(* eximp : forward proof rule for existentially quantifying variables in *)
(* both the antecedent and consequent of an implication.		 *)
(*									 *)
(* A call to:  								 *)
(*   									 *)
(*    eximp ["v1",...,"vn"]   A |- P ==> Q				 *)
(*									 *)
(* returns a pair (tm,th) where:					 *)
(*									 *)
(*    tm = "?v1...vn. P"   and   th = A,tm |- ?v1...vn. Q		 *)
(*									 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let eximp =                                                           *)
(*     let exfn v th = EXISTS(mk_exists(v,concl th),v)th in              *)
(*     let chfn v (a,th) =                                               *)
(*         let tm = mk_exists(v,a) in (tm,CHOOSE (v,ASSUME tm) th) in    *)
(*     \vs th. let A,C = dest_imp(concl th) in                           *)
(*                 itlist chfn vs (A,itlist exfn vs (UNDISCH th));;      *)
(* --------------------------------------------------------------------- *)

local
fun exfn v th = EXISTS(mk_exists{Bvar=v,Body=concl th},v) th
fun chfn v (a,th) =
   let val tm = mk_exists{Bvar=v,Body=a} 
   in
   (tm,CHOOSE (v,ASSUME tm) th) 
   end
in
fun eximp vs th =
   let val {ant,conseq} = dest_imp(concl th) 
   in
   itlist chfn vs (ant,itlist exfn vs (UNDISCH th))
   end
end;

(* --------------------------------------------------------------------- *)
(* A rule has the form:							 *)
(*									 *)
(* |- !x1...xn. 							 *)
(*     <side-conditions> ==> 						 *)
(*     (?v1...vn. <assumptions>) ==> !z1...zn. <conclusion>   		 *)
(*									 *)
(* Modified to:								 *)
(*									 *)
(* |- !x1...xn. (?v1...vn. <assumptions and side conditions>) 		 *)
(*		==>							 *)
(*              !z1...zn. <conclusion>					 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let derive_rule =                                                     *)
(*     let check v = assert ($not o (free_in v)) # assert (free_in v) in *)
(*     \rel (ab,as) th.                                                  *)
(*       let ([R],xs,body) = (I # strip_forall) (dest_thm th) in         *)
(*       let thm1 = SPECL xs th in                                       *)
(*       (let ante,cvs,con = (I # strip_forall) (dest_imp body) in       *)
(*        let evs,asms = (I # conjuncts) (strip_exists ante) in          *)
(*        let mfn tm=(free_in rel tm=>as tm | DISCH_ALL(ASSUME tm)) in   *)
(*        let ths = map mfn asms in                                      *)
(*        let A1,th1 = eximp evs (end_itlist IMP_CONJ ths) in            *)
(*        let th3 = ab (GEN rel (DISCH R (SPECL cvs (MP thm1 th1)))) in  *)
(*  	   GENL xs (DISCH A1 (GENL cvs th3))) ?                          *)
(*       GENL xs (ab (GEN rel (DISCH R thm1)));;                         *)
(* --------------------------------------------------------------------- *)

local
fun check v = (assert ((op not) o (free_in v)))##(assert (free_in v))
in
fun derive_rule rel (ab,ass) th =
   let val ([R],(xs,body)) = (I ## strip_forall) (dest_thm th)
       val thm1 = SPECL xs th
   in
      let val {ant,conseq} = dest_imp body
          val (cvs,con) = strip_forall conseq
          val (evs,asms) = (I ## strip_conj) (strip_exists ant)
          fun mfn tm = if (free_in rel tm) 
                       then ass tm 
                       else DISCH_ALL(ASSUME tm)
          val ths = map mfn asms
          val (A1,th1) = eximp evs (end_itlist IMP_CONJ ths)
          val th3 = ab (GEN rel (DISCH R (SPECL cvs (MP thm1 th1)))) 
      in
      GENL xs (DISCH A1 (GENL cvs th3))
      end
      handle _ => GENL xs (ab (GEN rel (DISCH R thm1)))
   end
end;

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION : derive_rules.					 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* let derive_rules def =                                                *)
(*     let vs,(left,right) = (I # dest_eq) (strip_forall def) in         *)
(*     let rel,(a,c) = (I # dest_imp) (dest_forall right) in             *)
(*     let rvs = subtract vs (snd(strip_comb c)) in                      *)
(*     let ab,as = usedef (snd(strip_comb c),SPECL vs (ASSUME def)) in   *)
(*     let ths = CONJUNCTS (ASSUME a) in                                 *)
(*     let rules = map (GENL rvs o derive_rule rel (ab,as)) ths in       *)
(*         LIST_CONJ rules;;                                             *)
(* --------------------------------------------------------------------- *)

fun derive_rules def = 
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_forall def)
       val {Bvar,Body} = dest_forall rhs
       val {ant,conseq} = dest_imp Body
       val tms = snd(strip_comb conseq)
       val (ab,ass) = usedef (tms,SPECL vs (ASSUME def))
       val ths = CONJUNCTS (ASSUME ant)
       val rules = map (GENL(set_diff vs tms) o derive_rule Bvar (ab,ass)) ths 
   in LIST_CONJ rules
   end;
    
fun prove_inductive_set_exists patt rules = 
   let val def = make_definition patt rules
       val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_forall def)
       val (R,args) = strip_comb lhs
       val thm1 = CONJ (derive_rules def) (derive_induction def)
       val eth = EXISTS(mk_exists{Bvar=R,Body=concl thm1},R) thm1
       val lam = list_mk_abs(vs,rhs)
       val bth = GENL vs (LIST_BETA_CONV (list_mk_comb(lam,vs)))
       val deth = EXISTS (mk_exists{Bvar=R,Body=def},lam) bth 
   in CHOOSE (R, deth) eth
   end;

(* --------------------------------------------------------------------- *)
(* new_inductive_definition : make a new inductive definition.		 *)
(* --------------------------------------------------------------------- *)

fun new_inductive_definition{name,fixity,patt,rules} =
   let val eth = prove_inductive_set_exists patt rules 
       val cname = #Name(dest_var(#Bvar(dest_exists(concl eth))))
       val (rules,ind) = 
        CONJ_PAIR(new_specification{name=name, sat_thm=eth,
                                    consts=[{const_name=cname,fixity=fixity}]})
   in {desc = CONJUNCTS rules, induction_thm = ind}
   end;

(* ===================================================================== *)
(* STRONGER FORM OF INDUCTION.						 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION : simp_axiom					*)
(*									*)
(* This function takes an axiom of the form				*)
(*									*)
(*    |- !xs. REL ps <args>						*)
(*									*)
(* and a term of the form						*)
(*									*)
(*    !xs. (\vs. REL ps vs /\ P vs) <args>				*)
(*									*)
(* and proves that							*)
(*									*)
(*    |- (!xs. P <args>) ==> !xs. (\vs. REL ps vs /\ P vs) <args>	*)
(*									*)
(* That is, simp_axiom essentially beta-reduces the input term, and 	*)
(* drops the redundant conjunct "REL ps xs", this holding merely by 	*)
(* virtue of the axiom being true.					*)
(* --------------------------------------------------------------------- *)

fun simp_axiom (ax,tm) =
   let val (vs,red) = strip_forall tm
       val bth = LIST_BETA_CONV red
       val asm = list_mk_forall(vs,rand(rand(concl bth)))
       val th1 = SPECL vs (ASSUME asm)
       val th2 = EQ_MP (SYM bth) (CONJ (SPECL vs ax) th1)
   in DISCH asm (GENL vs th2)
   end

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCION : reduce_asm					*)
(*									*)
(* The term asm is expected to be the antecedent of a rule in the form:	*)
(* 									*)
(*   "?zs. ... /\ (\vs. REL ps vs /\ P vs) <args> /\ ..."		*)
(* 									*)
(* in which applications of the supplied parameter fn:			*)
(*									*)
(*   "(\vs. REL ps vs /\ P vs)"						*)
(* 									*)
(* appear as conjuncts (possibly among some side conditions).  The 	*)
(* function reduce_asm beta-reduces these conjuncts and flattens the 	*)
(* resulting conjunction of terms.  The result is the theorem:		*)
(*									*)
(*   |- asm ==> ?zs. ... /\ REL ps <args> /\ P <args> /\ ...		*)
(*									*)
(* --------------------------------------------------------------------- *)
local 
fun reduce Fn tm =
   let val {conj1,conj2} = dest_conj tm
       val imp = reduce Fn conj2
   in
   if (fst(strip_comb conj1) = Fn) 
   then let val (t1,t2)=CONJ_PAIR(EQ_MP (LIST_BETA_CONV conj1) (ASSUME conj1))
            val thm1 = CONJ t1 (CONJ t2 (UNDISCH imp))
            val asm = mk_conj{conj1=conj1,conj2=rand(rator(concl imp))}
            val (h1,h2) = CONJ_PAIR (ASSUME asm) 
        in DISCH asm (PROVE_HYP h1 (PROVE_HYP h2 thm1)) 
        end
   else IMP_CONJ (DISCH conj1 (ASSUME conj1)) imp
   end
   handle _ => if (fst(strip_comb tm) = Fn)
               then fst(EQ_IMP_RULE(LIST_BETA_CONV tm)) 
               else DISCH tm (ASSUME tm) 
in
fun reduce_asm Fn asm =
   let val (vs,body) = strip_exists asm 
   in itlist EXISTS_IMP vs (reduce Fn body)
   end
end;


fun prove_asm P tm =
   let fun test t = not(fst(strip_comb(concl t)) = P)
       val (vs,body) = strip_exists tm
       val newc = LIST_CONJ(filter test (CONJUNCTS(ASSUME body)))
   in
   itlist EXISTS_IMP vs (DISCH body newc)
   end;


fun simp_concl rul tm =
   let val (vs,{ant,conseq}) = (I ## dest_imp) (strip_forall tm)
       val srul = SPECL vs rul
       val (cvs,{conj2,...}) = (I ## dest_conj) (strip_forall conseq)
       val simpl = prove_asm (fst(strip_comb conj2)) ant
       val thm1 = SPECL cvs (UNDISCH (IMP_TRANS simpl srul))
       val newasm=list_mk_forall (vs,mk_imp{ant=ant,
                                            conseq=list_mk_forall (cvs,conj2)})
       val thm2=CONJ thm1 (SPECL cvs (UNDISCH (SPECL vs (ASSUME newasm))))
   in DISCH newasm (GENL vs (DISCH ant (GENL cvs thm2)))
   end;


fun simp_rule (rul,tm) = 
   let val (vs,{ant,conseq}) = (I ## dest_imp) (strip_forall tm)
       val (cvs,red) = strip_forall conseq
       val bth = itlist FORALL_EQ cvs (LIST_BETA_CONV red)
       val basm = reduce_asm (fst(strip_comb red)) ant
       val asm = list_mk_forall(vs,mk_imp{ant=rand(concl basm),
                                          conseq=rand(concl bth)})
       val thm1 = UNDISCH (IMP_TRANS basm (SPECL vs (ASSUME asm)))
       val thm2 = DISCH asm (GENL vs (DISCH ant (EQ_MP (SYM bth) thm1)))
       val thm3 = simp_concl rul (rand(rator(concl thm2))) 
   in IMP_TRANS thm3 thm2
   end;


fun simp p = simp_rule p handle _ => simp_axiom p;


fun last [a] = a 
  | last (_::rst) = last rst
  | last [] = raise IND_DEF_ERR{function = "last",
                                message = "empty list has no last element!"};

fun butlast [_] = []
  | butlast (h::t) = h::(butlast t)
  | butlast [] = raise IND_DEF_ERR{function = "butlast",
                                   message = "empty list"};


fun derive_strong_induction (rules,ind) = 
   let val (vs,{conseq,...}) = (I ## dest_imp) (strip_forall (concl ind))
       val srules = map (SPECL (butlast vs)) rules
       val (cvs,{ant=rel,conseq=pred}) = (I ## dest_imp) (strip_forall conseq)
       val newp = list_mk_abs(cvs,mk_conj{conj1=rel,conj2=pred})
       val (pvar,args) = strip_comb pred
       val ith = INST [{redex=pvar,residue=newp}] (SPECL vs ind)
       val {ant,conseq=co} = dest_imp (concl ith)
       val bth = LIST_BETA_CONV (list_mk_comb(newp,args))
       val sth = CONJUNCT2 (EQ_MP bth (UNDISCH (SPECL args (ASSUME co))))
       val thm1 = IMP_TRANS ith (DISCH co (GENL args (DISCH rel sth)))
       val ths = map simp (combine (srules,strip_conj ant)) 
   in
   GENL vs (IMP_TRANS (end_itlist IMP_CONJ ths) thm1)
   end
   handle _ => raise IND_DEF_ERR{function = "derive_strong_induction_thm",
                                 message = ""};


(* ===================================================================== *)
(* RULE INDUCTION 							 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Internal function: TACF	 					 *)
(*									 *)
(* TACF is used to generate the subgoals for each case in an inductive 	 *)
(* proof.  The argument tm is formula which states one case in the 	 *)
(* the induction. In general, this will take one of the forms:		 *)
(*									 *)
(*   (1) no side condition, no assumptions:				 *)
(*									 *)
(*       tm = !x1...xn. P x1 ... xn					 *)
(*									 *)
(*   (2) side condition ?y1...ym.C, no assumptions:			 *)
(*									 *)
(*       tm = !xs. (?y1...ym.C) ==> !zs. P xz1 ... xz(n+o)		 *)
(*									 *)
(*   (3) assumptions ?y1...ym.A, no side condition:			 *)
(*									 *)
(*       tm = !xs. (?y1...ym.A) ==> !zs. P xz1 ... xz(n+o)		 *)
(*									 *)
(*   (4) assumptions ?y1...ym.A, and side condition (?y1...ym.C):	 *)
(*									 *)
(*       tm = !xs. ?zs.(?y1...ym.A) /\ (?w1...wm.C) ==> 		 *)
(*		  !zs. P xz1 ... xz(n+o)				 *)
(*									 *)
(*									 *)
(* 2--4 now merged into:						 *)
(*      								 *)
(*       tm = !xs. ?zs. A /\ ... /\ C /\ ... /\ A ==>			 *)
(*	          !ys. P ...						 *)
(*									 *)
(* TACF applied to each these terms to construct a parameterized tactic  *)
(* which will be used to further break these terms into subgoals.  The   *)
(* resulting tactic takes a variable name x and a user supplied theorem  *)
(* continuation ttac.  For a base case, like case 1 above, the resulting *)
(* tactic just throws these parameters away and passes the goal on 	 *)
(* unchanged (i.e. \x ttac. ALL_TAC).  For a step case, like case 2, the *)
(* tactic applies GTAC x as many times as required.  It then strips off  *)
(* the induction hypotheses and applies ttac to each one.  For example,  *)
(* if tac is the tactic generated by:					 *)
(*									 *)
(*    TACF "!n. P n ==> P(SUC n)" "x:num" ASSUME_TAC			 *)
(*									 *)
(* then applying tac to the goal A,"!n. P[n] ==> P[SUC n] has the same 	 *)
(* effect as applying:							 *)
(*									 *)
(*    GTAC "x:num" THEN DISCH_THEN ASSUME_TAC				 *)
(*									 *)
(* TACF is a strictly local function, used only to define TACS, below.	 *)
(*									 *)
(* --------------------------------------------------------------------- *)

fun MK_CONJ_THEN Fn tm =
   let val {conj1,conj2} = dest_conj tm
       val tcl1 = if (fst(strip_comb conj1) = Fn) 
                  then fn t1 => fn t2 => t1 
                  else fn t1 => fn t2 => t2
       val tcl2 = MK_CONJ_THEN Fn conj2
   in
   fn ttac1 => fn ttac2 => 
     CONJUNCTS_THEN2 (tcl1 ttac1 ttac2) (tcl2 ttac1 ttac2)
   end
   handle _ => if (fst(strip_comb tm) = Fn) 
               then K 
               else C K;

fun MK_CHOOSE_THEN Fn [] body = MK_CONJ_THEN Fn body 
  | MK_CHOOSE_THEN Fn (_::t) body =
      let val tcl = MK_CHOOSE_THEN Fn t body 
      in
      fn ttac1 => fn ttac2 => CHOOSE_THEN (tcl ttac1 ttac2) 
      end;

fun MK_THEN Fn tm =
   let val (vs,body) = strip_exists tm 
   in
   if (free_in Fn body)
   then MK_CHOOSE_THEN Fn vs body 
   else fn ttac1 => fn ttac2 => ttac2 
   end;

fun TACF Fn tm = 
   let val (vs,body) = strip_forall tm 
   in
   if (is_imp body) 
   then let val TTAC = MK_THEN Fn (#ant(dest_imp body)) 
        in
        fn ttac1 => fn ttac2 =>
          REPEAT GEN_TAC THEN DISCH_THEN (TTAC ttac1 ttac2) 
        end
   else fn ttac1 => fn ttac2 => ALL_TAC 
   end;

(* --------------------------------------------------------------------- *)
(* Internal function: TACS						 *)
(*									 *)
(* TACS uses TACF to generate a paramterized list of tactics, one for    *)
(* each conjunct in the hypothesis of an induction theorem.		 *)
(*									 *)
(* For example, if tm is the hypothesis of the induction thoerem for the *)
(* natural numbers---i.e. if:						 *)
(*									 *)
(*   tm = "P 0 /\ (!n. P n ==> P(SUC n))"				 *)
(*									 *)
(* then TACS tm yields the paremterized list of tactics:		 *)
(*									 *)
(*   \x ttac. [TACF "P 0" x ttac; TACF "!n. P n ==> P(SUC n)" x ttac]    *)
(*									 *)
(* TACS is a strictly local function, used only in INDUCT_THEN.		 *)
(*									 *)
(* --------------------------------------------------------------------- *)
(* Tricky coding, fall back on the original syntax *)
fun TACS Fn tm = 
   let val (cf,csf) = (TACF Fn ## TACS Fn) (Psyntax.dest_conj tm) 
                      handle _ => (TACF Fn tm, fn x => fn y => [])
   in fn ttac1 => fn ttac2 => ((cf ttac1 ttac2) :: (csf ttac1 ttac2))
   end;


(* --------------------------------------------------------------------- *)
(* Internal function RED_WHERE.						 *)
(*									 *)
(* Given the arguments "f" and "tm[f]", this function produces a 	 *)
(* conversion that will apply LIST_BETA_CONV to its argument at all	 *)
(* top-level subterms that correspond to occurrences of f (bottom-up).	 *)
(*									 *)
(* Optimized for induction special form.				 *)
(*									 *)
(* --------------------------------------------------------------------- *)

local
val AND = --`/\`--
val IMP = --`==>`--
fun mkred Fn (c::cs) =
   let val cfn = if (fst(strip_comb c) = Fn) 
                 then LIST_BETA_CONV 
                 else REFL 
   in
   if (null cs) 
   then cfn 
   else let val rest = mkred Fn cs 
        in
        fn tm => let val {conj1,conj2} = dest_conj tm
                 in
                 MK_COMB(AP_TERM AND (cfn conj1),rest conj2)
                 end
        end
   end
in
fun RED_CASE Fn pat =
   let val bdy = snd(strip_forall pat) 
   in
   if (is_imp bdy) 
   then let val {ant,...} = dest_imp bdy
            val hyps = strip_conj(snd(strip_exists ant))
            val redf = mkred Fn hyps 
        in fn tm =>
             let val (vs,{ant,conseq}) = (I##dest_imp) (strip_forall tm)
                 val (cvs,red) = strip_forall conseq
                 val th1 = itlist FORALL_EQ cvs (LIST_BETA_CONV red)
                 val (evs,hyp) = strip_exists ant
                 val th2 = itlist EXISTS_EQ evs (redf hyp) 
             in itlist FORALL_EQ  vs  (MK_COMB((AP_TERM IMP th2),th1))
             end
        end
   else fn tm => 
          let val (vs,con) = strip_forall tm 
          in itlist FORALL_EQ vs (LIST_BETA_CONV con)
          end
   end
end;


local
val AND = --`/\`--
in
fun APPLY_CASE [f] tm = f tm
  | APPLY_CASE (f::fs) tm =
     let val {conj1,conj2} = dest_conj tm 
     in MK_COMB (AP_TERM AND (f conj1),APPLY_CASE fs conj2) 
     end
end;

local
val IMP = --`==>`--
in
fun RED_WHERE Fn body =
   let val rfns = map (RED_CASE Fn) (strip_conj (#ant(dest_imp body)))
   in fn stm => 
        let val {ant,conseq} = dest_imp stm
            val hthm = APPLY_CASE rfns ant
            val cthm = RAND_CONV LIST_BETA_CONV conseq
        in MK_COMB(AP_TERM IMP hthm,cthm)
        end
   end
end;

fun residue_assoc itm =
   let fun assc ([]:(term,term) subst) = NONE
         | assc ({redex,residue}::rst) = 
             if (itm = residue)
             then SOME redex
             else assc rst
   in assc
   end;
(* lookup on the residue, then take the redex *)
fun is_param icvs slis arg =
   let val vl = case (residue_assoc arg slis)
                  of (SOME x) => x
                   | NONE => arg
   in mem vl icvs
   end;

(* --------------------------------------------------------------------- *)
(* RULE_INDUCT_THEN : general rule induction tactic.			 *)
(*									 *)
(* --------------------------------------------------------------------- *)

fun RULE_INDUCT_THEN_ERR s = IND_DEF_ERR{function = "RULE_INDUCT_THEN",
                                         message = s};

local
val ERR1 = RULE_INDUCT_THEN_ERR "inappropriate goal"
val ERR2 = RULE_INDUCT_THEN_ERR "ill-formed rule induction theorem"
fun pair x y = (x,y)
in
fun RULE_INDUCT_THEN th =
   let val (vs,{ant,conseq}) = (I ## dest_imp) (strip_forall (concl th))
       val (cvs,cncl) = strip_forall conseq
       val thm = DISCH ant (SPECL cvs(UNDISCH(SPECL vs th)))
       val pvar = genvar (type_of (last vs))
       val sthm = INST [{redex=last vs, residue=pvar}] thm
       val RED = RED_WHERE (last vs) (mk_imp{ant=ant,conseq=cncl})
       val tacs = TACS (last vs) ant 
   in
   fn ttac1 => fn ttac2 => fn (A,g) =>
     let val (gvs,body) = strip_forall g
         val (theta as (slis,ilis)) = match_term (rator cncl) (rator body)
         val sith = INST_TY_TERM theta sthm
         val largs = snd(strip_comb (rand(rator body)))
         val icvs = map (inst ilis) cvs
         val params = filter (is_param icvs slis) largs
         val lam = list_mk_abs(params,rand body)
         val spth = INST [{redex=inst ilis pvar,residue=lam}] sith
         val spec = GENL gvs (UNDISCH (CONV_RULE RED spth))
         val subgls = map (pair A) (strip_conj (hd(hyp spec)))
         fun tactc g = (subgls,fn ths => PROVE_HYP (LIST_CONJ ths) spec) 
     in (tactc THENL (tacs ttac1 ttac2)) (A,g)
     end
     handle _ => raise ERR1
   end
   handle _ => raise ERR2
end;

(* ===================================================================== *)
(* TACTICS FROM THEOREMS THAT STATE RULES.			 	 *)
(* ===================================================================== *)


fun axiom_tac th :tactic = fn (A,g) =>
   let val (vs,body) = strip_forall g
       val instl = match_term (concl th) body 
   in
   ([], K (itlist ADD_ASSUM A (GENL vs (INST_TY_TERM instl th))))
   end
   handle _ => raise IND_DEF_ERR{function = "axiom_tac", 
                                 message = "axiom does not match goal"};

(* --------------------------------------------------------------------- *)
(* prove_conj								 *)
(*									 *)
(* HOL88 code:                                                           *)
(*									 *)
(* letrec prove_conj ths tm =                                            *)
(*    uncurry CONJ ((prove_conj ths # prove_conj ths) (dest_conj tm)) ?  *)
(*    find (curry $= tm o concl) ths;;                                   *)
(* --------------------------------------------------------------------- *)

fun prove_conj ths tm = 
   let val {conj1,conj2} = dest_conj tm
       val f = prove_conj ths
   in CONJ (f conj1) (f conj2)
   end
   handle _ => first (curry (op =) tm o concl) ths;
 
(* --------------------------------------------------------------------- *)
(* RULE_TAC								 *)
(*									 *)
(* --------------------------------------------------------------------- *)


local fun RULE_TAC_ERR s = IND_DEF_ERR{function="RULE_TAC",message=s}
      val ERR1 = RULE_TAC_ERR "rule does not match goal"
      val ERR2 = RULE_TAC_ERR "ill-formed input theorem"
      fun mkg A vs c = (A,list_mk_forall(vs,c))
in
fun RULE_TAC th =
   let val (vs,rule) = strip_forall(concl th) handle _ => raise ERR2
   in
   let val {ant,conseq} = dest_imp rule
       val (cvs,cncl) = strip_forall conseq
       val ith = DISCH ant (SPECL cvs (UNDISCH (SPECL vs th))) 
   in fn (A,g) =>
         let val (gvs,body) = strip_forall g
             val (slis,ilis) = match_term cncl body
             val th1 = INST_TY_TERM (slis,ilis) ith
             val svs = hol88Lib.freesl (map (subst slis o inst ilis) vs)
             val nvs = intersect gvs svs
             val ante = #ant(dest_imp(concl th1))
             val newgs = map (mkg A nvs) (strip_conj ante) 
         in (newgs, 
             fn thl => let val ths = map (SPECL nvs o ASSUME o snd) newgs
                           val th2 = GENL gvs(MP th1 (prove_conj ths ante)) 
                       in itlist PROVE_HYP thl th2
                       end)
         end
         handle _ => raise ERR1
    end
    handle _ => axiom_tac (SPECL vs th) 
   end 
end;


(* =====================================================================*)
(* REDUCTION OF A CONJUNCTION OF EQUATIONS.				*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* INTERNAL FUNCTION : reduce 						*)
(* 									*)
(* A call to 								*)
(*									*)
(*   reduce [v1;...;vn] ths [] []					*)
(*									*)
(* reduces the list of theorems ths to an equivalent list by removing 	*)
(* theorems of the form |- vi = ti where vi does not occur free in ti,  *)
(* first using this equation to substitute ti for vi in all the other	*)
(* theorems. The theorems in ths are processed sequentially, so for 	*)
(* example:								*)
(*									*)
(*   reduce [a;b] [|- a=1; |- b=a+2; |- c=a+b] [] []			*)
(*									*)
(* is reduced in the following stages:					*)
(*									*)
(*   [|- a=1; |- b=a+2; |- c=a+b]					*)
(*   									*)
(*   ===> [|- b=1+2; |- c=1+b]      (by the substitution [1/a])		*)
(*   ===> [|- c=1+(1+2)]            (by the substitution [1+2/b])	*)
(*									*)
(* The function returns the reduced list of theorems, paired with a list *)
(* of the substitutions that were made, in reverse order.  The result 	*)
(* for the above example would be [|- c = 1+(1+2)],[("1+2",b);("1",a)].	*)
(* ---------------------------------------------------------------------*)

fun subst_in_subst theta =
  map (fn {redex,residue} => {redex=redex, residue = subst theta residue});

fun subst_assoc tm =
   let fun assc [] = NONE
         | assc ({redex,residue}::rst) = 
            if (tm = redex)
            then (SOME residue)
            else assc rst
   in assc
   end;

local val ERR = IND_DEF_ERR{function="",message=""}
in
fun reduce vs ths res subf =
   if (null ths) 
   then (rev res, subf) 
   else let val {lhs,rhs} = dest_eq(concl(hd ths))
            val (sth,pai) = if (mem lhs vs)
                            then (hd ths,{redex=lhs,residue=rhs})
                            else if (mem rhs vs)
                                 then (SYM(hd ths),{redex=rhs,residue=lhs})
                                 else raise ERR
        in if (free_in (#redex pai) (#residue pai))
           then raise ERR
           else let val sfn = map (SUBS [sth])
                    val ssfn = subst_in_subst [pai]
                in reduce vs (sfn (tl ths)) (sfn res) (pai::ssfn subf)
                end
        end
        handle _ => reduce vs (tl ths) (hd ths::res) subf
end;


(* --------------------------------------------------------------------- *)
(* REDUCE : simplify an existentially quantified conjuction by		*)
(* eliminating conjuncts of the form |- v=t, where v is among the 	*)
(* quantified variables and v does not appear free in t. For example 	*)
(* suppose:								*)
(* 									*)
(*   tm = "?vi. ?vs. C1 /\ ... /\ v = t /\ ... /\ Cn"			*)
(*									*)
(* then the result is:							*)
(*									*)
(*   |- (?vi. ?vs. C1 /\ ... /\ vi = ti /\ ... /\ Cn)			*)
(*          =								*)
(*      (?vs. C1[ti/vi] /\ ... /\ Cn[ti/vi])				*)
(*									*)
(* The equations vi = ti can appear as ti = vi, and all eliminable 	*)
(* equations are eliminated.  Fails unless there is at least one	*)
(* eliminable equation. Also flattens conjuncts. Reduces term to "T" if	*)
(* all variables eliminable.						*)
(* ---------------------------------------------------------------------*)

local
  fun chfn v (a,th) =
     let val tm = mk_exists{Bvar=v,Body=a}
         val th' = if (free_in v (concl th))
                   then EXISTS (mk_exists{Bvar=v,Body=concl th},v) th 
                   else th
     in (tm,CHOOSE (v,ASSUME tm) th')  end
  fun efn ss v (pat,th) =
     let val wit = case (subst_assoc v ss)
                     of NONE => v
                      | (SOME residue) => residue
         val ex = mk_exists{Bvar=v,Body=pat}
         val epat = subst ss ex
     in (ex,EXISTS(epat,wit) th)  end
  fun prove ths cs =
     (uncurry CONJ ((prove ths ## prove ths) (Psyntax.dest_conj cs)))
     handle _ 
     => (Lib.first (fn t => concl t = cs) ths)
     handle _
     => (REFL (rand cs))
in
fun REDUCE tm =
   let val (vs,cs) = strip_exists tm
       val (remn,ss) = reduce vs (CONJUNCTS (ASSUME cs)) [] []
   in if (null ss) 
      then raise IND_DEF_ERR{function="REDUCE",message=""}
      else let val th1 = LIST_CONJ remn handle _ => TRUTH 
               val th2 = (uncurry DISCH) (itlist chfn vs (cs,th1))
               val (rvs,rcs) = strip_exists(rand(concl th2))
               val eqt = subst ss cs
               val th3 = prove (CONJUNCTS (ASSUME rcs)) eqt
               val (_,th4) = itlist (efn ss) vs (cs,th3)
               val th5 = (uncurry DISCH) (itlist chfn rvs (rcs,th4))
           in IMP_ANTISYM_RULE th2 th5
           end
   end
end;



(* ===================================================================== *)
(* CASES THEOREM							 *)
(* ===================================================================== *)

(* ---------------------------------------------------------------------*)
(* INTERNAL FUNCTION : LIST_NOT_FORALL					*)
(*                                                                      *)
(* If:                                                                  *)
(*             |- ~P                                                    *)
(*        --------------- f : thm->thm                                  *)
(*         |- Q  |- R                                                   *)
(*                                                                      *)
(* Then:                                                                *)
(*                                                                      *)
(*   |-  ~!x1 ... xi. P                                                 *)
(*  ----------------------------                                        *)
(*   |-  ?x1 ... xi. Q    |- R                                          *) 
(* ---------------------------------------------------------------------*)

local fun efn v th =  EXISTS(mk_exists{Bvar=v,Body=concl th},v) th
in
fun LIST_NOT_FORALL f th =
   let val (vs,body) = strip_forall (dest_neg (concl th)) 
   in if (null vs) 
      then f th 
      else let val (Q,R) = f (ASSUME(mk_neg body))
               val nott = itlist efn vs Q
               val thm = CCONTR body (MP (ASSUME (mk_neg (concl nott))) nott) 
           in (CCONTR (concl nott) (MP th (GENL vs thm)), R)
           end
   end
end;

(* --------------------------------------------------------------------- *)
(* simp_axiom: simplify the body of an axiom.                            *)
(* --------------------------------------------------------------------- *)

local fun chfn v (a,th) = 
       let val tm = mk_exists{Bvar=v,Body=a}
       in (tm,CHOOSE (v,ASSUME tm) th)  end
in
fun simp_axiom sfn vs ax th =
   let val rbody = LIST_BETA_CONV (dest_neg(concl th))
       val fth = MP th (EQ_MP (SYM rbody) (ASSUME (rand (concl rbody))))
       val imp = PROVE_HYP th (CCONTR (dest_neg(rand(concl rbody))) fth)
       val {ant,conseq} = dest_imp(concl imp)
       val eqs = strip_conj conseq
       val (avs,res) = strip_forall (concl ax)
       val inst = INST (fst(match_term res ant)) (SPECL avs ax)
       val ths = MP imp inst
       val thm = sfn (ASSUME(concl ths)) inst
       val rth = (uncurry DISCH) (itlist chfn vs ((concl ths),thm))
   in (ths,rth)
   end
end;

fun crul rel th =
   if (free_in rel (concl th)) 
   then let val th1 = CONV_RULE LIST_BETA_CONV th 
        in CONJUNCT1 (CONV_RULE (REWR_CONV NOT_IMP) th1) end
   else th;


(* --------------------------------------------------------------------- *)
(* CONJ_RUL : chain through conjunction.				*)
(*                                                                      *)
(* If:                                                                  *)
(*                                                                      *)
(*        |- Pi                                                         *)
(*   -------------- (crul rel) 						*)
(*        |- Qi                                                         *)
(*                                                                      *)
(* then:                                                                *)
(*                                                                      *)
(*    |- P1 /\ ... /\ Pj						*)
(*  --------------------- CONJ_RUL rel					*)
(*    |- P1 /\ ... /\ Qj						*)
(* ---------------------------------------------------------------------*)

fun CONJ_RUL rel th =
   uncurry CONJ ((crul rel ## CONJ_RUL rel) (CONJ_PAIR th))
   handle _ => crul rel th;

fun LIST_EXISTS_THEN f th =
   let val (vs,body) = strip_exists(concl th)
       val th1 = DISCH body (f (ASSUME body)) 
   in MP (itlist EXISTS_IMP vs th1) th
   end;

fun RULE thm1 thm2 =
   let val (xs,imp) = strip_exists (concl thm1)
       val thm =  SPECL xs thm2
       val impth = MP (ASSUME imp) thm
       val iimp = DISCH imp impth 
   in MATCH_MP (itlist EXISTS_IMP xs iimp) thm1 
   end;

(* --------------------------------------------------------------------- *)
(* EXISTS_IMP2 : existentially quantify the antecedent and conclusion 	 *)
(* of an implication.							 *)
(*									 *)
(*        A |- P ==> Q							 *)
(* -------------------------- EXISTS_IMP "x"				 *)
(*   A |- (?x.P) ==> (?x.Q)						 *)
(*									 *)
(* LIKE built-in, but doesn't quantify in Q if not free there.		 *)
(* Actually, used only in context where x not free in Q.		 *)
(*									 *)
(* --------------------------------------------------------------------- *)

fun EXISTS_IMP2 x th =
   let val {ant,conseq} = dest_imp(concl th) 
   in if (free_in x conseq) 
   then let val th1 = EXISTS (mk_exists{Bvar=x,Body=conseq},x) (UNDISCH th)
            val asm = mk_exists{Bvar=x,Body=ant} 
        in DISCH asm (CHOOSE (x,ASSUME asm) th1) 
        end
   else let val asm = mk_exists{Bvar=x,Body=ant} 
        in DISCH asm (CHOOSE (x,ASSUME asm) (UNDISCH th))
        end
   end;

fun efn v th =
    if (free_in v (concl th)) 
    then EXISTS(mk_exists{Bvar=v,Body=concl th},v) th 
    else th;

fun mk_new_subst L2 L1 = 
   map2 (fn rdx => fn rsd => {redex=rdx,residue=rsd}) L1 L2;

fun RULE2 vs thm1 thm2 =
   let val (xs,P) = strip_exists(concl thm1)
       val (ys,Q) = strip_exists(concl thm2)
       fun itfn v vs =  let val v' = variant (vs @ xs) v 
                        in (v'::vs)
                        end
       val ys' = itlist itfn ys []
       val Q' = subst(mk_new_subst ys' ys) Q
       val asm = CONJ (ASSUME P) (ASSUME Q)
       val cs = LIST_CONJ (CONJUNCTS asm)
       val vs = filter (C free_in (concl cs)) (xs @ ys')
       val eth = MP (itlist EXISTS_IMP2 xs (DISCH P (itlist efn vs cs))) thm1
       val ethh = MP (itlist EXISTS_IMP2 ys' (DISCH Q' eth)) thm2 
   in  ethh
   end;

(* --------------------------------------------------------------------- *)
(*  |- ~~P   								*)
(* --------  NOT_NOT							*)
(*   |- P								*)
(* --------------------------------------------------------------------- *)

fun NOT_NOT th =
    CCONTR (dest_neg(dest_neg (concl th))) (UNDISCH th);

(* ---------------------------------------------------------------------*)
(* simp_rule: simplify the body of a non-axiom rule.                    *)
(* ---------------------------------------------------------------------*)

local
  val rule = NOT_NOT o CONV_RULE(RAND_CONV LIST_BETA_CONV)
  fun chfn v (a,th) = 
     let val tm = mk_exists{Bvar=v,Body=a} 
     in (tm,CHOOSE (v,ASSUME tm) th)
     end
  and efn v th = EXISTS(mk_exists{Bvar=v,Body=concl th},v) th
in
fun simp_rule sfn set vs rul th =
   let val (c1,c2) = CONJ_PAIR (CONV_RULE (REWR_CONV NOT_IMP) th)
       val (th1,_) = LIST_NOT_FORALL (fn th => (rule th,TRUTH)) c2
       val th2 = LIST_EXISTS_THEN (CONJ_RUL set) c1
       val (evs,imp) = strip_exists (concl th1)
       val (gvs,cnc) = (I ## rand) (strip_forall(concl rul))
       val th3 = UNDISCH (SPECL gvs rul)
       val pat = list_mk_forall(evs,#ant(dest_imp imp))
       val inst = fst(match_term (concl th3) pat)
       val tha = INST inst (DISCH_ALL th3)
       val rins = MATCH_MP tha th2
       val erins = MATCH_MP tha (ASSUME (concl th2))
       val eqns = RULE th1 rins
       val (evs,eths) = (I ## strip_conj) (strip_exists(concl eqns))
       val thm = sfn (LIST_CONJ (map ASSUME eths)) (SPECL evs erins)
       val (vv,cs) = (I ## strip_conj) (strip_exists(concl th2))
       fun itfn v vs = let val v' = variant (vs @ evs) v in (v'::vs) end
       val vv' = itlist itfn vv []
       val cs' = map (subst(mk_new_subst vv' vv)) cs
       val thx = PROVE_HYP (itlist efn vv' (LIST_CONJ (map ASSUME cs'))) thm
       val simp = RULE2 vs eqns th2
       val (nevs,cn) = strip_exists(concl simp)
       val hys = CONJUNCTS (ASSUME cn)
       val (hh,nthm) = itlist chfn nevs (cn,itlist PROVE_HYP hys thx)
       val res = (uncurry DISCH) (itlist chfn vs (hh,nthm))
   in (PROVE_HYP th simp, res)
   end
end;



fun simp set sfn rul th =
   let val vs = fst(strip_forall (dest_neg (concl th))) 
   in LIST_NOT_FORALL (simp_axiom sfn vs rul) th 
      handle _
      => LIST_NOT_FORALL (simp_rule sfn set vs rul) th 
      handle _ =>
      raise IND_DEF_ERR{function="simp", message=""}
   end;

local
  val v1 = genvar(==`:bool`==)
  and v2 = genvar(==`:bool`==)
  val thm = fst(EQ_IMP_RULE(CONJUNCT1 (SPECL [v1,v2] DE_MORGAN_THM)))
  fun IDISJ th1 th2 =
     let val di = mk_disj{disj1=rand(rator(concl th1)),
                          disj2=rand(rator(concl th2))}
     in DISCH di (DISJ_CASES (ASSUME di) (UNDISCH th1) (UNDISCH th2)) 
     end
  fun ITDISJ th1 th2 =
     let val ([hy1],cl1) = dest_thm th1 
         and ([hy2],cl2) = dest_thm th2 
         val dth = UNDISCH (INST [{redex=v1,residue=rand hy1},
                                  {redex=v2,residue=rand hy2}] thm)
     in DISJ_CASES_UNION dth th1 th2 
     end
in
fun LIST_DE_MORGAN f ths th =
   let val cs = strip_conj(dest_neg (concl th))
       val (ts1,ts2) = split (map2 (fn r => fn t => f r (ASSUME(mk_neg t)))
                                   ths cs)
   in (PROVE_HYP th (end_itlist ITDISJ ts1), end_itlist IDISJ ts2)
   end
end;

exception mymap2_ERR;
fun mymap2 ([],[]) = []
  | mymap2 (h1::rst1, h2::rst2) = mk_eq{lhs=h1,rhs=h2}::mymap2(rst1,rst2)
  | mymap2  _  = raise mymap2_ERR

fun derive_cases_thm (rules,ind) =
   let val (vs,{ant,conseq}) = (I ## dest_imp) (strip_forall (concl ind))
       val (ps,P) = (butlast vs, last vs)
       val sind = SPECL ps ind 
       and srules = map (SPECL ps) rules
       val (cvs,con) = strip_forall conseq
       val thm1 = DISCH ant (SPECL cvs (UNDISCH (SPEC P sind)))
       val avs = map (genvar o type_of) cvs
       val eqns = list_mk_conj(mymap2 (cvs,avs))
       val theta = map2 (fn r1 => fn r2 => {redex=r1,residue=r2}) cvs avs
       val asmp = subst theta (rator con)
       val pred = list_mk_abs (avs,mk_neg(mk_comb{Rator=asmp,Rand=eqns}))
       val thm2 = UNDISCH (UNDISCH (INST [{redex=P,residue=pred}] thm1))
       val thm3 = CONV_RULE LIST_BETA_CONV thm2
       val HY = rand(rator con)
       val contr = DISCH HY (ADD_ASSUM HY (LIST_CONJ (map REFL cvs)))
       val fthm = NOT_INTRO (DISCH (subst [{redex=P,residue=pred}] ant)
                                          (MP thm3 contr))
       fun sfn eqs = SUBST(map2 (fn th => fn v => (v |-> th))
                                (map SYM (CONJUNCTS eqs)) cvs) HY
       val set = fst(strip_comb HY)
       val (a,b) = LIST_DE_MORGAN (simp set sfn) srules fthm
       val th = IMP_ANTISYM_RULE (DISCH HY a) b
       val ds = map (TRY_CONV REDUCE) (strip_disj(rand(concl th)))
       val red = end_itlist (fn t1 => fn t2 => 
                               MK_COMB (AP_TERM (--`\/`--) t1, t2)) ds
   in GENL ps (GENL cvs (TRANS th red))
   end;

type rule = (Term.term quotation list * Term.term quotation list) 
              * Term.term quotation
type pattern = Term.term quotation * Term.term quotation list

val indDefine = fn name => fn rules => fn fixity => fn patt => 
  let val {desc,induction_thm} =
    new_inductive_definition
    {name = name, fixity = fixity, 
     patt = (Term ## map Term) patt,
     rules = map (fn((H,S),C) => {hypotheses=H,side_conditions=S,conclusion=C})
                 (map ((map Term ## map Term) ## Term) rules)}
  in
   {rules=desc, induction = induction_thm}
  end;

end; (* Ind_defLib *)
