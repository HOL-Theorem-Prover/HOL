(*=============================================================== *)
(* Some tools to do term simplifications.

   Used by the symbolic execution or by RUN, with constraint solver
   or SMT solver.
*)
(*=============================================================== *)


open HolKernel Parse boolLib  arithmeticTheory 
     relationTheory newOpsemTheory 
     computeLib bossLib;


(* --------------------------------------------------- *)
(* Function to get the result of an equational theorem *)
(* --------------------------------------------------- *)
fun getThm thm =
  snd(dest_comb(concl(thm)));


(* --------------------------------------------------- *)
(* functions to transform JML bounded forall statement *)
(* --------------------------------------------------  *)

(* conversion rule to rewrite a bounded for all term
   as a conjunction *) 
fun boundedForALL_ONCE_CONV tm =
 let val (vars,body) = strip_forall tm
     val (ant,con) = dest_imp body
     val (_,[lo,hi]) = strip_comb ant
 in
  if hi = Term(`0:num`)
   then (EVAL THENC SIMP_CONV std_ss []) tm
   else CONV_RULE
         (RHS_CONV EVAL)
         (BETA_RULE
          (SPEC
            (mk_abs(lo,con))
            (Q.GEN `P` (CONV_RULE EVAL (SPEC hi BOUNDED_FORALL_THM)))))
 end;                                                                                                                                    

val boundedForAll_CONV =
 TOP_DEPTH_CONV boundedForALL_ONCE_CONV THENC REWRITE_CONV [];                                                                           

(* take a term t and converts it according to
    boundedForAll_CONV *)
fun rewrBoundedForAll tm =
    getThm (boundedForAll_CONV tm)
    handle UNCHANGED => tm;

(* --------------------------------------------------- *)
(* function to eliminate  ``T`` from conjunctions. 
   It is required because the current Java implementation
   that takes a XML tree to build the CSP
   doesn't consider Booleans.
   So if precondition is ``T`` then the XML tag is empty
*)
(* --------------------------------------------------- *)
fun mkSimplConj t1 t2 = 
  getThm (EVAL ``^t1 /\ ^t2``);



(*---------------------------------------------------------*)
(* Tool for applying De Morgan's laws at the top level to a 
negated conjunction terms. For each term which is
an implication, apply NOT_IMP_CONJ theorem:

NOT_CONJ_IMP_CONV  ``~((A1 ==> B1) /\ ... /\ (An ==> Bn) /\ TM)`` =
 |- (A1 /\ ~B1) \/ ... \/ (An /\ ~Bn) \/ ~TM
*)

(* ---------------------------------------------------------*)
local

   val DE_MORGAN_AND_THM = METIS_PROVE [] ``!A B. ~(A/\B) = ~A \/ ~B `` 

in

fun NOT_CONJ_IMP_CONV tm =
 let val tm1 = dest_neg tm
 in
  if is_imp_only tm1
   then let val (tm2,tm3) = dest_imp tm1
        in
         SPECL [tm2,tm3] NOT_IMP
        end
   else 
     if is_conj tm1
     then let val (tm2,tm3) = dest_conj tm1
        in
            if is_imp_only tm2
            then let val (tm4,tm5) = dest_imp tm2
              in
                CONV_RULE
                (RAND_CONV(RAND_CONV NOT_CONJ_IMP_CONV))
                (SPECL [tm4,tm5,tm3] NOT_IMP_CONJ)
             end
            else 
               CONV_RULE
                (RAND_CONV(RAND_CONV NOT_CONJ_IMP_CONV))
                (SPECL [tm2,tm3] DE_MORGAN_AND_THM)
        end
      else REFL tm
  end
  handle HOL_ERR t  => 
     (print "HOL_ERR in NOT_CONJ_IMP_CONV";
      REFL tm
     )
end;

(* --------------------------------------------------- *)
(* Functions to handle post and pre conditions         *)
(* --------------------------------------------------- *)


(* --------------------------------------------------- *)
(* function to take the negation of the postcondition
   using NOT_CONJ_IMP_CONV *)
(* --------------------------------------------------- *)
fun takeNegPost post =
 let val n = mk_neg(post);
   in
     if is_conj(post) orelse is_imp_only(post)
     then 
     (* build the negation using De Morgan laws at one level *)
         getThm (NOT_CONJ_IMP_CONV n)
     else
       (* case where post is not an implication *)
       n
     handle HOL_ERR t  => 
       (print "HOL_ERR in takeNegPost";
        n
        )
   end;

(* val post = `` i < j ==> (i - j = j - i)``;
val n = mk_neg(post);*)
(* --------------------------------------------------- *)
(* evaluate precondition on initial state *)
(* --------------------------------------------------- *)
fun evalPre t st = 
   rewrBoundedForAll(getThm (EVAL ``^t ^st``));

(* modify the initial state to take into
   account equalities of the form "x = l" where x is a variable
   and l is a constant *)
(*TODO
fun computeStateFromPre pre s =
  *)

(* --------------------------------------------------- *)
(* function to evaluate the postcondition.
   st1 is the state before execution of the program
   st2 is the state after execution of the program
*)
(* --------------------------------------------------- *)
fun evalPost t st1 st2 = 
  let val p = getThm (EVAL ``^t ^st1``);
   val pp =  if (is_abs(p))
             then getThm (EVAL ``^p ^st2``)
             else p
   in
     rewrBoundedForAll pp
   end
   handle HOL_ERR s => 
     (print "HOL_ERR in evalPost";
      t
     )
  ;
