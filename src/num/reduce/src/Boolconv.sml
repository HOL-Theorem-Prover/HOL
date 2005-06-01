(*===========================================================================
== LIBRARY:     reduce (Part I)                                            ==
==                                                                         ==
== DESCRIPTION: Conversions for reducing boolean expressions.              ==
==                                                                         ==
== AUTHOR:      John Harrison                                              ==
==              University of Cambridge Computer Laboratory                ==
==              New Museums Site                                           ==
==              Pembroke Street                                            ==
==              Cambridge CB2 3QG                                          ==
==              England.                                                   ==
==                                                                         ==
==              jrh@cl.cam.ac.uk                                           ==
==                                                                         ==
== DATE:        18th May 1991                                              ==
==                                                                         ==
== TRANSLATOR:  Kim Dam Petersen (kimdam@tfl.dk)                           ==
============================================================================*)

structure Boolconv :> Boolconv =
struct

open HolKernel Parse boolLib;

val ERR = mk_HOL_ERR "Boolconv";
fun failwith function = raise (ERR function "");

val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars boolTheory.bool_grammars

val zv    = mk_var("z",bool)
and beqop = inst [alpha |->bool] equality;

(*-----------------------------------------------------------------------*)
(* NOT_CONV "~F"  = |-  ~F = T                                           *)
(* NOT_CONV "~T"  = |-  ~T = F                                           *)
(* NOT_CONV "~~t" = |- ~~t = t                                           *)
(*-----------------------------------------------------------------------*)

local val [c1,c2,c3] = CONJUNCTS
	(Tactical.prove((--`(~T = F) /\ (~F = T) /\ (!t. ~~t = t)`--),
	       REWRITE_TAC[NOT_CLAUSES]))
in
fun NOT_CONV tm =
 let val xn = dest_neg tm
 in if xn = T then c1 else
    if xn = F then c2
    else let val xn' = dest_neg xn in SPEC xn c3 end
 end handle HOL_ERR _ => raise ERR "NOT_CONV" ""
end;

(*-----------------------------------------------------------------------*)
(* AND_CONV "T /\ t" = |- T /\ t = t                                     *)
(* AND_CONV "t /\ T" = |- t /\ T = t                                     *)
(* AND_CONV "F /\ t" = |- F /\ t = F                                     *)
(* AND_CONV "t /\ F" = |- t /\ F = F                                     *)
(* AND_CONV "t /\ t" = |- t /\ t = t                                     *)
(*-----------------------------------------------------------------------*)

local val [c1,c2,c3,c4,c5] = CONJUNCTS
       (Tactical.prove
        (Term`(!t. T /\ t = t) /\ (!t. t /\ T = t) /\
              (!t. F /\ t = F) /\ (!t. t /\ F = F) /\ (!t. t /\ t = t)`,
	       REWRITE_TAC[AND_CLAUSES]))
in
fun AND_CONV tm =
 let val (xn,yn) = with_exn dest_conj tm (ERR "AND_CONV" "")
 in if xn = T then SPEC yn c1 else
    if yn = T then SPEC xn c2 else
    if xn = F then SPEC yn c3 else
    if yn = F then SPEC xn c4 else
    if xn = yn then SPEC xn c5 else
    if aconv xn yn
     then SUBST [zv |-> ALPHA xn yn]
           (mk_comb(mk_comb(beqop,mk_conj(xn,zv)), xn))
           (SPEC xn c5)
     else failwith "AND_CONV"
 end
 end;

(*-----------------------------------------------------------------------*)
(* OR_CONV "T \/ t" = |- T \/ t = T                                      *)
(* OR_CONV "t \/ T" = |- t \/ T = T                                      *)
(* OR_CONV "F \/ t" = |- F \/ t = t                                      *)
(* OR_CONV "t \/ F" = |- t \/ F = t                                      *)
(* OR_CONV "t \/ t" = |- t \/ t = t                                      *)
(*-----------------------------------------------------------------------*)

local val [c1,c2,c3,c4,c5] = CONJUNCTS
	(Tactical.prove
         (Term`(!t. T \/ t = T) /\ (!t. t \/ T = T) /\ (!t. F \/ t = t) /\
		   (!t. t \/ F = t) /\ (!t. t \/ t = t)`,
	  REWRITE_TAC[OR_CLAUSES]))
in
fun OR_CONV tm =
 let val (xn,yn) = with_exn dest_disj tm (ERR "OR_CONV" "")
 in if xn = T then SPEC yn c1 else
    if yn = T then SPEC xn c2 else
    if xn = F then SPEC yn c3 else
    if yn = F then SPEC xn c4 else
    if xn = yn then SPEC xn c5 else
    if aconv xn yn
      then SUBST [zv |-> ALPHA xn yn]
             (mk_comb(mk_comb(beqop,mk_disj(xn,zv)),xn))
             (SPEC xn c5)
      else failwith "OR_CONV"
 end
end;

(*-----------------------------------------------------------------------*)
(* IMP_CONV "T ==> t" = |- T ==> t = t                                   *)
(* IMP_CONV "t ==> T" = |- t ==> T = T                                   *)
(* IMP_CONV "F ==> t" = |- F ==> t = T                                   *)
(* IMP_CONV "t ==> F" = |- t ==> F = ~t                                  *)
(* IMP_CONV "t ==> t" = |- t ==> t = T                                   *)
(*-----------------------------------------------------------------------*)

local val [c1,c2,c3,c4,c5] = CONJUNCTS
	(Tactical.prove(
          Term`(!t. (T ==> t) = t) /\ (!t. (t ==> T) = T) /\
               (!t. (F ==> t) = T) /\ (!t. (t ==> F) = ~t) /\
               (!t. (t ==> t) = T)`, REWRITE_TAC[IMP_CLAUSES]))
in
fun IMP_CONV tm =
 let val (xn,yn) = with_exn dest_imp tm (ERR "IMP_CONV" "")
 in if xn = T then SPEC yn c1 else
    if yn = T then SPEC xn c2 else
    if xn = F then SPEC yn c3 else
    if yn = F then SPEC xn c4 else
    if xn = yn then SPEC xn c5 else
    if aconv xn yn
       then SUBST [zv |-> ALPHA xn yn]
              (mk_comb(mk_comb(beqop,mk_imp(xn,zv)),T))
              (SPEC xn c5)
       else failwith "IMP_CONV"
 end
end;

(*-----------------------------------------------------------------------*)
(* BEQ_CONV "T = t" = |- T = t = t                                       *)
(* BEQ_CONV "t = T" = |- t = T = t                                       *)
(* BEQ_CONV "F = t" = |- F = t = ~t                                      *)
(* BEQ_CONV "t = F" = |- t = F = ~t                                      *)
(* BEQ_CONV "t = t" = |- t = t = T                                       *)
(*-----------------------------------------------------------------------*)

local val [c1,c2,c3,c4,c5] = CONJUNCTS
       (Tactical.prove
        (Term`(!t. (T = t) = t) /\ (!t. (t = T) = t) /\ (!t. (F = t) = ~t) /\
		   (!t. (t = F) = ~t) /\ (!t:bool. (t = t) = T)`,
	       REWRITE_TAC[EQ_CLAUSES]))
in
fun BEQ_CONV tm =
 let val (xn,yn) = with_exn dest_eq tm (ERR "BEQ_CONV" "")
 in if xn = T then SPEC yn c1 else
    if yn = T then SPEC xn c2 else
    if xn = F then SPEC yn c3 else
    if yn = F then SPEC xn c4 else
    if xn = yn then SPEC xn c5 else
    if aconv xn yn then EQT_INTRO (ALPHA xn yn) else failwith "BEQ_CONV"
 end
end;

(*-----------------------------------------------------------------------*)
(* COND_CONV "F => t1 | t2" = |- (T => t1 | t2) = t2                     *)
(* COND_CONV "T => t1 | t2" = |- (T => t1 | t2) = t1                     *)
(* COND_CONV "b => t  | t"  = |- (b => t | t)   = t                      *)
(*-----------------------------------------------------------------------*)

local val [c1,c2,c3] = CONJUNCTS
	(Tactical.prove(Term`(!t1 t2. (if T then t1 else t2) = (t1:'a)) /\
	                     (!t1 t2. (if F then t1 else t2) = (t2:'a)) /\
		             (!b t.   (if b then t else t) = (t:'a))`,
	       REWRITE_TAC[COND_CLAUSES, COND_ID]))
in
fun COND_CONV tm =
 let val (b,t1,t2) = with_exn dest_cond tm (ERR "COND_CONV" "")
 in if b = T then SPECL [t1,t2] (INST_TYPE[alpha |-> type_of t1] c1) else
    if b = F then SPECL [t1,t2] (INST_TYPE[alpha |-> type_of t1] c2) else
    if t1=t2 then SPECL [b,t1]  (INST_TYPE[alpha |-> type_of t1] c3) else
    if aconv t1 t2
      then TRANS (AP_TERM (rator tm) (ALPHA t2 t1))
                 (SPECL [b, t1] (INST_TYPE [alpha |-> type_of t1] c3))
      else failwith "BEQ_CONV"
 end
end;

val _ = Parse.temp_set_grammars ambient_grammars

end
