
open Globals HolKernel Parse bossLib

open Drule Thm boolTheory

val _ = new_theory "sat";

val RES_THMl0 = save_thm("RES_THMl0",PROVE [] ``!x. x /\ ~x ==> F \/ F``)
val RES_THMrl = save_thm("RES_THMrl",PROVE [] ``!x P. (x \/ P) /\ ~x ==> P \/ F``)
val RES_THMll = save_thm("RES_THMll",PROVE [] ``!x Q. x /\ (~x \/ Q) ==> F \/ Q``)
val RES_THMl = save_thm("RES_THMl",PROVE [] ``!x P Q. (x \/ P) /\ (~x \/ Q) ==> P \/ Q``)
val RES_THMr0 = save_thm("RES_THMr0",PROVE [] ``!x. ~x /\ x ==> F \/ F``)
val RES_THMrr = save_thm("RES_THMrr",PROVE [] ``!x P. (~x \/ P) /\ x ==> P \/ F``)
val RES_THMlr = save_thm("RES_THMlr",PROVE [] ``!x Q. ~x /\ (x \/ Q) ==> F \/ Q``)
val RES_THMr = save_thm("RES_THMr",PROVE [] ``!x P Q. (~x \/ P) /\ (x \/ Q) ==> P \/ Q``)

val RES_THM2 = save_thm("RES_THM2",PROVE [] ``!a b c. a ==> b ==> (a /\ b ==> c) ==> c``)
val RES_THM3 = save_thm("RES_THM3",
			PROVE [] ``!a a' b b' c. (a==>a') ==> (b==>b') ==> (a' /\ b' ==> c) ==> (a /\ b ==> c)``)

val AND_OR = save_thm("AND_OR",PROVE [] ``!A B. A /\ B ==> A \/ B``)
val AND_IMP = save_thm("AND_IMP",PROVE [] ``!A B C. A /\ B ==> C = A ==> B ==> C``)
val NOT_NOT = save_thm("NOT_NOT",GEN_ALL (hd (CONJUNCTS (SPEC_ALL NOT_CLAUSES))))
val NOT_FALSE = save_thm("NOT_FALSE",GEN_ALL (last (CONJUNCTS (SPEC_ALL NOT_CLAUSES))))
val NOT_AND_EXTEND = save_thm("NOT_AND_EXTEND",PROVE [] ``!a b. ~a ==> ~(a /\ b)``)
val IMP_REFL = save_thm("IMP_REFL",GEN_ALL (EQT_ELIM (List.nth(CONJUNCTS (SPEC_ALL IMP_CLAUSES),3))))
val IMP_F = save_thm("IMP_F",GEN_ALL (List.nth(CONJUNCTS (SPEC_ALL IMP_CLAUSES),4)))
val T_IMP = save_thm("T_IMP",GEN_ALL (List.nth(CONJUNCTS (SPEC_ALL IMP_CLAUSES),0)))
val IMP_CHAIN = 
    save_thm("IMP_CHAIN",
	     PROVE []``!l1 l2 l3 l4 l5. (l1 /\ l2 ==> l3) ==> (l4 ==> l1) ==> (l5 ==> l2) ==> (l4 /\ l5) ==> l3``)
val LEFT_IMP_CHAIN = save_thm("LEFT_IMP_CHAIN",
			      PROVE [] ``!l1 l2 l3 l4. (l1 /\ l2 ==> l3) ==> (l4 ==> l1) ==>  (l4 /\ l2) ==> l3``)
val RIGHT_IMP_CHAIN = save_thm("RIGHT_IMP_CHAIN",
			       PROVE [] ``!l1 l2 l3 l5. (l1 /\ l2 ==> l3) ==> (l5 ==> l2) ==>  (l1 /\ l5) ==> l3``)

(* ac thms for disjs *)

val OR_NO_DUP = save_thm("OR_NO_DUP", PROVE [] ``!a b. a \/ (a \/ b) = a \/ b``)
val OR_OR = save_thm("OR_OR",GEN_ALL(last(CONJUNCTS(SPEC_ALL OR_CLAUSES))))

val OR_IMP_FALSE = save_thm("OR_IMP_FALSE",PROVE [] ``!t. t ==> (t \/ F)``)
val OR_FALSE = save_thm("OR_FALSE",GEN_ALL (List.nth(CONJUNCTS (SPEC_ALL OR_CLAUSES),3)))
val FALSE_OR = save_thm("FALSE_OR",GEN_ALL (List.nth(CONJUNCTS (SPEC_ALL OR_CLAUSES),2)))
val OR_FALSE2 = save_thm("OR_FALSE2",PROVE [] ``!a b. a \/ (F \/ b) = a \/ b``)
val OR_FALSE3 = save_thm("OR_FALSE3",PROVE [] ``!a. F \/ (F \/ a) = a``)

val ACR3d = save_thm ("ACR3d",PROVE [] ``!A B C. A \/ (B \/ C) =  B \/ (A \/ C)``)
val ACLd = save_thm("ACLd",PROVE [] ``!a b c d. (a \/ b) \/ (c \/ d) = a \/ (b \/ (c \/ d))``)
val ACRd = save_thm("ACRd",PROVE [] ``!a b c d. (a \/ b) \/ (c \/ d) = c \/ ((a \/ b) \/ d)``)
val ACEd = save_thm("ACEd",PROVE [] ``!a b c. (a \/ b) \/ (a \/ c) = a \/ (b \/ c)``)

val FACEd1 = save_thm("FACEd1",PROVE [] ``!a b c. (F \/ a) \/ (b \/ c) = a \/ (b \/ c)``)
val FACEd2 = save_thm("FACEd2",PROVE [] ``!a b c. (a \/ b) \/ (F \/ c) = (a \/ b) \/ c``)
val FACEd3 = save_thm("FACEd3",PROVE [] ``!a b. (F \/ a) \/ (F \/ b) = a \/ b``)

val MACd = save_thm("MACd",METIS_PROVE [] ``!a b c d e. (a=b) ==> (c=d) ==> (b \/ d = e) ==> (a \/ c = e)``)  

val OPTd = save_thm("OPTd",PROVE [] ``!a b c d. (a=b) ==> (c=d) ==> (a\/c=b\/d)``)

val OR_INV_IDl = save_thm("OR_INV_IDl",PROVE [] ``!a. (a \/ ~a = T)``)
val OR_INV_IDr = save_thm("OR_INV_IDr",PROVE [] ``!a. (~a \/ a = T)``)
val OR_INVl = save_thm("OR_INVl",PROVE [] ``!a b. a \/ (~a \/ b) = T``)
val OR_INVr = save_thm("OR_INVr",PROVE [] ``!a b. ~a \/ (a \/ b) = T``)
val OR_INVbl = save_thm("OR_INVbl",PROVE [] ``!x P Q. ((x \/ P) \/ (~x \/ Q) = T)``)
val OR_INVbr = save_thm("OR_INVbr",PROVE [] ``!x P Q. ((~x \/ P) \/ (x \/ Q) = T)``)

(* ac thms for conjs *)

val AND_NO_DUP = save_thm("AND_NO_DUP", PROVE [] ``!a b. a /\ (a /\ b) = a /\ b``)
val AND_AND = save_thm("AND_AND",GEN_ALL(last(CONJUNCTS(SPEC_ALL AND_CLAUSES))))

val AND_TRUE = save_thm("AND_TRUE",GEN_ALL (List.nth(CONJUNCTS (SPEC_ALL AND_CLAUSES),3)))
val TRUE_AND = save_thm("TRUE_AND",GEN_ALL (List.nth(CONJUNCTS (SPEC_ALL AND_CLAUSES),2)))
val AND_TRUE2 = save_thm("AND_TRUE2",PROVE [] ``!a b. a /\ (T /\ b) = a /\ b``)
val AND_TRUE3 = save_thm("AND_TRUE3",PROVE [] ``!a. T /\ (T /\ a) = a``)

val ACR3c = save_thm ("ACR3c",PROVE [] ``!a b c. a /\ (b /\ c) =  b /\ (a /\ c)``)
val ACLc = save_thm("ACLc",PROVE [] ``!a b c d. (a /\ b) /\ (c /\ d) = a /\ (b /\ (c /\ d))``)
val ACRc = save_thm("ACRc",PROVE [] ``!a b c d. (a /\ b) /\ (c /\ d) = c /\ ((a /\ b) /\ d)``)
val ACEc = save_thm("ACEc",PROVE [] ``!a b c. (a /\ b) /\ (a /\ c) = a /\ (b /\ c)``)

val TACEc1 = save_thm("TACEc1",PROVE [] ``!a b c. (T /\ a) /\ (b /\ c) = a /\ (b /\ c)``)
val TACEc2 = save_thm("TACEc2",PROVE [] ``!a b c. (a /\ b) /\ (T /\ c) = (a /\ b) /\ c``)
val TACEc3 = save_thm("TACEc3",PROVE [] ``!a b. (T /\ a) /\ (T /\ b) = a /\ b``)

val MACd = save_thm("MACc",METIS_PROVE [] ``!a b c d e. (a=b) ==> (c=d) ==> (b /\ d = e) ==> (a /\ c = e)``)  

val OPTd = save_thm("OPTc",PROVE [] ``!a b c d. (a=b) ==> (c=d) ==> (a/\c=b/\d)``)

val AND_INV_IDl = save_thm("AND_INV_IDl",PROVE [] ``!a. (a /\ ~a = F)``)
val AND_INV_IDr = save_thm("AND_INV_IDr",PROVE [] ``!a. (~a /\ a = F)``)
val AND_INVl = save_thm("AND_INVl",PROVE [] ``!a b. a /\ (~a /\ b) = F``)
val AND_INVr = save_thm("AND_INVr",PROVE [] ``!a b. ~a /\ (a /\ b) = F``)
val AND_INVbl = save_thm("AND_INVbl",PROVE [] ``!x P Q. ((x /\ P) /\ (~x /\ Q) = F)``)
val AND_INVbr = save_thm("AND_INVbr",PROVE [] ``!x P Q. ((~x /\ P) /\ (x /\ Q) = F)``)

(* generic ac thms for deriving special ones *)

val GACR3 = save_thm ("GACR3",METIS_PROVE [] 
		      ``!P. 
		      (!t1 t2 t3. P t1 (P t2 t3) =  P (P t1 t2) t3) ==>
			  (!t1 t2. P t1 t2 = P t2 t1) ==>
			      !a b c. P a (P b c) =  P b (P a c)``)

val GACL = save_thm ("GACL",METIS_PROVE [] 
		     ``!P. 
		     (!t1 t2 t3. P t1 (P t2 t3) =  P (P t1 t2) t3) ==>
			 (!t1 t2. P t1 t2 = P t2 t1) ==>
			     !a b c d. P (P a b) (P c d) = P a (P b (P c d))``)

val GACR = save_thm ("GACR",METIS_PROVE [] 
		     ``!P. 
		     (!t1 t2 t3. P t1 (P t2 t3) =  P (P t1 t2) t3) ==>
			 (!t1 t2. P t1 t2 = P t2 t1) ==>
			     !a b c d. P (P a b) (P c d) = P c (P (P a b) d)``)

val GMAC = save_thm ("GMAC",METIS_PROVE [] ``!P. !a b c d e. (a=b) ==> (c=d) ==> (P b d = e) ==> (P a c = e)``)

(* support for GROUND_RES_CONV*)

val GRCl = save_thm("GRCl",PROVE [] ``!a P Q. (a \/ P) /\ Q ==> a \/ (P /\ Q)``)
val GRCr = save_thm("GRCr", PROVE [] ``!a P Q. P /\ (a \/ Q) ==> a \/ (P /\ Q)``)
val GRCb = save_thm("GRCb", PROVE [] ``!a b P Q. (a \/ P) /\ (b \/ Q) ==> a \/ b \/ (P /\ Q)``)
val GRC2 = save_thm("GRC2", PROVE [] ``!a b. (b==>F) ==> (a \/ b) ==> a``)
val GRC2b = save_thm("GRC2b", PROVE [] ``!a a' b. (b==>F) ==> (a \/ a' \/ b) ==> (a \/ a')``)
val GRC3 = save_thm("GRC3", PROVE [] ``!a b c. (b==>c) ==> (a \/ b) ==> (a \/ c)``)
val GRC4 = save_thm("GRC4", PROVE [] ``!a a' b c. (b==>c) ==> (a \/ a' \/ b) ==> (a \/ a' \/ c)``)
val GRCm = save_thm("GRCm",PROVE [] ``!x y a a' b b'. ((x \/ a') /\ (y \/ b') ==> a' \/ b') ==> 
				 (((a \/ x \/ a') /\ (b \/ y \/ b')) ==> (a \/ a') \/ (b \/ b'))``)

val FvF = save_thm("FvF",PROVE [] ``!a. F \/ a \/ F = a``)
val xvF = save_thm("xvF",PROVE [] ``!x a. x \/ a \/ F = x \/ a``)

(*support for litList2Clause*)

val mp00 = save_thm("CL2_MP00",PROVE [] ``!A B. ~A /\ ~B = ~(A \/ B)``)
val mp01 = save_thm("CL2_MP01",PROVE [] ``!A B. ~A /\ B = ~(A \/ ~B)``)
val mp10 = save_thm("CL2_MP10",PROVE [] ``!A B. A /\ ~B = ~(~A \/ B)``)
val mp11 = save_thm("CL2_MP11",PROVE [] ``!A B. A /\ B = ~(~A \/ ~B)``)

val AND_INV = save_thm("AND_INV",PROVE [] ``!A. ~A /\ A = F``)
val AND_INV_IMP = save_thm("AND_INV_IMP",PROVE [] ``!A. A ==> ~A ==> F``)
val OR_DUAL = save_thm("OR_DUAL", PROVE [] ``(~(A \/ B) ==> F) = (~A ==> ~B ==> F)``)

(*support for mostly sublinear REORDER_CLAUSE_CONV*)
local

open boolSyntax Conv

in 

(* moves literal p to leftmost position in a clause, preparatory to use with RES_THM(l/r)        *)
(* assert: p occurs in the clause *)
(* assert: clause is ac-norm *)
(* runs in linear time *)
fun REORDER_CLAUSE_CONV p c =
    if is_disj c
    then let val (c1,c2) = dest_disj c
         in if Term.compare(p,c1)=EQUAL
            then REFL c
            else let val th1 = REORDER_CLAUSE_CONV p c2
                 in if Term.compare(p,rhs(concl th1))=EQUAL
                    then REWR_CONV DISJ_COMM c
                    else CONV_RULE (RHS_CONV (REWR_CONV ACR3d)) (AP_TERM (mk_comb(disjunction,c1)) th1)
                 end
         end
    else REFL c

fun mk_roc_thm n = 
    let val c = list_mk_disj(List.tabulate(n+1,fn i => mk_var("v"^(int_to_string i),bool)))
	val _ = save_thm("ROC"^(int_to_string n),
			 GEN_ALL (REORDER_CLAUSE_CONV (mk_var ("v"^(int_to_string (n-1)),bool)) c))
    in () end

val _ = List.app mk_roc_thm [1,2,4,8,16,32,64,128,256,512]

end

val _ = export_theory();
