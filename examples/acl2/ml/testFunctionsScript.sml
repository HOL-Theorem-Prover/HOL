open bossLib Theory Datatype Drule Tactical Tactic translateTheory
open Thm Term Lib listTheory ratTheory testTypesTheory Conv sexpTheory;

val _ = new_theory "testFunctions";

(*****************************************************************************)
(* Definitions:                                                              *)
(*     FLAT : flatten a list using three clauses                             *)
(*                                                                           *)
(*****************************************************************************)

val FLAT = Define `
    (FLAT [] = []) /\
    (FLAT ([]::xs) = FLAT xs) /\
    (FLAT (((y:'a)::ys)::xs) = y::FLAT (ys::xs))`;

val SPLIT_def = tDefine "SPLIT"
    `(split1 [] (X,Y) = (X,Y)) /\
     (split1 (x::ys) (X,Y) = split2 ys (x::X,Y)) /\
     (split2 [] (X,Y) = (X,Y)) /\
     (split2 (x::ys) (X,Y) = split1 ys (X,x::Y))`
    (WF_REL_TAC `measure (sum_case (LENGTH o FST) (LENGTH o FST))` THEN
     RW_TAC arith_ss [listTheory.LENGTH]);

val merge_def = Define `
    (merge [] [] = []) /\
    (merge (a::b) [] = a::b) /\
    (merge [] (c::d) = c::d) /\
    (merge (a::b) (c::d) =
    	   if a < c:num then a :: merge b (c::d)
	      	    else c :: merge (a::b) d)`;

local
fun varftac f tac (a,g) =
let val v = f g
in  tac v (a,g)
end
val tactic =
    completeInduct_on `LENGTH x` THEN
    Cases THEN
    TRY (varftac (rand o rand o rand o rand o rator)
    		 (fn v => STRUCT_CASES_TAC (ISPEC v list_CASES))) THEN
    RW_TAC arith_ss [LENGTH,SPLIT_def,arithmeticTheory.ADD1] THEN
    varftac (rand o rand o rator o rand o rand)
    	    (fn v => POP_ASSUM (MP_TAC o ISPEC ``LENGTH (^v)``) THEN RW_TAC arith_ss []) THEN
    varftac (rand o rand o rator o rand o rand)
    	    (fn v => POP_ASSUM (MP_TAC o ISPEC v) THEN RW_TAC arith_ss [] THEN
		     DISJ_CASES_TAC (ISPEC ``1 < LENGTH (^v)`` boolTheory.EXCLUDED_MIDDLE) THEN1
    		         METIS_TAC [arithmeticTheory.LESS_TRANS,
		     	       	    DECIDE ``SUC a + b < a + (b + 2n)``,LENGTH]) THEN
    varftac (rand o rand o rator o rand o rand)
    	    (fn v => REPEAT (POP_ASSUM MP_TAC) THEN
	    	     STRUCT_CASES_TAC (ISPEC v listTheory.list_CASES) THEN
    		     RW_TAC arith_ss [LENGTH,SPLIT_def,arithmeticTheory.ADD1]) THEN
    varftac (rand o rand o rator o rand o rand)
    	    (fn v => REPEAT (POP_ASSUM MP_TAC) THEN
    		     STRUCT_CASES_TAC (ISPEC v list_CASES)) THEN
    RW_TAC arith_ss [LENGTH,SPLIT_def,arithmeticTheory.ADD1]
in
val length_split1_lemma1 = prove(``!x a b. 1 < LENGTH x ==>
      (LENGTH (FST (split1 x (a,b))) < LENGTH x + LENGTH a)``,tactic);
val length_split1_lemma2 = prove(``!x a b. 1 < LENGTH x ==>
      (LENGTH (SND (split1 x (a,b))) < LENGTH x + LENGTH b)``,tactic);
end;

val merge_sort_def = tDefine "merge_sort" `
    (merge_sort xs =
      if LENGTH xs <= 1 then xs
         else let (left,right) = split1 xs ([],[])
	      in  merge (merge_sort left) (merge_sort right))`
    (WF_REL_TAC `measure LENGTH` THEN
     RW_TAC std_ss [] THEN
     METIS_TAC [arithmeticTheory.NOT_LESS_EQUAL,
      SIMP_RULE std_ss [LENGTH] (Q.SPECL [`xs`,`[]`,`[]`] length_split1_lemma2),
      SIMP_RULE std_ss [LENGTH] (Q.SPECL [`xs`,`[]`,`[]`] length_split1_lemma1),
      pairTheory.PAIR,pairTheory.PAIR_EQ]);

val EVEN_EXTEND_def= store_thm("EVEN_EXTEND_def",
    ``(EVEN 0 = T) /\
      (EVEN (SUC 0) = F) /\
      (!n. EVEN (SUC (SUC n)) = EVEN n)``,
    RW_TAC arith_ss [arithmeticTheory.EVEN]);

val ODD_EVEN_def = store_thm("ODD_EVEN_def",
    ``(EVEN 0 = T) /\ (ODD 0 = F) /\
      (!n. EVEN (SUC n) = ODD n) /\ (!n. ODD (SUC n) = EVEN n)``,
    RW_TAC arith_ss [arithmeticTheory.EVEN,arithmeticTheory.ODD,
    	   arithmeticTheory.ODD_EVEN]);

val ECASE = Define `
    (ECASE 0 _ = T) /\
    (ECASE (SUC 0) _ = T) /\
    (ECASE (SUC (SUC n)) [] = T)`;

val LCASE = Define `
    (LCASE [] _ = T) /\
    (LCASE [x] _ = F) /\
    (LCASE (x::y::xys) 0n = T)`;

val OLIST = Define `
    (OLIST [] = []) /\
    (OLIST (SOME x :: xs) = x :: OLIST xs) /\
    (OLIST (NONE :: xs) = OLIST xs)`;

val FLATTEN_TREE = Define `
    (FLATTEN_TREE (TLeaf a) = [a]) /\
    (FLATTEN_TREE (TBranch t1 t2) = FLATTEN_TREE t1 ++ FLATTEN_TREE t2)`;

val FT_FAST = Define `
    (FT_FAST (TLeaf a) A = (a::A)) /\
    (FT_FAST (TBranch t1 t2) A = FT_FAST t1 (FT_FAST t2 A))`;

val ADDLIST_def = Define `
    (ADDLIST [] = 0n) /\ (ADDLIST (x::xs) = x + ADDLIST xs)`;

val GENL_def = Define `
    (GENL 0 = []) /\ (GENL (SUC n) = n::GENL n)`;

val ADDN_def = Define `
    (ADDN n = ADDLIST (GENL n))`;

val _ = export_theory();

