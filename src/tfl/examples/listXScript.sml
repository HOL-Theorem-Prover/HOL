(*---------------------------------------------------------------------------
           Supplementary list definitions and theorems.
 ---------------------------------------------------------------------------*)

structure listXScript =
struct

open HolKernel basicHol90Lib bossLib QLib listTheory ;

infix THEN THENL;

val _ = new_theory"listX";


val mem_def = 
 Define 
    `(mem x [] = F) /\ 
     (mem x (CONS y L) = (x=y) \/ mem x L)`;


val filter_def = 
 Define 
    `(filter P [] = []) /\
     (filter P (CONS x L) = (P x => CONS x (filter P L) | filter P L))`;


val mem_filter = Q.store_thm("mem_filter",
`!P L (x:'a). mem x (filter P L) = P x /\ mem x L`,
Induct_on `L`  
 THEN RW_TAC list_ss [mem_def,filter_def] 
 THEN PROVE_TAC [mem_def]);


val mem_filter_lemma = Q.store_thm("mem_filter_lemma",
`!P L (x:'a). mem x L = mem x (filter P L) \/ mem x (filter ($~ o P) L)`,
RW_TAC list_ss [mem_filter,combinTheory.o_DEF] 
  THEN PROVE_TAC[]);


val length_filter = Q.store_thm("length_filter",
`!L P. LENGTH (filter P L) <= LENGTH L`,
REPEAT GEN_TAC 
  THEN Induct_on `L` 
  THEN RW_TAC list_ss  [filter_def]); 


val length_filter_subset = Q.store_thm("length_filter_subset",
`(!y. P y ==> Q y) ==> !L. LENGTH(filter P L) <= LENGTH (filter Q L)`,
DISCH_TAC THEN Induct 
 THEN RW_TAC list_ss [filter_def]
 THEN PROVE_TAC[]);

val length_filter_stable = Q.store_thm("length_filter_stable",
`!L P. (LENGTH(filter P L) = LENGTH L) ==> (filter P L = L)`,
Induct 
  THEN RW_TAC list_ss [filter_def,length_filter]
  THEN MP_TAC (SPEC_ALL length_filter)
  THEN RW_TAC arith_ss []);


val mem_of_append = Q.store_thm("mem_of_append",
`!y L M. mem y (APPEND L M) = mem y L \/ mem y M`,
Induct_on `L` THEN RW_TAC list_ss [APPEND,mem_def] THEN PROVE_TAC[]);

val APPEND = save_thm("APPEND",
CONJ (Q.prove`!L. APPEND L [] = L`
             (Induct THEN Rewrite.ASM_REWRITE_TAC[listTheory.APPEND]))
     listTheory.APPEND);


val filter_append_distrib = Q.store_thm("filter_append_distrib",
`!P L M. filter P (APPEND L M) = APPEND (filter P L) (filter P M)`,
Induct_on `L` THEN RW_TAC list_ss [filter_def]);

val length_append_comm = Q.store_thm("length_append_comm",
`!L M. LENGTH (APPEND L M) = LENGTH (APPEND M L)`,
Induct THEN RW_TAC list_ss []);

val length_append_distrib = Q.store_thm("length_append_distrib",
`!L M. LENGTH (APPEND L M) = LENGTH L + LENGTH M`,
Induct THEN RW_TAC list_ss []);

(*
val append_induction = Q.store_thm("append_induction",
`!P:'a list->bool. 
       P [] /\ 
   (!x.P[x]) /\ 
   (!L1 L2. P L1 /\ P L2 ==> P (APPEND L1 L2)) 
   ==> !L. P L`,
NTAC 2 STRIP_TAC THEN Induct THEN RW_TAC list_ss [] 
 THEN PROVE_TAC [Q.prove `CONS h L = APPEND [h] L`
                         (Rewrite.REWRITE_TAC[APPEND])]);
*)

val length_append_filter = Q.store_thm("length_append_filter",
`!L. LENGTH L = LENGTH (APPEND (filter P L) (filter (~ o P) L))`,
Induct 
 THEN RW_TAC list_ss [filter_def, combinTheory.o_DEF] 
 THEN PROVE_TAC []);

val filters_compose = Q.store_thm("filters_compose",
`!P Q L. 
    filter P (filter Q L) = filter (\x. P x /\ Q x) L`,
Induct_on `L` 
  THEN RW_TAC list_ss [filter_def] 
  THEN RW_TAC list_ss []
  THEN PROVE_TAC []);

val filters_commute = Q.store_thm("filters_commute",
`!P Q L. filter P (filter Q L) = filter Q (filter P L)`,
Induct_on `L` THEN RW_TAC list_ss [filter_def]);


val _ = export_theory();

end;
