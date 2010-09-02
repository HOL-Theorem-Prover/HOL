
open HolKernel Parse boolLib bossLib; val _ = new_theory "m1_factorial_proof";

open m1_progTheory m1_factorialTheory;
open combinTheory addressTheory sexpTheory imported_acl2Theory;
open complex_rationalTheory hol_defaxiomsTheory;
open arithmeticTheory;

infix \\
val op \\ = op THEN;

val sexp_fact_def = acl2_fact_definition
  |> SIMP_RULE bool_ss [top_defun,pop_defun,push_defun,nth_lemma, 
       LET_DEF,nth_1,cdr_def,car_def,ite_def,not_eq_nil] 

val FACT_def = Define `
  (FACT (0,m) = m) /\
  (FACT (SUC n,m) = FACT (n,m * SUC n))`;

val FACTORIAL_def = Define `
  (FACTORIAL 0 = 1) /\
  (FACTORIAL (SUC n) = SUC n * FACTORIAL n)`;

val FACT_EQ_FACTORIAL = prove(
  ``!n m. FACT (n,m) = FACTORIAL n * m``,
  Induct \\ ASM_SIMP_TAC std_ss [FACT_def,FACTORIAL_def,AC MULT_ASSOC MULT_COMM]);

val sexp_fact1_thm = prove(
  ``!n m. fact1_pre (List [nat n; nat m],List []) /\
          (sexp_fact1 (List [nat n; nat m]) (List []) = 
           List [List [nat 0; nat (FACT (n,m))]; List []])``,
  Induct \\ FULL_SIMP_TAC std_ss [List_def] \\ ONCE_REWRITE_TAC [sexp_fact_def]
  \\ SIMP_TAC std_ss [FACT_def,car_def,less_nat,cdr_def,mult_nat,
       update_nth_lemma,update_nth_1,sexp_not]
  \\ ONCE_REWRITE_TAC [] \\ ASM_SIMP_TAC std_ss [sexp_reduce_SUC]  
  \\ SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM]); 

val sexp_fact_thm = prove(
  ``!n m. fact_pre (List [nat n; nat m],List []) /\
          (sexp_fact (List [nat n; nat m]) (List []) = 
           List [List [nat 0; nat (FACT (n,1))]; List [nat (FACT (n,1))]])``,
  ONCE_REWRITE_TAC [sexp_fact_def]  
  \\ SIMP_TAC std_ss [List_def,update_nth_1,car_def,cdr_def]
  \\ SIMP_TAC std_ss [GSYM List_def,sexp_fact1_thm]
  \\ SIMP_TAC std_ss [List_def,update_nth_1,car_def,cdr_def]);

val m1_factorial_thm = acl2_fact_certificate 
  |> Q.INST [`l`|->`List [nat n; nat m]`,`s`|->`List []`]
  |> SIMP_RULE std_ss [sexp_fact_thm,set_sepTheory.SEP_CLAUSES,LET_DEF,FACT_EQ_FACTORIAL,
       EVAL ``car (List (x::xs))``,EVAL ``car (cdr (List (x::y::xs)))``]

val _ = save_thm("m1_factorial_thm",m1_factorial_thm);


val _ = export_theory();

