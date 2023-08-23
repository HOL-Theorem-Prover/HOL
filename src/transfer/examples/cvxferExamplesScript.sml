open HolKernel Parse boolLib bossLib;

open arithmeticTheory
open cvTheory transferTheory transferLib cvxferTheory

val _ = new_theory "cvxferExamples";

Overload Num = “cv$Num”
Overload Pair = “cv$Pair”

Definition c2n_def[simp]:
  c2n (Num n) = n /\
  c2n _ = 0
End

(* ----------------------------------------------------------------------
    factorial
   ---------------------------------------------------------------------- *)

(* these two should be automatic when given term FACT to translate *)
Definition factc_def:
  factc c = Num (FACT (c2n c))
End

Theorem FACT_C[transfer_rule]:
  (NC |==> NC) FACT factc
Proof
  simp[NC_def, factc_def, FUN_REL_def]
QED

Theorem FACT_COND:
  !n. FACT n = if n < 2 then 1 else n * FACT (n - 1)
Proof
  Induct_on ‘n’ >> simp[FACT]
QED

Theorem cFACT_COND =
        time (transfer_thm 10 ["FACT"] true (global_ruledb()))
             FACT_COND
          |> SPEC_ALL |> UNDISCH_ALL

(* ----------------------------------------------------------------------
    exponentiation (handling of let)
   ---------------------------------------------------------------------- *)

(* next two should be automatic *)
Definition cv_exp_def:
  cv_exp bc ec = Num (c2n bc ** c2n ec)
End
Theorem EXP_C[transfer_rule]:
  (NC |==> NC |==> NC) $EXP cv_exp
Proof
  simp[cv_exp_def, NC_def, FUN_REL_def]
QED

(* then characterise with an if-then-else *)
Theorem EXP_COND:
  b ** e = if e = 0 then 1
           else if e MOD 2 = 1 then
             b * (b ** (e - 1))
           else let x = b ** (e DIV 2)
                in x * x
Proof
  Cases_on ‘e = 0’ >> rw[]
  >- (Cases_on ‘e’ >> gs[EXP]) >>
  REWRITE_TAC[EXP,TWO, GSYM EXP_ADD, EXP_1] >>
  simp[] >>
  ‘2 * (e DIV 2) = e’ suffices_by simp[] >>
  qspec_then ‘2’ mp_tac DIVISION >> simp[] >>
  ‘e MOD 2 = 0’ by (‘e MOD 2 < 2’ suffices_by DECIDE_TAC >> simp[]) >>
  disch_then $ qspec_then ‘e’ mp_tac >> simp[]
QED

Theorem cEXP = transfer_thm 1 ["EXP"] true (global_ruledb()) (GEN_ALL EXP_COND)
                 |> repeat (UNDISCH o SPEC_ALL)

(* ----------------------------------------------------------------------
    primality checking

    see examples/cv_compute for connecting isprime to built-in prime
    predicate
   ---------------------------------------------------------------------- *)

Definition isprime_aux_def:
  isprime_aux dvs n =
    if dvs < n then
      if n MOD dvs <> 0 then
        isprime_aux (dvs + 2) n
      else F
    else T
Termination
  WF_REL_TAC ‘measure (λ(dvs,n). n - dvs)’
End

(* next two should be automatic *)
Definition isprime_auxc_def:
  isprime_auxc d n = b2c (isprime_aux (c2n d) (c2n n))
End

Theorem isprime_aux_C[transfer_rule]:
  (NC |==> NC |==> BC) isprime_aux isprime_auxc
Proof
  simp[isprime_auxc_def, NC_def, FUN_REL_def]
QED

Theorem cISPRIME_AUX = time (transfer_thm 10 [] true (global_ruledb()))
                            isprime_aux_def
                        |> repeat (UNDISCH o SPEC_ALL)

Definition isprime_def:
  isprime n =
    if n < 2 then F else
    if n = 2 then T else
    if n MOD 2 = 0 then F
    else isprime_aux 3 n
End

(* next two should be automatic *)
Definition isprimec_def:
  isprimec c <=> b2c (isprime (c2n c))
End

Theorem isprime_C[transfer_rule]:
  (NC |==> BC) isprime isprimec
Proof
  simp[isprimec_def, FUN_REL_def, NC_def]
QED

Theorem cISPRIME = transfer_thm 10 [] true (global_ruledb()) isprime_def
                     |> repeat (UNDISCH o SPEC_ALL)

(* ----------------------------------------------------------------------
    primes_upto (includes a list)
   ---------------------------------------------------------------------- *)

Definition primes_upto_def:
  primes_upto upto =
    if 1 < upto then
      if isprime upto then
        upto :: primes_upto (upto - 1)
      else
        primes_upto (upto - 1)
    else
      []
End

(* next two should be automatic *)
Definition primes_uptoc_def:
  primes_uptoc c = seq2cl Num (primes_upto (c2n c))
End

Theorem PRIMES_UPTO_C[transfer_rule]:
  (NC |==> NLC NC) primes_upto primes_uptoc
Proof
  simp[FUN_REL_def, primes_uptoc_def, NC_def, seq2cl_correct]
QED

Theorem cPRIMES_UPTO =
        time (transfer_thm 10 [] true (global_ruledb())) primes_upto_def

(* ----------------------------------------------------------------------
    pairing example, rather artificial
   ---------------------------------------------------------------------- *)

Definition addl_def:
  addl (x,[]) = [] /\
  addl (x,h::t) = (h + x) :: addl (x,t)
End

Theorem addl_oneline:
  addl xl = case oHD (SND xl) of
              NONE => []
            | SOME h => (FST xl + h) :: addl (FST xl, TL (SND xl))
Proof
  Cases_on ‘xl’ >> simp[] >> Cases_on ‘r’ >> simp[addl_def]
QED

Definition addlc_def:
  addlc xl = seq2cl Num (addl (c2n $ cv_fst xl, cl2seq c2n $ cv_snd xl))
End

Theorem NLC_E:
  (!a c. AB a c ==> d c = a) ==>
  NLC AB as c ==> cl2seq d c = as
Proof
  strip_tac >> Induct_on ‘NLC’ >> simp[cl2seq_def]
QED

Theorem NLC_NC:
  !c. NLC NC ns c <=> c = seq2cl Num ns
Proof
  simp[EQ_IMP_THM, FORALL_AND_THM] >>
  conj_tac >- (Induct_on ‘NLC’ >> simp[NC_def]) >>
  Induct_on ‘ns’ >> simp[NC_def]
QED

Theorem cl2seq_c2n_seq2cl[simp]:
  cl2seq c2n (seq2cl Num ns) = ns
Proof
  Induct_on ‘ns’ >> simp[cl2seq_def]
QED

Theorem ADDL_C[transfer_rule]:
  (ACPC NC (NLC NC) |==> NLC NC) addl addlc
Proof
  simp[FUN_REL_def, addlc_def, pairTheory.FORALL_PROD, ACPC_def, PULL_EXISTS,
       NC_def, NLC_NC]
QED

val th = transfer_thm 10 ["addl"] true (global_ruledb()) (GEN_ALL addl_oneline)


val _ = export_theory()
