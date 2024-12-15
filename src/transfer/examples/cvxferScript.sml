open HolKernel Parse boolLib bossLib;

open transferLib transferTheory cvTheory arithmeticTheory

val _ = new_theory "cvxfer";

Overload Num = “cv$Num”
Overload Pair = “cv$Pair”

Definition NC_def:
  NC n c <=> c = Num n
End

Theorem NC_rule[transfer_rule]:
  NC n (Num n)
Proof
  simp[NC_def]
QED

Definition BC_def:
  (BC T c <=> c = Num 1) /\
  (BC F c <=> c = Num 0)
End

Theorem BC_THM[simp]:
  BC b (b2c b)
Proof
  Cases_on ‘b’ >> simp[BC_def]
QED

Theorem BC_rule[transfer_rule]:
  BC T (Num 1) /\ BC F (Num 0)
Proof
  simp[BC_def]
QED

Theorem total_NC[transfer_safe]:
  transfer$total NC
Proof
  simp[total_def, NC_def]
QED

Theorem left_unique_NC[transfer_safe]:
  left_unique NC
Proof
  simp[left_unique_def, NC_def]
QED

Theorem right_unique_NC[transfer_safe]:
  right_unique NC
Proof
  simp[right_unique_def, NC_def]
QED

Theorem bi_unique_NC:
  bi_unique NC
Proof
  simp[bi_unique_implied, left_unique_NC, right_unique_NC]
QED

Theorem left_unique_BC[transfer_safe]:
  left_unique BC
Proof
  simp[left_unique_def] >> ntac 2 Cases >> simp[BC_def]
QED

Theorem right_unique_BC[transfer_safe]:
  right_unique BC
Proof
  simp[right_unique_def] >> ntac 2 Cases >> simp[BC_def]
QED

Definition cv_not_def:
  cv_not (Num 0) = Num 1 /\
  cv_not (Num 1) = Num 0 /\
  cv_not c = c
End

Theorem NOT_C[transfer_rule]:
  (BC |==> BC) $~ cv_not
Proof
  simp[FUN_REL_def] >>
  Cases >> simp[BC_def, PULL_EXISTS, cv_not_def]
QED

Theorem EQ_C[transfer_rule]:
  (NC |==> NC |==> BC) $= cv_eq
Proof
  simp[FUN_REL_def, NC_def]
QED

Theorem ADD_C[transfer_rule]:
  (NC |==> NC |==> NC) $+ cv_add
Proof
  simp[FUN_REL_def, NC_def]
QED

Theorem MUL_C[transfer_rule]:
  (NC |==> NC |==> NC) $* cv_mul
Proof
  simp[FUN_REL_def, NC_def]
QED

Theorem SUB_C[transfer_rule]:
  (NC |==> NC |==> NC) $- cv_sub
Proof
  simp[FUN_REL_def, NC_def]
QED

Theorem COND_C[transfer_rule]:
  (BC |==> R |==> R |==> R) COND cv_if
Proof
  rw[FUN_REL_def] >> rename [‘BC bool c’] >>
  Cases_on ‘bool’ >> gvs[BC_def, c2b_def]
QED

Theorem LESS_C[transfer_rule]:
  (NC |==> NC |==> BC) $< cv_lt
Proof
  simp[FUN_REL_def, NC_def] >> rw[] >> simp[BC_def]
QED

Theorem MOD_C[transfer_rule]:
  (NC |==> NC |==> NC) $MOD cv_mod
Proof
  simp[FUN_REL_def, NC_def]
QED

Theorem DIV_C[transfer_rule]:
  (NC |==> NC |==> NC) $DIV cv_div
Proof
  simp[FUN_REL_def, NC_def]
QED

Theorem RRANGE_NC[transfer_simp]:
  RRANGE NC c <=> ?n. c = Num n
Proof
  simp[relationTheory.RRANGE, NC_def]
QED

(* lists of encodable things *)
Inductive NLC:
[~nil:]
  NLC AB [] (Num 0)
[~cons:]
  !n c ns cs. AB n c /\ NLC AB ns cs ==> NLC AB (n::ns) (Pair c cs)
End

Theorem NLC_SIMP[simp]:
  (NLC AB [] c <=> c = Num 0) /\
  (NLC AB xs (Num 0) <=> xs = []) /\
  (NLC AB (x::xs) cv <=> ?c cs. cv = Pair c cs /\ AB x c /\ NLC AB xs cs) /\
  (NLC AB xs (Pair c cs) <=> ?h t. xs = h::t /\ AB h c /\ NLC AB t cs)
Proof
  rpt conj_tac >> simp[SimpLHS, Once NLC_cases]
QED

Theorem CONS_C[transfer_rule]:
  (AB |==> NLC AB |==> NLC AB) CONS Pair
Proof
  simp[FUN_REL_def, NLC_cons]
QED

Theorem NIL_C[transfer_rule] = SPEC_ALL NLC_nil

Theorem NLC_total[transfer_safe]:
  total AB ==> total (NLC AB)
Proof
  simp[total_def] >> strip_tac >> Induct >> metis_tac[NLC_rules]
QED

Theorem NLC_left_unique[transfer_safe]:
  left_unique AB ==> left_unique (NLC AB)
Proof
  simp[left_unique_def] >> strip_tac >> Induct_on ‘NLC’ >> rw[] >>
  pop_assum mp_tac >> simp[Once NLC_cases] >> metis_tac[]
QED

Theorem NLC_right_unique[transfer_safe]:
  right_unique AB ==> right_unique (NLC AB)
Proof
  simp[right_unique_def] >> strip_tac >> Induct_on ‘NLC’ >> rw[] >>
  pop_assum mp_tac >> simp[Once NLC_cases] >> metis_tac[]
QED

Definition cl2seq_def:
  cl2seq d (Num 0) = [] /\
  cl2seq d (Pair c cs) = d c :: cl2seq d cs
End

Definition seq2cl_def[simp]:
  seq2cl m [] = Num 0 /\
  seq2cl m (h::t) = Pair (m h) (seq2cl m t)
End

Theorem seq2cl_correct:
  (!a. AB a (mk a)) ==>
  NLC AB as (seq2cl mk as)
Proof
  strip_tac >> Induct_on ‘as’ >> simp[NLC_rules]
QED

Theorem RRANGE_NLC[transfer_simp]:
  RRANGE (NLC AB) n <=> ?l. NLC AB l n
Proof
  simp[relationTheory.RRANGE]
QED

(* pairing *)

Definition ACPC_def:
  ACPC AB CD (x,y) c <=> ?c1 c2. c = Pair c1 c2 /\ AB x c1 /\ CD y c2
End

Theorem total_ACPC[transfer_safe]:
  total AB /\ total CD ==> total (ACPC AB CD)
Proof
  simp[total_def, ACPC_def, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem left_unique_ACPC[transfer_safe]:
  left_unique AB /\ left_unique CD ==> left_unique (ACPC AB CD)
Proof
  simp[left_unique_def, ACPC_def, pairTheory.FORALL_PROD, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem right_unique_ACPC[transfer_safe]:
  right_unique AB /\ right_unique CD ==> right_unique (ACPC AB CD)
Proof
  simp[right_unique_def, ACPC_def, pairTheory.FORALL_PROD, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem COMMA_C[transfer_rule]:
  (AB |==> CD |==> ACPC AB CD) $, Pair
Proof
  simp[ACPC_def, FUN_REL_def]
QED

Theorem FST_C[transfer_rule]:
  (ACPC AB CD |==> AB) FST cv_fst
Proof
  simp[ACPC_def, FUN_REL_def, pairTheory.FORALL_PROD, PULL_EXISTS]
QED

Theorem SND_C[transfer_rule]:
  (ACPC AB CD |==> CD) SND cv_snd
Proof
  simp[ACPC_def, FUN_REL_def, pairTheory.FORALL_PROD, PULL_EXISTS]
QED

Theorem RRANGE_ACPC[transfer_simp]:
  RRANGE (ACPC AB CD) bd <=>
  ?b d. bd = Pair b d /\ RRANGE AB b /\ RRANGE CD d
Proof
  simp[relationTheory.RRANGE, ACPC_def, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

(* ----------------------------------------------------------------------
    options
   ---------------------------------------------------------------------- *)

Definition OPTC_def:
  (OPTC AC NONE c <=> c = Num 0) /\
  (OPTC AC (SOME a) c <=> ?c0. c = Pair (Num 1) c0 /\ AC a c0)
End

Theorem total_OPTC[transfer_safe]:
  total ACv ==> total (OPTC ACv)
Proof
  simp[total_def, OPTC_def, optionTheory.FORALL_OPTION]
QED

Theorem left_unique_OPTC[transfer_safe]:
  left_unique ACv ==> left_unique (OPTC ACv)
Proof
  simp[left_unique_def, OPTC_def, optionTheory.FORALL_OPTION, PULL_EXISTS]
QED

Theorem right_unique_OPTC[transfer_safe]:
  right_unique ACv ==> right_unique (OPTC ACv)
Proof
  simp[right_unique_def, OPTC_def, optionTheory.FORALL_OPTION, PULL_EXISTS]
QED

Theorem OPTC_NONE[transfer_rule]:
  OPTC ACv NONE (Num 0)
Proof
  simp[OPTC_def]
QED

Theorem OPTC_SOME[transfer_rule]:
  (ACv |==> OPTC ACv) SOME (Pair (Num 1))
Proof
  simp[FUN_REL_def, OPTC_def]
QED

Definition mkcvopt_def:
  mkcvopt mk NONE = Num 0 /\
  mkcvopt mk (SOME x) = Pair (Num 1) (mk x)
End

Definition destcvopt_def:
  destcvopt d (Num 0) = NONE /\
  destcvopt d (Pair (Num 1) c) = SOME (d c)
End

Theorem destmk_cvopt[simp]:
  (!a. d (m a) = a) ==>
  destcvopt d (mkcvopt m opt) = opt
Proof
  Cases_on ‘opt’ >> simp[mkcvopt_def, destcvopt_def]
QED

Theorem option_CASE_C[transfer_rule]:
  (OPTC ACv |==> BCv |==> (ACv |==> BCv) |==> BCv) option_CASE
  (λocv bcv f. cv_if (cv_ispair ocv) (f (cv_snd ocv)) bcv)
Proof
  rw[FUN_REL_def] >> rename [‘OPTC ACv aopt ocv’] >>
  Cases_on ‘aopt’ >> gvs[OPTC_def, c2b_def]
QED

Theorem OHD_C[transfer_rule]:
  (NLC ACv |==> OPTC ACv) oHD
  (λc. cv_if (cv_ispair c) (Pair (Num 1) (cv_fst c)) (Num 0))
Proof
  simp[FUN_REL_def] >> Cases >>
  simp[Once NLC_cases, PULL_EXISTS, OPTC_def, c2b_def]
QED

Theorem TL_C[transfer_rule]:
  (NLC ACv |==> NLC ACv) TL cv_snd
Proof
  rw[FUN_REL_def] >> rename [‘NLC _ (TL xs) (cv_snd cv)’]>>
  Cases_on ‘xs’ >> gvs[]
QED

val _ = export_theory();
