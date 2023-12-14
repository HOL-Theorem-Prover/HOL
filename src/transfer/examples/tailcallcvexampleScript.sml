open HolKernel Parse boolLib bossLib;

open whileTheory cvxferExamplesTheory

val _ = new_theory "tailcallcvexample";


fun tuplify t =
  let val (f, xs) = strip_comb t
      fun nRATORC n c = if n <= 0 then c
                        else RATOR_CONV (nRATORC (n - 1) c)
      fun build n =
          if n < 0 then ALL_CONV
          else nRATORC n (REWR_CONV (GSYM pairTheory.UNCURRY_DEF)) THENC
               build(n-1)
  in
    build (length xs - 2) t
  end


fun strip_cond t =
  if is_cond t then
    let val (g,th,el) = dest_cond t
        val (rest,e) = strip_cond el
    in
      ((g,th) :: rest, e)
    end
  else ([], t)


val th1 = cISPRIME_AUX
            |> concl
            |> rhs
            |> Term.subst[“isprime_auxc” |-> “f:cv -> cv -> cv”]
            |> SCONV [cvTheory.cv_if_def0,LET_THM]


val t = “
  TAILCALL (λ(uv3:cv, uv1:cv).
           if cv$c2b $ cv_lt uv3 uv1 then
             if cv$c2b (cv_not (cv_eq (cv_mod uv1 uv3) (Num 0)))
             then
               INL (cv_add uv3 (Num 2), uv1)
             else
               INR (Num 0)
           else
             INR (Num 1))
  (UNCURRY f) (a, b)
”

fun UNPBETA_CONV tup t =
  let val t' = mk_comb(pairSyntax.mk_pabs(tup,t), tup)
  in
    SYM (pairLib.PAIRED_BETA_CONV t')
  end

Theorem option_CASE_OPTION_MAP:
  option_CASE (OPTION_MAP f v) n sf =
  option_CASE v n (sf o f)
Proof
  Cases_on ‘v’ >> simp[]
QED

Theorem option_CASE_COND:
  option_CASE (COND p t e) n sf = if p then option_CASE t n sf
                                  else option_CASE e n sf
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem dumb_COND:
  COND g t (COND g t' e) = COND g t e
Proof
  simp[]
QED

Theorem sum_CASE_COND:
  sum_CASE (COND p t e) l r = if p then sum_CASE t l r
                              else sum_CASE e l r
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem COND_CONJ:
  (if p /\ q then t else e) = if p then if q then t else e else e
Proof
  rpt COND_CASES_TAC >> gs[]
QED

val th2 =    SIMP_CONV std_ss [TAILCALL_def,
                               pairTheory.pair_CASE_def, sum_CASE_COND,
                               COND_CONJ
                               ] t;

val th3 = CONV_RULE (RAND_CONV (REWR_CONV (GSYM th2))) th1

val th4 = cISPRIME_AUX |> CONV_RULE (FORK_CONV(tuplify, REWR_CONV th3))
|> DISCH_ALL |> REWRITE_RULE[AND_IMP_INTRO]
|> CONV_RULE (LAND_CONV (UNPBETA_CONV “(UV3:cv,UV1:cv)”))
|> pairLib.PGEN “p:cv # cv”  “(UV3:cv, UV1:cv)”

Theorem FORALL_CV:
  (!c. P c) <=> (!n. P (Num n)) /\ (!c d. P (Pair c d))
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >> Cases_on ‘c’ >> simp[]
QED

val th5 =
  PART_MATCH (last o strip_conj o lhand) TAILREC_GUARD_ELIMINATION_SIMPLER
             (concl th4)
   |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL |> PROVE_HYP th4
   |> DISCH_ALL |> REWRITE_RULE[AND_IMP_INTRO]
   |> SIMP_RULE std_ss []
   |> CONV_RULE (LAND_CONV
                 (RAND_CONV (SCONV[pairTheory.FORALL_PROD, PULL_EXISTS])))
   |> SRULE[pairTheory.FORALL_PROD, sum_CASE_COND, AllCaseEqs()]

val termination_t =
  lhand (concl th5)
    |> Term.subst[“R : cv # cv -> cv # cv -> bool” |->
                  “measure (λ(c,d). c2n (cv_sub d c))”]

Theorem termination_thm:
  ^termination_t
Proof
  simp[pairTheory.FORALL_PROD, PULL_EXISTS] >>
  Cases >> Cases >> simp[cvTheory.c2b_def]
QED

val th6 = MATCH_MP th5 termination_thm
val newc = th6 |> concl |> strip_forall |> #2 |> rand |> rhs |> rator
val def = new_definition("aux'_def", “aux' = ^newc”)

val th7 = (AP_THM def “(c,d):cv # cv”) |> ONCE_REWRITE_RULE [TAILREC_TAILCALL]
                                       |> REWRITE_RULE[SYM def]

val th3' = th3 |> Q.INST[‘f’ |-> ‘CURRY g’]
               |> REWRITE_RULE[pairTheory.UNCURRY_CURRY_THM]
               |> SYM

val th8 = REWRITE_RULE[th3'] th7

val def' = new_definition("A", “A = CURRY aux'”);
val aux'_elim = prove(“aux' = UNCURRY A”, simp[def'])

val A_def = REWRITE_RULE[aux'_elim,pairTheory.CURRY_UNCURRY_THM,
                         pairTheory.UNCURRY_DEF] th8

val almost_there = REWRITE_RULE[SYM def,aux'_elim, pairTheory.UNCURRY_DEF] th6

Theorem BC_E:
  BC b c ==> (b <=> c = Num 1)
Proof
  Cases_on ‘b’ >> simp[cvxferTheory.BC_def]
QED

Theorem atlast =
isprime_aux_C
  |> SRULE[transferTheory.FUN_REL_def,cvxferTheory.NC_def, almost_there]
  |> SPEC_ALL
  |> MATCH_MP (GEN_ALL BC_E)


val _ = export_theory();
