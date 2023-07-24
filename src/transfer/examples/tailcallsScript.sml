open HolKernel Parse boolLib bossLib;

val _ = new_theory "tailcalls";


(* ----------------------------------------------------------------------
    tailcall experiments
   ---------------------------------------------------------------------- *)

(* has an enabled "call" guard *)
Definition hascgd_def[simp]:
  (hascgd et [] x <=> F) /\
  (hascgd et (gcsum :: rest) x <=>
   case gcsum of
     INL (g, c) => g x \/ hascgd et rest x
   | INR (g, _) => ~g x /\ hascgd et rest x)
End

(* execute an enabled call guard *)
Definition execcgd_def[simp]:
  (execcgd et [] x = x) /\
  (execcgd et (gcsum :: rest) x =
   case gcsum of
     INL (g, c) => if g x then c x else execcgd et rest x
   | INR _ => execcgd et rest x)
End

Definition exectmgd_def[simp]:
  (exectmgd et [] x = et x) /\
  (exectmgd e (gcsum :: rest) x =
   case gcsum of
   | INL _ => exectmgd e rest x
   | INR (g, tm) => if g x then tm x else exectmgd e rest x)
End

Definition trec_def:
  trec e f x = exectmgd e f (WHILE (hascgd e f) (execcgd e f) x)
End

Definition tcall_def[simp]:
  tcall et [] f x = et x /\
  (tcall et (INL (g, c) :: rest) f x =
   if g x then f (c x)
   else tcall et rest f x) /\
  (tcall et (INR (g, tm) :: rest) f x =
   if g x then tm x
   else tcall et rest f x)
End

Theorem tcall_calls:
  !e opts x. hascgd e opts x ==>
             tcall e opts f x = f (execcgd e opts x)
Proof
  Induct_on ‘opts’ >> simp[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rw[]
QED

Theorem tcall_terms:
  !e opts x. ~hascgd e opts x ==> tcall e opts f x = exectmgd e opts x
Proof
  Induct_on ‘opts’ >> simp[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rw[]
QED

Theorem tcall_EQN:
  tcall e opts f x =
  if hascgd e opts x then f (execcgd e opts x)
  else exectmgd e opts x
Proof
  rw[]
  >- (drule tcall_calls >> simp[]) >>
  drule tcall_terms >> simp[]
QED

Theorem trec_thm0:
  trec e opts x = if hascgd e opts x then trec e opts (execcgd e opts x)
                  else exectmgd e opts x
Proof
  simp[trec_def] >> simp[SimpLHS, Once whileTheory.WHILE] >> rw[]
QED

Theorem trec_NIL[simp]:
  trec e [] x = e x
Proof
  simp[Once trec_thm0]
QED

Theorem trec_thm:
  WF R /\ (!s. hascgd e opts s ==> R (execcgd e opts s) s) ==>
  !x. trec e opts x = tcall e opts (trec e opts) x
Proof
  strip_tac >>
  first_assum (ho_match_mp_tac o MATCH_MP relationTheory.WF_INDUCTION_THM) >>
  rpt strip_tac >>
  simp[Once trec_thm0] >> rw[]
  >- (drule tcall_calls >> simp[]) >>
  drule tcall_terms >> simp[]
QED

Definition callsites_def[simp]:
  (callsites P [] <=> T) /\
  (callsites P (INR (g, tm) :: rest) <=>
   callsites (λx. P x /\ ~g x) rest) /\
  (callsites P (INL (g, c) :: rest) <=>
   (!x. P x /\ g x ==> P (c x)) /\
   callsites (λx. P x /\ ~g x) rest)
End

Theorem callsites_exec0:
  !P Q. callsites P opts /\ (!x. P x ==> Q x) ==>
        !x. P x /\ hascgd e opts x ==> Q (execcgd e opts x)
Proof
  Induct_on ‘opts’
  >- simp[] >>
  simp_tac (srw_ss())[sumTheory.FORALL_SUM, pairTheory.FORALL_PROD] >>
  rpt strip_tac
  >- (COND_CASES_TAC >- metis_tac[] >> fs[])
  >- (COND_CASES_TAC >- metis_tac[] >> last_x_assum irule >> simp[] >>
      first_assum $ irule_at (Pat ‘callsites _ _’) >> simp[]) >>
  last_x_assum irule >> simp[] >>
  first_assum $ irule_at (Pat ‘callsites _ _’) >> simp[]
QED

Theorem callsites_exec = callsites_exec0 |> Q.SPECL[‘P’, ‘P’] |> SRULE[]

Theorem guard_elimination:
  WF R /\
  (!x. hascgd e opts x ==> R (execcgd e opts x) x) /\
  (!x. P x /\ hascgd e opts x ==> P (execcgd e opts x)) /\
  (!x. P x ==> f x = tcall e opts f x) ==>
  (!x. P x ==> f x = trec e opts x)
Proof
  strip_tac >>
  first_assum (ho_match_mp_tac o MATCH_MP relationTheory.WF_INDUCTION_THM) >>
  rw[] >> rw[tcall_EQN]
  >- (drule_all trec_thm >> disch_then (fn th => simp[SimpRHS, th]) >>
      simp[tcall_EQN]) >>
  drule_all trec_thm >> disch_then (fn th => simp[SimpRHS, th]) >>
  simp[tcall_EQN]
QED

Theorem COND_moveright:
  COND g1 (COND g2 t e1) e2 =
  COND (g1 /\ g2) t (COND g1 e1 e2)
Proof
  rw[] >> gs[]
QED

open cvxferExamplesTheory

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
            |> SCONV [cvTheory.cv_if_def0,COND_moveright,LET_THM]


val t = “tcall (λ(x:cv,y:cv). Num 1)
  [INL ((λ(x:cv,y:cv).
          c2b (cv_lt x y) /\ c2b (cv_not (cv_eq (cv_mod y x) (Num 0)))),
        (λ(x:cv,y:cv). (cv_add x (Num 2), y)));
   INR ((λ(x,y). c2b (cv_lt x y)), (λ(x:cv,y:cv). Num 0))]
   (UNCURRY f) (a,b)”;

fun UNPBETA_CONV tup t =
  let val t' = mk_comb(pairSyntax.mk_pabs(tup,t), tup)
  in
    SYM (pairLib.PAIRED_BETA_CONV t')
  end

val th2 =    SIMP_CONV std_ss [tcall_EQN, hascgd_def, execcgd_def, exectmgd_def,
                               pairTheory.pair_CASE_def] t;

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
  PART_MATCH (last o strip_conj o lhand) guard_elimination (concl th4)
   |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL |> PROVE_HYP th4
   |> DISCH_ALL |> REWRITE_RULE[AND_IMP_INTRO]
   |> SIMP_RULE std_ss []
   |> CONV_RULE (LAND_CONV
                 (RAND_CONV (SCONV[pairTheory.FORALL_PROD, PULL_EXISTS])))
   |> REWRITE_RULE[]
   |> CONV_RULE (RAND_CONV (SCONV[pairTheory.FORALL_PROD]))

val termination_t =
  lhand (concl th5)
    |> Term.subst[“R : cv # cv -> cv # cv -> bool” |->
                  “measure (λ(c,d). c2n (cv_sub d c))”]

val termination_thm = TAC_PROOF(([], termination_t),
                                simp[pairTheory.FORALL_PROD] >> Cases >> Cases >>
                                simp[cvTheory.c2b_def])

val th6 = MATCH_MP th5 termination_thm
val newc = th6 |> concl |> strip_forall |> #2 |> rand |> rhs |> rator
val def = new_definition("aux'_def", “aux' = ^newc”)

val trec_expanded = MATCH_MP trec_thm termination_thm
val th7 = (AP_THM def “(c,d):cv # cv”) |> ONCE_REWRITE_RULE [trec_expanded]
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
