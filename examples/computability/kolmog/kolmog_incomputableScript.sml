open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmogorov_complexityTheory invarianceResultsTheory boolListsTheory
open churchDBTheory
open recursivefnsTheory primrecfnsTheory prtermTheory

val _ = new_theory "kolmog_incomputable"

(*  Proving kolmog is not computable  *)

(* longest it takes machines of size n to terminate *)
val tmax_def = Define`
  tmax n = MAX_SET {t | ∃m. terminated (steps t (mk_initial_state m 0)) ∧
                            (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ∧
                            ( ℓ  m = n) }
`;

(* the machine of size n, that takes that longest time to terminate,
   the "busy beaver" if you will
*)
val BB_def = Define`
  BB n = @m. terminated (steps (tmax n) (mk_initial_state m 0)) ∧ (ℓ m = n)
`;

val HALT_def = Define`
  HALT = {(M,x)| ∃t. terminated (steps t (mk_initial_state M x)) }
`;

val _ = overload_on ("N2T",``λt. toTerm (numdB t)``)

(* a machine M' encoding one computation, that being M applied to x. *)
val prime_tm_def = Define`
  prime_tm M x = dBnum (fromTerm (K @@ (N2T M @@ church x)))
`;

Theorem prime_tm_corr:
  Phi (prime_tm M x) 0 = Phi M x
Proof
  simp[prime_tm_def,Phi_def,K_lemma]
QED

(** up to here **)

val OGENLIST_def = Define`
  OGENLIST f 0 = [] ∧
  OGENLIST f (SUC n) = OGENLIST f n ++ (case f n of NONE => [] | SOME r => [r])
`;

val Z_lam_def = Define‘
  Z_lam M n =
   λx. case comp_count (mk_initial_state M 0) of
           NONE => NONE
         | SOME s =>
           let results =
                 OGENLIST  (λmi. if terminated (steps s (mk_initial_state mi 0))
                                 then
                                   SOME (cs_to_num (steps s
                                                      (mk_initial_state mi 0)))
                                 else NONE)
                           (4**n DIV 2)
           in
             SOME (LEAST x. ¬MEM x results ∧ ℓ x = 2*n)
’;

(* cap3 f (x,y,z) = (x,y,f z) *)
val cap3_def = Define`cap3 = LAM "f" (
  LAM "p" (
    cpair @@ (cfst @@ VAR "p")
          @@ (cpair @@ (cfst @@ (csnd @@ VAR "p"))
                    @@ (VAR "f" @@ (csnd @@ (csnd @@ VAR "p"))))
  )
)`;

val cap3_eqn = brackabs.brackabs_equiv [] cap3_def

Theorem cap3_behaviour:
  cap3 @@ f @@ (cvpr x (cvpr y z)) == cvpr x (cvpr y (f @@ z))
Proof
  simp_tac (bsrw_ss()) [cap3_eqn, churchpairTheory.cpair_behaviour]
QED

Theorem FV_cap3[simp]: FV cap3 = {}
Proof simp[EXTENSION,cap3_def]
QED

val dt0_def = Define`dt0 = LAM "p" (LAM "ms" (LAM "i"
 (cfilter
   @@ (B @@ VAR "p" @@ (B @@ csnd @@ csnd ) )
   @@ (cmap @@ (cap3 @@ cforce_num)
            @@ (cfilter
                  @@ (B @@ cbnf @@ (B @@ csnd @@ csnd) ))
                  @@ (cmap
                      @@ (LAM "pair" (
                             (LAM "m" (LAM "j" (
                                cpair @@ VAR "m"
                                      @@ (cpair
                                           @@ VAR "j"
                                           @@ (csteps
                                                @@ VAR "i"
                                                @@ (cdAPP @@ VAR "m"
                                                          @@ VAR "j"))))))
                               @@ (cfst @@ VAR"pair") @@ (csnd @@ VAR "pair")))
                                        @@ (VAR "ms") )  )
 ) ) )`;

(*val dt_def = Define`dt = LAM "p" (LAM "ms"
 (cfindleast @@ (LAM "n" (dt0 @@ VAR "p" @@ VAR "ms" @@ VAR"n" @@ cB T @@ (K @@ (K @@ cB F)) ) )
             @@ (LAM "n" (chd @@ (dt0 @@ VAR "p" @@ VAR "ms" @@ VAR"n")) ) ))`

val size_dovetail_def = Define`size_dovetail0 P ms i = let results = map (λ(m,j). steps i (mk_initial_state m j) ms ); term_results = filter terminsted results;`

(* Make fn which takes n and gives list of nats st log 2 nats = n *)
*)

val log2list_def = Define`log2list n = GENLIST (λx. x+2**n) (2**n) `

val clog2list_def = Define`clog2list =
  LAM "n" (ctabulate @@ (cexp @@ church 2 @@ VAR "n")
                     @@ (cplus @@ (cexp @@ church 2 @@ VAR "n")))`

Theorem FV_clog2list[simp]:
  FV clog2list = {}
Proof
  rw[clog2list_def,EXTENSION]
QED

val clog2list_eqn = brackabs.brackabs_equiv [] clog2list_def


Theorem clog2list_behaviour:
  clog2list @@ church n == cvlist (MAP church (log2list n))
Proof
  asm_simp_tac(bsrw_ss())[clog2list_eqn,log2list_def,MAP_GENLIST,
                          ctabulate_cvlist] >>
  HO_MATCH_MP_TAC cvlist_genlist_cong >>
  simp_tac(bsrw_ss())[churchnumTheory.cplus_behaviour,ADD_COMM]
QED

val computable_def = Define`
  computable (f:num->num) <=> ∃i. ∀n. Phi i n = SOME (f n)
`;


(*
val narg_kolmog_def = Define`narg_kolmog x = bl2n (arg_kolmog x)`;

*)



val core_complexity0_def = Define`
  core_complexity0 x = THE (core_complexity (λy. on2bl (Phi (bl2n y) 0)) x)
`;

Theorem core_complexity0_exists:
  ∀x. ∃y. core_complexity (λy. on2bl (Phi (bl2n y) 0)) x = SOME y
Proof
  rw[core_complexity_def,EXTENSION] >> simp[Phi_def] >>
  qexists_tac`n2bl (dBnum (fromTerm (K @@ church (bl2n x))))` >> simp[on2bl_def] >>
  qexists_tac`bl2n x` >> rw[num_bool_inv] >>
  qexists_tac`church (bl2n x)` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED





Theorem Phi_x_0:
  ∀y. ∃x. Phi x 0 = SOME y
Proof
  rw[] >> simp[Phi_def] >>
  qexists_tac` (dBnum (fromTerm (K @@ church y)))` >> simp[bool_num_inv] >>
  qexists_tac`church y` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED

Theorem Phi_bl2nx_0:
  ∀y. ∃x. Phi (bl2n x) 0 = SOME y
Proof
  rw[] >> simp[Phi_def] >>
  qexists_tac`n2bl (dBnum (fromTerm (K @@ church y)))` >> simp[bool_num_inv] >>
  qexists_tac`church y` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED



Theorem core_complexity0_thm:
  core_complexity0 x = (MIN_SET {LENGTH p |  on2bl (Phi (bl2n p) 0) = SOME x})
Proof
  fs[core_complexity0_def,core_complexity_def] >>
  Cases_on`{y | on2bl (Phi (bl2n y) 0) = SOME x} = ∅` >>
  fs[] >> `∃y. on2bl (Phi (bl2n y) 0) = SOME x` by 
    (fs[on2bl_def] >> `∃k. Phi (bl2n k) 0 = SOME (bl2n x)` by fs[Phi_bl2nx_0] >>
     qexists_tac`k` >> qexists_tac`bl2n x` >> rw[bool_num_inv]) >>
  `y∈{y | on2bl (Phi (bl2n y) 0) = SOME x}` by fs[] >> metis_tac[MEMBER_NOT_EMPTY]
QED

(*

Theorem arg_plain_kolmog_exists:
  ∃q. Phi q 0 = SOME x ∧ LENGTH (n2bl q) = plain_kolmog x
Proof
  fs[plain_kolmog_thm] >> `{LENGTH p | Phi (bl2n p) 0 = SOME x} <> {}` by
    fs[EXTENSION,Phi_bl2nx_0] >>
  `MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME x} ∈
    {LENGTH p | Phi (bl2n p) 0 = SOME x}`
    by fs[MIN_SET_LEM] >>
  ‘IMAGE LENGTH {p | Phi (bl2n p) 0 = SOME x} =
   {LENGTH p | Phi (bl2n p) 0 = SOME x}’
     by fs[IMAGE_DEF] >>
  ‘MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME x} ∈
     IMAGE LENGTH {p | Phi (bl2n p) 0 = SOME x}’ by
    metis_tac[] >>
  ‘∃q1. MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME x} = LENGTH q1 ∧
        q1 ∈ {p | Phi (bl2n p) 0 = SOME x}’
     by metis_tac[IN_IMAGE] >>
  qexists_tac`bl2n q1` >> fs[]
QED

*)

val tPhi_def = Define‘
  tPhi mi x t ⇔
    terminated (steps t (mk_initial_state mi x)) ∧
    ∀t'. t' < t ⇒ ¬terminated (steps t' (mk_initial_state mi x))
’;

Theorem PhiSOME_tPhi:
  Phi m x = SOME y ⇒ ∃t. tPhi m x t
Proof
  simp[tPhi_def, Phi_steps, CaseEq "option", comp_count_def, OLEAST_EQ_SOME] >>
  metis_tac[]
QED

(* complicated(!) leastness characterisation across various dimensions.
   Machine m is:
     1. smallest (by size (ℓ)) machine returning x
     2. then, quickest of those
     3. then, smallest by raw index of those
*)
val arg_plain_pred_def = Define‘
  arg_plain_pred x m <=>
    Phi m 0 = SOME x /\
     ℓ m = MIN_SET { ℓ ni | Phi ni 0 = SOME x} ∧
    ∃t. tPhi m 0 t ∧
        (∀n u. ℓ n = ℓ m ∧ tPhi n 0 u ∧ Phi n 0 = SOME x ⇒ t ≤ u) ∧
        (∀n. ℓ n = ℓ m ∧ tPhi n 0 t ∧ Phi n 0 = SOME x ⇒ m ≤ n)
’;

Theorem arg_plain_pred_exists :
  ∀x. ∃m. arg_plain_pred x m
Proof
  simp[arg_plain_pred_def] >> qx_gen_tac ‘y’ >> simp[PULL_EXISTS] >>
  qabbrev_tac ‘mis = { i | Phi i 0 = SOME y}’ >>
  qabbrev_tac ‘sizes = IMAGE ℓ mis’ >>
  ‘sizes ≠ ∅’ by simp[Abbr‘sizes’, Abbr‘mis’, EXTENSION, Phi_x_0] >>
  qabbrev_tac ‘lsz = MIN_SET sizes’ >>
  qabbrev_tac ‘small_mis = { i | i ∈ mis ∧ ℓ i = lsz}’ >>
  ‘small_mis ≠ ∅’
     by (simp[Abbr‘small_mis’, EXTENSION, Abbr‘lsz’, Abbr‘sizes’] >>
         DEEP_INTRO_TAC MIN_SET_ELIM >> simp[PULL_EXISTS] >> rw[] >>
         metis_tac[]) >>
  ‘∀m. m ∈ small_mis ⇔ ℓ m = lsz ∧ Phi m 0 = SOME y’
     by (simp[Abbr‘small_mis’, Abbr‘mis’, Abbr‘lsz’] >> metis_tac[]) >>
  qabbrev_tac ‘times = { t | ∃m. tPhi m 0 t ∧ m ∈ small_mis}’ >>
  qabbrev_tac ‘fastest = MIN_SET times’ >>
  qabbrev_tac ‘fastest_mis = { m | tPhi m 0 fastest ∧ m ∈ small_mis }’ >>
  ‘fastest_mis ≠ ∅’
    by (simp[Abbr‘fastest_mis’, Abbr‘fastest’, Abbr‘times’, EXTENSION] >>
        DEEP_INTRO_TAC MIN_SET_ELIM >> simp[PULL_EXISTS] >>
        simp[EXTENSION] >> metis_tac[MEMBER_NOT_EMPTY, PhiSOME_tPhi]) >>
  ‘∃m. m ∈ fastest_mis’ by metis_tac [MEMBER_NOT_EMPTY] >>
  map_every qexists_tac [‘MIN_SET fastest_mis’, ‘fastest’] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> simp[] >> qx_gen_tac ‘M’ >> strip_tac >>
  ‘M ∈ small_mis’ by fs[Abbr‘fastest_mis’] >> rpt conj_tac
  >- metis_tac[]
  >- (pop_assum mp_tac >> simp[] >>
      simp[Abbr‘lsz’, Abbr‘sizes’, Abbr‘mis’] >> strip_tac >> AP_TERM_TAC >>
      simp[EXTENSION])
  >- fs[Abbr‘fastest_mis’]
  >- (qx_genl_tac [‘N’,‘u’] >> strip_tac >>
      ‘N ∈ small_mis’ by metis_tac[] >>
      ‘u ∈ times’ by (simp[Abbr‘times’] >> metis_tac[]) >>
      simp[Abbr‘fastest’] >> metis_tac[MIN_SET_LEM, MEMBER_NOT_EMPTY])
  >- (qx_gen_tac ‘N’ >> strip_tac >> ‘N ∈ fastest_mis’ suffices_by metis_tac[]>>
      simp[Abbr‘fastest_mis’] >> metis_tac[])
QED

Theorem arg_plain_pred_unique :
   ∀x m1 m2. arg_plain_pred x m1 ∧ arg_plain_pred x m2 ⇒ (m1 = m2)
Proof
  rw[arg_plain_pred_def] >> ‘ℓ m1 = ℓ m2’ by simp[] >>
  rename [‘ℓ m1 = ℓ m2’, ‘tPhi m1 0 t1’, ‘tPhi m2 0 t2’] >>
  ‘t1 ≤ t2 ∧ t2 ≤ t1’ by metis_tac[] >> ‘t1 = t2’ by simp[] >>
  pop_assum SUBST_ALL_TAC >> ‘m1 ≤ m2 ∧ m2 ≤ m1’ by metis_tac[] >>
  simp[]
QED

val arg_plain_kolmog_def = new_specification("arg_plain_kolmog_def",
  ["arg_plain_kolmog"], CONV_RULE SKOLEM_CONV arg_plain_pred_exists);

Theorem arg_plain_kolmog_unique :
  (arg_plain_kolmog x = y) ⇔ arg_plain_pred x y
Proof
  metis_tac[arg_plain_kolmog_def, arg_plain_pred_unique]
QED

Theorem PhiSOME_terminated :
  (Phi m x = SOME y) ⇒
  ∃t cs0. cs0 = mk_initial_state m x ∧ y = cs_to_num (steps t cs0) ∧
          terminated (steps t cs0)
Proof
  simp[Phi_steps, CaseEq "option"] >> rw[] >>
  metis_tac[correctness_on_termination]
QED

Theorem arg_plain_kolmog_raw_props =
  SIMP_RULE (srw_ss()) [arg_plain_pred_def] arg_plain_kolmog_def

Theorem Phi_arg_pl_kolmog[simp]:
  Phi (arg_plain_kolmog y) 0 = SOME y
Proof
  simp[arg_plain_kolmog_raw_props]
QED

Theorem arg_plain_kolmog_leastsize:
  (Phi N 0 = SOME y) ⇒ ℓ (arg_plain_kolmog y) ≤ ℓ N
Proof
  strip_tac >> simp[arg_plain_kolmog_raw_props] >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> simp[EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Theorem MIN_SET_L_PHI_NON_EMPTY:
  {LENGTH p | Phi (bl2n p) 0 = SOME y} <> {}
Proof
  fs[EXTENSION,Phi_bl2nx_0]
QED

Theorem oPhi_bl2nx_0:
  ∃p. on2bl (Phi (bl2n p) 0) = SOME y
Proof
  fs[on2bl_def] >> `∃p. Phi (bl2n p) 0 = SOME (bl2n y)` by fs[Phi_bl2nx_0] >>
  qexists_tac`p` >> qexists_tac`bl2n y` >> rw[]
QED

Theorem MIN_SET_L_o_PHI_NON_EMPTY:
  {LENGTH p | on2bl (Phi (bl2n p) 0) = SOME y} <> {}
Proof
  fs[EXTENSION,oPhi_bl2nx_0]
QED



Theorem core_complexity0_smallest:
  on2bl (Phi k 0) = SOME y ⇒ core_complexity0 y ≤ ℓ k
Proof
  simp[core_complexity0_thm] >> strip_tac >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (simp[EXTENSION,oPhi_bl2nx_0]) >>
  fs[PULL_EXISTS]
QED

Theorem core_complexity0_props:
  ∀y. ∃z. core_complexity0 y = ℓ z ∧ on2bl (Phi z 0) = SOME y
Proof
  simp[core_complexity0_thm] >> strip_tac >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- simp[MIN_SET_L_o_PHI_NON_EMPTY] >> qexists_tac ‘bl2n p’ >> simp[]
QED



Theorem ELL_EQ_0[simp]:
  ℓ x = 0 ⇔ (x = 0)
Proof
  simp[Once num_to_bool_list_def] >> rw[]
QED

val TWO_TIMES_DIV = Q.prove(
  ‘(2 * n DIV 2 = n) ∧ (2 * n + 1) DIV 2 = n ∧ (2 * n + 2) DIV 2 = n + 1’,
  reverse (rpt conj_tac)
  >- (‘2 * n + 2 = 2 * (n + 1)’ by simp[LEFT_ADD_DISTRIB] >>
      simp[] >> metis_tac[MULT_DIV, DECIDE “0 < 2n”, MULT_COMM]) >>
  metis_tac[DIV_MULT, DECIDE “1 < 2n”, MULT_COMM, MULT_DIV, DECIDE “0 < 2n”]);
val _ = augment_srw_ss [rewrites [TWO_TIMES_DIV]];

val BIT2_smaller = Q.prove(
  ‘x ≠ 0 ∧ EVEN x ⇒ (x - 2) DIV 2 < x’,
  Cases_on ‘x’ >> simp[EVEN] >> rename [‘EVEN m’] >> Cases_on ‘m’ >>
  simp[EVEN,ADD1,DIV_LT_X]);
val BIT1_smaller = Q.prove(
  ‘x ≠ 0 ⇒ (x - 1) DIV 2 < x’,
  Cases_on ‘x’ >> simp[ADD1, DIV_LT_X]);

Theorem ELL_MONOTONE[simp]:
  ∀x y. x ≤ y ⇒ ℓ x ≤ ℓ y
Proof
  completeInduct_on ‘x’ >> qspec_then ‘x’ mp_tac num_to_bool_list_def >> rw[] >>
  qspec_then ‘y’ mp_tac num_to_bool_list_def >> rw[] >>
  first_x_assum irule >> simp[BIT1_smaller, BIT2_smaller, DIV_LE_MONOTONE] >>
  ‘∃y0. y = 2 * y0’ by metis_tac[EVEN_EXISTS] >> Cases_on ‘y0’ >>
  fs[ADD1, LEFT_ADD_DISTRIB] >>
  ‘∃x0. x = 2 * x0 + 1’ by metis_tac[ODD_EXISTS, ADD1, EVEN_ODD] >>
  Cases_on ‘x0’ >> fs[ADD1, LEFT_ADD_DISTRIB]
QED

Theorem ELL_log2list:
  ∀i n. ℓ n = i ⇔ MEM (n + 1) (log2list i)
Proof
  simp[log2list_def, MEM_GENLIST, PULL_EXISTS] >>
  ‘∀j i. ℓ j = i ⇔ 2 ** i ≤ j + 1 ∧ j + 1 < 2 ** (i + 1)’
     suffices_by (
       rw[] >> reverse eq_tac >> rw[]
       >- simp[LT_SUB_RCANCEL, EXP_ADD] >>
       qexists_tac ‘n - (2 ** i - 1)’ >>
       simp[SUB_LEFT_LESS] >> fs[EXP_ADD]
     ) >>
  completeInduct_on ‘j’ >>
  simp[Once num_to_bool_list_def] >> rw[] >> fs[]
  >- (Cases_on ‘i’ >> fs[EXP] >> fs[DECIDE “x ≤ 1n ⇔ x = 0 ∨ x = 1”]) >>
  simp[DECIDE “SUC x = y ⇔ y ≠ 0 ∧ x = y - 1”] >>
  simp[BIT1_smaller, BIT2_smaller] >> csimp[] >>
  Cases_on ‘i’ >> simp[]
  >- (fs[EVEN_EXISTS] >> rw[] >> fs[] >> rename [‘j0 ≠ 0’] >> Cases_on ‘j0’ >>
      simp[ADD1, LEFT_ADD_DISTRIB] >> rename [‘2 ** n ≤ m + 1 /\ m + 1 < _’] >>
      simp[EXP_ADD]) >>
  fs[GSYM ODD_EVEN, ODD_EXISTS, ADD1, EXP_ADD]
QED

Theorem MEM_log2list:
  MEM x (log2list i) ⇔ 0 < x ∧ ℓ (x - 1) = i
Proof
  csimp[ELL_log2list] >> Cases_on ‘x’ >> simp[] >>
  simp[log2list_def, MEM_GENLIST]
QED

Theorem ELL_LE[simp]:
  ℓ k <= k
Proof
  completeInduct_on`k` >> qspec_then ‘k’ mp_tac num_to_bool_list_def >> rw[]
  >- (`(k-2) DIV 2 < k` by fs[BIT2_smaller] >>
      `ℓ ((k-2) DIV 2) ≤ ((k-2) DIV 2)` by fs[] >>
      `ℓ ((k − 2) DIV 2) < k` by fs[] >> fs[])
  >- (`(k-1) DIV 2 < k` by fs[BIT1_smaller] >>
      `ℓ ((k-1) DIV 2) ≤ ((k-1) DIV 2)` by fs[] >>
      `ℓ ((k − 1) DIV 2) < k` by fs[] >> fs[] )
QED

Theorem ELL_LT[simp]:
  ℓ k < k ⇔ 1 < k
Proof
  completeInduct_on ‘k’ >> simp[Once num_to_bool_list_def] >> rw[]
  >- (‘(k - 2) DIV 2 < k’ by simp[BIT2_smaller]>>
      Cases_on ‘1 < (k - 2) DIV 2’
      >- (‘ℓ ((k - 2) DIV 2) < (k - 2) DIV 2’ by metis_tac[] >>
          simp[]) >>
      ‘¬(ℓ ((k - 2) DIV 2) < (k - 2) DIV 2)’ by metis_tac[] >>
      ‘ℓ ((k - 2) DIV 2) = (k - 2) DIV 2’ by metis_tac[LESS_OR_EQ, ELL_LE] >>
      fs[NOT_LESS_EQUAL, X_LT_DIV] >>
      ‘k ≠ 0’ by (strip_tac >> fs[]) >> ‘k ≠ 1’ by (strip_tac >> fs[]) >>
      ‘1 < k’ by simp[] >> simp[] >> fs[DIV_LT_X] >>
      ‘k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5’ by simp[] >> simp[]) >>
  ‘(k - 1) DIV 2 < k’ by simp[BIT1_smaller] >>
  Cases_on ‘1 < (k - 1) DIV 2’
  >- (‘ℓ ((k - 1) DIV 2) < (k - 1) DIV 2’ by metis_tac[] >> simp[]) >>
  ‘¬(ℓ ((k - 1) DIV 2) < (k - 1) DIV 2)’ by metis_tac[] >>
  ‘ℓ ((k - 1) DIV 2) = (k - 1) DIV 2’ by metis_tac[LESS_OR_EQ, ELL_LE] >>
  fs[NOT_LESS_EQUAL, X_LT_DIV, DIV_LT_X] >>
  ‘k = 1 ∨ k = 2 ∨ k = 3 ∨ k= 4’ by simp[] >> simp[]
QED


Theorem LENGTH_log2list[simp]:
  LENGTH (log2list k) = 2 ** k
Proof
  simp[log2list_def]
QED

(* part1: if kolmog was computable, there'd be a machine j which would, when
   given a y, come back with the smallest index i of a machine that would
   return y when given input 0. *)

(*
   j is the machine that, given argument y, runs all machines of size
   equal to y's complexity (dovetailing) until it finds one that
   terminates on input 0. It can stop and output that machine's index.

   fun jm y = let c = km y  ;
                  machines = log2list c ;
                  run i = map (λm. steps i (mk_state m 0)) machines ;
              in
                 cfindleast (λt. exists (λs. terminated s) (run t))
                            (λi. 2 ** c + findindex is_terminated (run i))
*)

(*
val compute_arg_lt_def = Define‘
  compute_arg_lt pki =
  LAM "y" (
    (* let c = ... in *)
    LAM "c" (
       LAM "machines" (
         LAM "term_with_y" (
           LAM "run" (
             cfindleast
               @@ (B @@ (cexists @@ VAR "term_with_y") @@ VAR "run")
               @@ (LAM "i" (cplus @@ (cpred @@ (cexp @@ church 2 @@ VAR "c"))
                                  @@ (cfind_index @@ VAR "term_with_y"
                                                  @@ (VAR "run" @@ VAR "i"))))
           )
           @@ (* run's value *)
             LAM "i" (
                  cmap
                    @@ LAM "m" (
                          csteps @@ VAR "i"
                                 @@ (cdAPP @@ VAR "m" @@ (cchurch @@ church 0))
                       )
                    @@ VAR "machines"
             )
         )
         @@ (* term_with_y = *)
            LAM "s" (cand @@ (cbnf @@ VAR "s")
                          @@ (ceqnat @@ VAR "y" @@ (cforce_num @@ VAR "s")))
       )
       @@ (* machine's value *) (cmap @@ (B @@ cnumdB @@ cpred)
                                      @@ (clog2list @@ VAR "c"))
    )
    @@ (* c's value: *) (cbnf_ofk @@ cforce_num
                                  @@ (cdAPP @@ (cnumdB @@ church pki)
                                            @@ (cchurch @@ VAR "y")))
  )
’;
*)

(*
Theorem FV_cexists[simp]:
  FV cexists = ∅
Proof
  simp[cexists_def, EXTENSION]
QED

Theorem FV_cfind_index[simp]:
  FV cfind_index = ∅
Proof
  simp[cfind_index_def, EXTENSION]
QED


val compute_arg_eqn = brackabs.brackabs_equiv [] (SPEC_ALL compute_arg_lt_def)

*)

Theorem EL_log2list :
  n < 2 ** i ⇒ EL n (log2list i) = n + 2 ** i
Proof
  simp[log2list_def, EL_GENLIST]
QED

(*

Theorem kolmog_arg_computable:
  computable plain_kolmog ⇒ computable arg_plain_kolmog
Proof
  simp[computable_def] >> disch_then (qx_choose_then ‘pki’ assume_tac) >>
  qexists_tac ‘dBnum (fromTerm (compute_arg_lt pki))’ >>
  simp[Phi_def] >>
  asm_simp_tac (bsrw_ss()) [compute_arg_eqn] >>
  qx_gen_tac ‘y’ >>
  qabbrev_tac ‘
     cpty = cbnf_ofk @@ cforce_num
                           @@ cDB (dAPP (numdB pki) (fromTerm (church y)))
  ’ >>
  ‘cpty == church (plain_kolmog y)’
    by (simp[Abbr‘cpty’] >> pop_assum (qspec_then ‘y’ strip_assume_tac) >>
        drule_then strip_assume_tac PhiSOME_cbnf_ofk >>
        asm_simp_tac (bsrw_ss()) []) >>
  Q.MATCH_GOALSUB_ABBREV_TAC ‘cfind_index @@ test’ >>
  asm_simp_tac (bsrw_ss()) [clog2list_behaviour, cmap_cvlist] >>
  simp[listTheory.MAP_MAP_o] >>
  qmatch_abbrev_tac ‘∃z. bnf_of (cfindleast @@ P @@ k) = SOME z ∧
                         arg_plain_kolmog y = force_num z’ >>
  Q.MATCH_ASMSUB_ABBREV_TAC ‘cvlist l’ >>
  ‘(∀n. ∃b. P @@ church n == cB b) ∧
   ∀n. (P @@ church n == cB T) ⇔
       ∃M r. ℓ M = plain_kolmog y ∧ steps n (N2T M @@ church 0) = r ∧
             bnf r ∧ force_num r = y’
    by (simp_tac (bsrw_ss())[Abbr‘P’, cmap_cvlist, GSYM FORALL_AND_THM] >>
        qx_gen_tac ‘n’ >>
        qmatch_abbrev_tac ‘
           (∃b. cexists @@ test @@ cvlist ll == cB b) ∧
           (cexists @@ test @@ cvlist ll == cB T ⇔ _)
        ’ >>
        ‘∀e. MEM e ll ⇒ ∃b. test @@ e == cB b’
           by simp_tac (bsrw_ss()) [Abbr‘ll’, MEM_MAP, PULL_EXISTS, Abbr‘l’,
                                    csteps_behaviour, Abbr‘test’,
                                    cbnf_behaviour] >>
        asm_simp_tac (bsrw_ss())
          [cexists_thm, Abbr‘l’, MEM_MAP, PULL_EXISTS, cbnf_behaviour,
           csteps_behaviour, MEM_log2list, Abbr‘test’, Abbr‘ll’] >>
        CONV_TAC (LAND_CONV (HO_REWR_CONV EXISTS_NUM)) >> simp[PRE_SUB1] >>
        metis_tac[]) >>
  drule (GEN_ALL churchnumTheory.cfindleast_termI) >>
  ‘∃m. P @@ church m == cB T’
    by (simp[] >>
        qspec_then ‘y’ mp_tac plain_kolmog_props >>
        disch_then (qx_choose_then ‘M’ (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
        simp[Phi_def, stepsTheory.bnf_steps, PULL_EXISTS] >>metis_tac[]) >>
  disch_then drule >> simp_tac (bsrw_ss()) [] >> disch_then kall_tac >>
  qabbrev_tac ‘t = LEAST n. P @@ church n == cB T’ >>
  ‘P @@ church t == cB T’
     by (simp_tac(srw_ss())[Abbr‘t’] >> numLib.LEAST_ELIM_TAC >>
         metis_tac[]) >>
  ‘∃Mt. ℓ Mt = plain_kolmog y ∧ bnf (steps t (N2T Mt @@ church 0)) ∧
       force_num (steps t (N2T Mt @@ church 0)) = y’ by metis_tac[] >>
  simp_tac (bsrw_ss()) [Abbr‘k’, cmap_cvlist] >>
  qmatch_abbrev_tac ‘
    ∃z. bnf_of (cplus @@ _ @@ (cfind_index @@ _ @@ cvlist ll)) = SOME z ∧
        arg_plain_kolmog y = force_num z
  ’ >>
  ‘∀e. MEM e ll ⇒ ∃b. test @@ e == cB b’
     by simp_tac (bsrw_ss()) [Abbr‘ll’, Abbr‘l’, Abbr‘test’, MEM_MAP,
                              PULL_EXISTS, csteps_behaviour, cbnf_behaviour] >>
  asm_simp_tac (bsrw_ss()) [cfind_index_thm, normal_orderTheory.bnf_bnf_of] >>
  simp[arg_plain_kolmog_unique] >>
  ‘∃e. MEM e ll ∧ test @@ e == cB T’
    by (simp_tac (bsrw_ss()) [Abbr‘test’, Abbr‘ll’, Abbr‘l’, MEM_MAP,
                              PULL_EXISTS, cbnf_behaviour, csteps_behaviour,
                              MEM_log2list] >>
        Q.REFINE_EXISTS_TAC ‘SUC z’ >> simp[] >> metis_tac[]) >>
  ‘EXISTS (λe. test @@ e == cB T) ll’ by (simp[EXISTS_MEM] >> metis_tac[]) >>
  simp[findPi_thm] >>
  qabbrev_tac ‘
    TNY = λt n y. steps t (N2T (EL n (log2list (plain_kolmog y)) - 1) @@
                           church 0)
  ’ >>
  ‘∀n. n < LENGTH ll ⇒
       (test @@ EL n ll == cB T ⇔ bnf (TNY t n y) ∧ force_num (TNY t n y) = y)’
    by (simp_tac (bsrw_ss()) [Abbr‘test’, Abbr‘ll’, Abbr‘l’, EL_MAP,
                              csteps_behaviour, cbnf_behaviour, PRE_SUB1] >>
        metis_tac[]) >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[MEM_EL] >>
  qx_gen_tac ‘n’ >> strip_tac >>
  simp[arg_plain_pred_def, PRE_SUB1] >>
  simp[Phi_def, stepsTheory.bnf_steps, PULL_EXISTS] >>
  ‘LENGTH ll = 2 ** plain_kolmog y’ by simp[Abbr‘ll’, Abbr‘l’] >> fs[] >>
  map_every qexists_tac [‘t’, ‘t’] >>
  ‘bnf (TNY t n y) ∧ force_num (TNY t n y) = y’ by metis_tac[] >>
  qabbrev_tac ‘ββ = λt m. steps t (N2T m @@ church 0)’ >> fs[] >>
  qabbrev_tac ‘arg = n + 2 ** plain_kolmog y - 1’ >>
  ‘ℓ arg = plain_kolmog y’
     by (simp[ELL_log2list, MEM_GENLIST, log2list_def] >>
         qexists_tac ‘arg + 1 - 2 ** plain_kolmog y’ >>
         simp[Abbr‘arg’]) >>
  rpt strip_tac
  >- (qpat_x_assum ‘bnf (TNY t n _)’ mp_tac >> simp[Abbr‘TNY’, EL_log2list])
  >- (rw[] >> qpat_x_assum ‘force_num _ = force_num _’ mp_tac >>
      simp[Abbr‘TNY’, EL_log2list])
  >- (qmatch_abbrev_tac ‘ℓ _ = MIN_SET ss’ >> simp[] >>
      DEEP_INTRO_TAC MIN_SET_ELIM >> conj_tac
      >- (simp[Abbr‘ss’, EXTENSION] >> metis_tac[]) >>
      simp[PULL_EXISTS, Abbr‘ss’] >> rpt strip_tac >>
      rename [‘plain_kolmog _ = ℓ Ni’] >>
      ‘ℓ Ni ≤ ℓ Mt’ by metis_tac[] >>
      ‘ℓ Mt ≤ ℓ Ni’ suffices_by metis_tac[LESS_EQUAL_ANTISYM] >>
      simp[] >> irule plain_kolmog_smallest >>
      simp[Phi_def, stepsTheory.bnf_steps, PULL_EXISTS] >> metis_tac[])
  >- (simp[tPhi_def, terminated_def, prtermTheory.pr_bnf_correct,
           mk_initial_state_def, prtermTheory.pr_steps_correct] >>
      ‘ββ t arg = TNY t n y’ by simp[Abbr‘TNY’, EL_log2list] >> simp[] >>
      Q.SUBGOAL_THEN ‘∃t0. (λt0. P @@ church t0 == cB T) t0’
         (mp_tac o CONJUNCT2 o MATCH_MP LEAST_EXISTS_IMP) >- metis_tac[] >>
      simp[] >> rpt strip_tac >>
      ‘ββ t' arg = ββ t arg’ suffices_by metis_tac[] >>
      metis_tac[stepsTheory.bnf_steps_upwards_closed])
  >- (qpat_x_assum ‘tPhi _ _ _’ mp_tac >>
      simp[tPhi_def, terminated_def, prtermTheory.pr_steps_correct,
           prtermTheory.pr_bnf_correct, mk_initial_state_def] >>
      rename [‘bnf (ββ u N) ∧ _ ⇒ t ≤ u’] >> strip_tac >>
      spose_not_then (assume_tac o REWRITE_RULE [NOT_LESS_EQUAL]) >>
      ‘force_num (ββ u N) = y’
         by metis_tac[stepsTheory.bnf_steps_upwards_closed,
                      DECIDE “x:num < y ∨ x = y ∨ y < x”] >>
      Q.SUBGOAL_THEN ‘∃t0. (λt0. P @@ church t0 == cB T) t0’
         (mp_tac o CONJUNCT2 o MATCH_MP LEAST_EXISTS_IMP) >- metis_tac[] >>
      simp[] >> metis_tac[])
  >- (qpat_x_assum ‘y = force_num _’ (assume_tac o SYM) >> simp[] >>
      rename [‘arg ≤ N’] >> qpat_x_assum ‘tPhi _ _ _ ’ mp_tac >>
      simp[tPhi_def, terminated_def, prtermTheory.pr_steps_correct,
           prtermTheory.pr_bnf_correct, mk_initial_state_def] >> strip_tac >>
      ‘force_num (ββ t N) = y’
         by metis_tac[stepsTheory.bnf_steps_upwards_closed,
                      DECIDE “x:num < y ∨ x = y ∨ y < x”] >>
      spose_not_then (assume_tac o REWRITE_RULE [NOT_LESS_EQUAL]) >>
      Q.UNDISCH_THEN ‘ℓ N = ℓ arg’ mp_tac >>
      simp[ELL_log2list, MEM_GENLIST, log2list_def] >> qx_gen_tac ‘N0’ >>
      rpt strip_tac >>
      ‘N = N0 + 2 ** plain_kolmog y - 1’ by simp[] >>
      pop_assum SUBST_ALL_TAC >> fs[Abbr‘arg’] >>
      ‘¬(test @@ EL N0 ll == cB T)’ by metis_tac[] >> pop_assum mp_tac >>
      REWRITE_TAC[] >>
      Q.UNDISCH_THEN ‘N0 < 2 ** plain_kolmog y’ (
             (fn th => first_x_assum (SUBST1_TAC o C MATCH_MP th))) >>
      simp[Abbr‘TNY’] >> simp[EL_GENLIST, log2list_def] >>
      metis_tac[stepsTheory.bnf_steps_upwards_closed,
                      DECIDE “x:num < y ∨ x = y ∨ y < x”])
QED

*)

(* proven *)

(*
Theorem part1_arg_kolmog:
  computable arg_plain_kolmog ==>
  ∃j. ∀y. ∃i. Phi j y = SOME i ∧ Phi i 0 = SOME y
Proof
  rw[computable_def] >> qexists_tac`i` >>
  rw[arg_plain_kolmog_leastsize,Phi_arg_pl_kolmog]
QED



val yMt_pred_def = Define‘
  yMt_pred e n yi Mi ti <=>
    plain_kolmog yi < 2*n ∧
    ℓ yi = 2* n ∧
    ℓ Mi = plain_kolmog yi ∧
    terminated (steps ti (mk_initial_state Mi 0)) ∧
    cs_to_num (steps ti (mk_initial_state Mi 0)) = yi ∧
    (∀t'. terminated (steps t' (mk_initial_state Mi 0)) ==> ti<=t') ∧
    e=npair yi (npair Mi ti)
’;

*)


(* might not need above here *)

val fkmin_def = Define`fkmin m = MIN_SET {bl2n n | m<= core_complexity0 n}`

Theorem f_min_set_f:
  (∃x. m<= f x) ==> (m:num) <= f (MIN_SET {n | m<= f n})
Proof
  rw[] >> `{n | m ≤ f n} <> {}` by (fs[EXTENSION] >> metis_tac[]) >> 
  `MIN_SET {n | m ≤ f n} ∈ {n | m ≤ f n}` by fs[MIN_SET_LEM] >> fs[]
QED

Theorem contrapos_FINITE_DIFF_down:
  INFINITE P ==> (INFINITE (P DIFF Q) ∨ INFINITE Q)
Proof
  metis_tac[FINITE_DIFF_down]
QED

Theorem INFINITE_DIFF_down:
  INFINITE P ∧ FINITE Q ==> INFINITE (P DIFF Q)
Proof
  rw[] >>  metis_tac[contrapos_FINITE_DIFF_down]
QED

Theorem INFINITE_SURJ:
  INFINITE t ∧ SURJ f s t ==> INFINITE s
Proof
  metis_tac[FINITE_SURJ]
QED



Theorem n2bl_inj[simp]:
  n2bl x = n2bl y <=> x=y
Proof
  eq_tac >> rw[] >> `bl2n (n2bl x) = bl2n (n2bl y)` by metis_tac[] >> metis_tac[bool_num_inv]
QED



Theorem core_complexity0_lb_exists:
  ∃x. m <= core_complexity0 x
Proof
  CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
  `∀x. ∃i. on2bl (Phi i 0) = SOME x ∧ ℓ i < m` by metis_tac[core_complexity0_props] >>
  fs[SKOLEM_THM] >> 
  `FINITE (count m)` by fs[FINITE_COUNT] >>
  `INFINITE {f x | x | T}` by 
    (`SURJ (λx. on2bl (Phi (f x) 0)) UNIV {SOME n|T}` by 
       (fs[SURJ_DEF] >> rw[]) >> 
     `IMAGE (λx. on2bl (Phi (f x) 0)) UNIV = {SOME n|T}` by fs[IMAGE_SURJ]>>
     fs[IMAGE_DEF] >> 
     `{SOME n | T} = IMAGE (λx. on2bl (Phi x 0)) {f x | x | T}` by 
       (fs[IMAGE_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[] 
        >- (qexists_tac`f n` >> metis_tac[]) 
        >- (qexists_tac`x''` >> metis_tac[]) ) >> 
     `SURJ (λx. on2bl (Phi x 0)) {f x | x | T} {SOME n | T}` by fs[SURJ_IMAGE] >>

     `¬(FINITE {SOME (n:bool list) | T})` by 
       (`INFINITE 𝕌(:bool list option)` by 
          (fs[infinite_num_inj] >> qexists_tac`SOME o n2bl` >> rw[INJ_DEF,n2bl_inj]) >> 
        `{SOME n | T} = 𝕌(:bool list option) DIFF {NONE}` by  
          (rw[EXTENSION] >> eq_tac >> rw[] >> Cases_on`x` >> fs[]) >> 
        `FINITE {NONE}` by fs[FINITE_SING] >> 
        rw[] >> fs[INFINITE_DIFF_down]) >> 

     `∃g. INJ g {SOME n | T} {f x | x | T} ∧ ∀y. y ∈ {SOME n | T} ⇒ (λx. on2bl (Phi x 0)) (g y) = y` by 
       (irule pred_setTheory.SURJ_INJ_INV >> fs[]) >> metis_tac[INFINITE_INJ] ) >>
  `FINITE {i | ∃x. i = (f x)}` by 
    (`{i | ∃x. i = (f x)} ⊆ count (2**m + 2**m)` suffices_by 
       metis_tac[SUBSET_FINITE_I,FINITE_COUNT] >> simp[SUBSET_DEF] >> rw[] >> fs[] >>
     `ℓ (f x') < m` by fs[] >> 
     `MEM ((f x') + 1) (log2list (ℓ (f x')))` by metis_tac[ELL_log2list] >> 
     fs[log2list_def,MEM_GENLIST] >> 
     `f x' < 2 ** ℓ (f x') + 2 ** ℓ (f x')` by fs[] >>
     `prim_rec$< (2 ** (ℓ (f x'))+2 ** (ℓ (f x')))  (2 ** m+2 ** m)` by fs[LESS_TRANS] >> 
     `f x' < 2 ** m + 2 ** m` by metis_tac[LESS_TRANS] >> fs[]) >> 
   `SURJ (λx. x)  {i | (∃x. i = (f x))} {f x | x | T}` by 
    (fs[SURJ_DEF] >> rw[] ) >>
  `FINITE {f x | x | T}` by metis_tac[FINITE_SURJ]
QED

(* up to fixing here *)

(* not sure if needed to fix?
Theorem kfkmin_lb:
  ∀m. m <= core_complexity0 (n2bl (fkmin m))
Proof
  rw[] >> `∃x. m <= core_complexity0 x` by fs[core_complexity0_lb_exists] >> 
  
  rw[fkmin_def,core_complexity0_def] >> 
  {}
  irule f_min_set_f >> 
QED
*)


Theorem computable_imp_thm:
  ∀f. computable f ==> ∃i. ∀n. Phi i n = SOME (f n)
Proof
  metis_tac[computable_def]
QED

Theorem computable_imp_min_thm:
  ∀f. computable f ⇒ ∃i. (∀n. Phi i n = SOME (f n)) ∧ (∀j. (∀n. Phi j n = SOME (f n)) ==> i<=j)
Proof
  rw[] >> 
  qexists_tac`MIN_SET {i | (∀n. Phi i n = SOME (f n))}`>>
  `{i | (∀n. Phi i n = SOME (f n))} <> {}` 
    by (fs[EXTENSION,computable_imp_thm]) >>
  rw[] 
  >- (`MIN_SET {i | (∀n. Phi i n = SOME (f n))} ∈ {i | (∀n. Phi i n = SOME (f n))}` 
        by fs[MIN_SET_LEM] >> fs[IN_DEF])
  >- (fs[MIN_SET_LEM])
QED


val recfn_index2_def =
new_specification("recfn_index2_def", ["recfn_index2"],
		  computable_imp_min_thm
		      |> SIMP_RULE (srw_ss()) [LEFT_FORALL_IMP_THM]
		      |> SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])


val kolmog_fn2_def = Define`kolmog_fn2 f = if computable f
                                             then SOME (recfn_index2 f)
                                           else NONE`



Theorem ell_0[simp]:
  ℓ 0 = 0
Proof
  EVAL_TAC
QED


Theorem MEM_log2list_ineq:
   MEM x (log2list i) ⇔ 0 < x ∧ (2 ** i)  <= x ∧ x < (2 ** (i+1)) 
Proof
  eq_tac >> fs[log2list_def,MEM_GENLIST ] >> rw[]
  >- (`x'+2**i < 2** i + 2**i` by fs[] >> `(2n**i:num) + 2**i = 2*2**i` by fs[GSYM TIMES2] >>
      `2n**i + 2**i = 2 ** SUC i` by fs[EXP] >> fs[ADD1])
  >- (qexists_tac`x-2n**i` >> fs[] >> `2n*2**i = 2 ** SUC i` by fs[EXP] >> fs[ADD1])
QED

Theorem exp_ELL1:
  2n ** ℓ x <= x+1
Proof
  `MEM (x+1) (log2list (ℓ x))` by metis_tac[ELL_log2list] >>
  fs[MEM_GENLIST,log2list_def]
QED

Theorem exp_ELL2:
  x+1 < 2n ** ((ℓ x)+1 )
Proof
  `MEM (x+1) (log2list (ℓ x))` by metis_tac[ELL_log2list] >>
  fs[MEM_log2list_ineq]
QED


Theorem pair_arithineq1:
  (x<>0 ∧ y<>0) ==> x*y + x + y + 1 < 2*(x*y) + 4n
Proof
  rw[] >> ONCE_REWRITE_TAC[TIMES2] >> `x+y+1 < x*y+4` suffices_by fs[] >> 
  Induct_on`x` >> fs[ADD1]
QED



Theorem ELL_REC_EQ:
  ℓ (2*x+2) = 1+ ℓ x ∧ ℓ (2*x+1) = 1+ ℓ x
Proof
  completeInduct_on`x` >> fs[] >> rw[] >> 
  simp[Once num_to_bool_list_def,SimpLHS,EVEN_ADD,EVEN_MULT]
QED

Theorem ELL_REC_BIT_EQ:
  ℓ (BIT2 x) = 1+ ℓ x ∧ ℓ (BIT1 x) = 1+ ℓ x ∧ ℓ ZERO = 0
Proof
  simp[SimpLHS,Once BIT1,Once BIT2] >> simp[ ELL_REC_EQ,ALT_ZERO]
QED

Theorem lem111:
  y<>0 ==> 2 * ((x:num) * (y:num) + 1) ≤ y * (2 * x + 1) + 1
Proof
  rw[]
QED


Theorem ell_mult1:
  ℓ(x*y) <= (ℓ x) + (ℓ y) +1
Proof
  CCONTR_TAC >> ` (ℓ x) + (ℓ y) +1 < ℓ(x*y)` by fs[] >>
  `2n ** ℓ x <= x+1 ∧ 2 ** ℓ y <= y+1 ∧ 2n ** ℓ (x*y) <= (x*y)+1` by fs[exp_ELL1] >>
  `x + 1 < 2n ** (ℓ x + 1) ∧ y + 1 < 2n ** (ℓ y + 1) ∧ (x*y) + 1 < 2n ** (ℓ (x*y) + 1)` by fs[exp_ELL2] >> 
  `ℓ x + ℓ y + 2 <= ℓ (x * y)` by fs[] >> 
  `2n ** (ℓ x + ℓ y) <= (x+1) * (y+1) ∧ (x + 1) * (y + 1) < 2n ** (ℓ x + ℓ y + 2)` by 
  (fs[LESS_MONO_MULT2,EXP_ADD] >> 
   `(x + 1 ) * (y + 1) < (2 * 2n ** ℓ x) * (y+1)` by fs[LT_MULT_LCANCEL] >>
   `0<(2 * 2n ** ℓ x)` by fs[] >>
   `(2 * 2n ** ℓ x) * (y+1) < (2 * 2 ** ℓ x ) *  (2 * 2 ** ℓ y)` by rw[LT_MULT_LCANCEL] >> 
   `(x + 1) * (y + 1) < 2 * 2n ** ℓ x * (2 * 2 ** ℓ y)` by rw[] >> rw[]) >>
  `x*y+1 <= (x+1)*(y+1)` by fs[] >> 
  `(x + 1) * (y + 1) < 2n ** (ℓ (x*y) )` by 
    (`2 ** (ℓ x + ℓ y + 2) <= 2n ** (ℓ (x*y))` by fs[] >> rw[]) >> fs[]
QED

Theorem ell_mult_corr:
  ∀n. ∃k. ∀x. ℓ(n*x) <= ℓ(x)+k
Proof
  rw[] >> qexists_tac`ℓ n + 1` >> rw[] >> metis_tac[ell_mult1,ADD_ASSOC]
QED

Theorem ell_SUC_corr:
   ∀x. ℓ(x+1) <= ℓ(x)+2
Proof
  rw[] >> Cases_on`x=0` >> fs[] >- EVAL_TAC >> `x+1<=2*x` by (Induct_on`x` >> fs[]) >> 
  `ℓ (x+1) <= ℓ (2*x)` by fs[ELL_MONOTONE] >> `ℓ (2*x) <= ℓ x + 2` suffices_by fs[] >>
  `ℓ (2*x) <= ℓ 2 + ℓ x + 1 ` by fs[ell_mult1] >> fs[] >> `ℓ 2 + 1 = 2` by EVAL_TAC >> 
  metis_tac[]
QED

Theorem ell_1[simp]:
  ℓ 1 = 1
Proof
  EVAL_TAC
QED

Theorem sum_lt_mult:
  (x <> 0 ∧ y <> 0 ∧ x <> 1 ∧ y <> 1) ==> (x:num)+y<=x*y
Proof
  rw[] >> Induct_on`x` >> fs[] >> rw[MULT_SUC] >> `SUC x <= y * x` suffices_by fs[] >>
  irule MULT_INCREASES >> rw[]
QED

Theorem ell_add_corr:
  ∀n. ∃k. ∀x. ℓ(x+n) <= ℓ(x)+k
Proof
  rw[] >> qexists_tac`ℓ (n) + 1` >> rw[] >> Cases_on`n=0` >> Cases_on`x=0` >> fs[] >>
  Cases_on`n=1` >> Cases_on`x=1` >> fs[ell_SUC_corr] >- EVAL_TAC >>
  `n+x<=n*x` by fs[sum_lt_mult] >> `ℓ (n + x) <= ℓ (n*x)` by fs[ELL_MONOTONE] >>
  `ℓ (n * x) <= ℓ n + (ℓ x + 1)` suffices_by fs[] >>
  metis_tac[ell_mult1,ADD_ASSOC]
QED


Theorem ell_sum_corr:
  ℓ (x + y) ≤ ℓ x + ℓ y + 1
Proof
  Cases_on`x=0` >> Cases_on`y=0` >> Cases_on`x=1` >> Cases_on`y=1` >> fs[ell_SUC_corr]
  >- EVAL_TAC >> `x+y<= x*y` by fs[sum_lt_mult] >>
  `ℓ (x + y) <= ℓ (x * y)` by fs[ELL_MONOTONE] >>
  `ℓ (x * y) <= ℓ x + (ℓ y + 1)` suffices_by fs[] >>
  metis_tac[ell_mult1,ADD_ASSOC]
QED

Theorem ell_npair:
  ∃k. ∀x y. ℓ (x ⊗ y) <= 2*(ℓ x + ℓ y) + k
Proof
  `∃k. ∀z. ℓ(z+1) <= ℓ(z)+k` by fs[ell_add_corr] >>
  qexists_tac`2*k+3` >> rw[] >> fs[numpairTheory.npair_def,numpairTheory.tri_formula] >>
  `y + (x + y) * (x + (y + 1)) DIV 2 <= (x+y+1)*(x+y+1)` by 
    (`(x + y) * (x + (y + 1)) DIV 2 <= (x + y) * (x + (y + 1))` by fs[DIV_LESS_EQ] >> 
     `y + (x + y) * (x + (y + 1)) ≤ (x + y + 1) * (x + y + 1)` suffices_by fs[] >> 
     `∃d. y + (x + y) * (x + (y + 1)) + d = (x + y + 1) * (x + y + 1)` suffices_by fs[] >>
     qexists_tac`x+1` >>
     ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
     ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
     ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >>
     ONCE_REWRITE_TAC[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] >> fs[]) >> 
  `ℓ (y + (x + y) * (x + (y + 1)) DIV 2) <= ℓ ((x + y + 1) * (x + y + 1))` by fs[ELL_MONOTONE]>>
  `ℓ ((x + y + 1) * (x + y + 1)) <= 2 * k + (2 * (ℓ x + ℓ y) + 3)` suffices_by fs[] >>
  `ℓ ((x + y + 1) * (x + y + 1)) <= ℓ (x + y + 1) + ℓ (x + y + 1) +1` by fs[ell_mult1]>>
  `ℓ (x + y + 1) + ℓ (x + y + 1) + 1 <= 2 * k + (2 * (ℓ x + ℓ y) + 3)` suffices_by fs[] >>
  `ℓ (x+y+1) <= k + ℓ (x+y)` by fs[] >>
  `(ℓ (x + y) + k) + (ℓ (x + y) + k) + 1 <= 2 * k + (2 * (ℓ x + ℓ y) + 3)` suffices_by fs[] >>
  fs[] >> `2 * ℓ (x + y) ≤ 2 * ( ℓ x + ℓ y ) + 2` suffices_by fs[] >> 
  `ℓ (x + y) ≤ (ℓ x + ℓ y) + 1` suffices_by fs[] >> metis_tac[ell_sum_corr]
QED



Theorem Phi_bl2nx_npair:
  ∀y. ∃x. Phi (nfst (bl2n x)) (nsnd (bl2n x)) = SOME y
Proof
  rw[] >> simp[Phi_def] >>
  qexists_tac`n2bl (npair (dBnum (fromTerm (K @@ church y))) (dBnum (fromTerm (K @@ church y))))` >>
  simp[bool_num_inv] >>
  qexists_tac`church y` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED



(*
val _ = overload_on ("UKC",``(λx. THE (kolmog_complexity (x:num) (U:bool list -> num option ) ))``)
*)


Theorem univ_rf_smallest:
  univ_rf U ∧ U k = SOME y ⇒ KC U y ≤ LENGTH k
Proof
  rw[univ_rf_def] >> simp[KC_def,core_complexity_def] >> 
  `{p | U p = SOME y} <> ∅` by (fs[EXTENSION] >> metis_tac[]) >>
  simp[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (simp[EXTENSION] >> metis_tac[]) >>
  fs[PULL_EXISTS]
QED


Theorem univ_rf_kolmog_fn_ub:
  computable f ∧ univ_rf U ==> 
  ∃c. ∀m. 
    KC U (n2bl (f m)) <=  ℓ (m)  + c
Proof
  rw[] >> 
   `(∀n. Phi (recfn_index2 f) n = SOME (f n)) ∧
    ∀j. (∀n. Phi j n = SOME (f n)) ⇒ recfn_index2 f ≤ j` by fs[recfn_index2_def]>>
  `∀m. Phi (recfn_index2 f) (m) = SOME (f m)` by fs[] >>
  `∃g. ∀m. on2bl (Phi (recfn_index2 f) m) = (U (g ++ n2bl m))` by 
    (fs[univ_rf_def] >> `∃g. ∀x. on2bl (Phi (recfn_index2 f) x) = (U (g ++ n2bl x))` by fs[])>>
  qexists_tac`LENGTH g` >> rw[] >>
  `U (g ++ n2bl m) = SOME (n2bl (f m))` by 
    (`on2bl (Phi (recfn_index2 f) m) = U (g++ n2bl m)` by fs[] >> 
     `Phi (recfn_index2 f) m = SOME (f m)` by fs[] >>
     fs[on2bl_def] >> fs[optionTheory.OPTION_MAP_DEF]) >>
  `KC U (n2bl (f m)) ≤ LENGTH (g ++ n2bl m)` by fs[univ_rf_smallest] >> fs[]
QED

Theorem computable_id:
  computable (λx. x)
Proof
  fs[computable_def,Phi_def] >> qexists_tac`dBnum (fromTerm (I))` >>
  rw[] >> qexists_tac`(church x)` >> rw[churchnumTheory.force_num_church] >>
  `I @@ church x == church x` by fs[chap2Theory.lameq_I] >>
  `bnf (church x)` by fs[churchnumTheory.bnf_church] >>
  fs[normal_orderTheory.lameq_bnf_of_SOME_I] 
QED


Theorem univ_rf_kolmog_ub:
  univ_rf U ==> ∃c. ∀m. KC U (n2bl m) <= (ℓ (m) ) + c
Proof
  rw[] >> `computable (λx. x)` by fs[computable_id] >> 
  qabbrev_tac`f = (λx. (x:num))` >> 
  `∃c. ∀m. KC U (n2bl (f m)) <=  ℓ (m)  + c` by 
    metis_tac[univ_rf_kolmog_fn_ub]  >>metis_tac[ADD_COMM]
QED



Definition UKCfkmin_def:
  UKCfkmin (U:bool list->bool list option) m = MIN_SET {bl2n n | m <= KC U n}
End

Theorem MIN_SET_L_PHI_NPAIR_NON_EMPTY:
  {LENGTH p | Phi (nfst (bl2n p)) (nsnd (bl2n p)) = SOME y} <> {}
Proof
  fs[EXTENSION,Phi_bl2nx_npair]
QED


Theorem univ_rf_kolmog_props:
  univ_rf U ==> ∀y. ∃z. KC U y = LENGTH z ∧ U z = SOME y
Proof
  rw[] >> fs[KC_def,core_complexity_def,univ_rf_nonempty] >>  
  DEEP_INTRO_TAC MIN_SET_ELIM >>  
  rw[] >> `{p | U p = SOME y} ≠ ∅` by fs[univ_rf_nonempty] >> 
  fs[EXTENSION] >> metis_tac[]
QED


Theorem univ_rf_kolmog_lb_exists:
  univ_rf U ==> ∃x. m <= KC U x
Proof
  CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
  `∀x. ∃i. U i = SOME x ∧ LENGTH i < m` by metis_tac[univ_rf_kolmog_props] >>
  fs[SKOLEM_THM] >> 
  `FINITE (count m)` by fs[FINITE_COUNT] >>
  `INFINITE {f x | x | T}` by 
    (`SURJ (λx. U (f x)) UNIV {SOME n|T}` by 
       (fs[SURJ_DEF] >> rw[]) >> 
     `IMAGE (λx. U (f x) ) UNIV = {SOME n|T}` by fs[IMAGE_SURJ]>>
     fs[IMAGE_DEF] >> 
     `{SOME n | T} = IMAGE (λx. U x) {f x | x | T}` by 
       (fs[IMAGE_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[] 
        >- (qexists_tac`f n` >> metis_tac[]) 
        >- (qexists_tac`x''` >> metis_tac[]) ) >> 
     `SURJ (λx. U x) {f x | x | T} {SOME n | T}` by fs[SURJ_IMAGE] >>
     `¬(FINITE {SOME (n:bool list) | T})` by 
       (`INFINITE 𝕌(:bool list option)` by 
          (`∃f. INJ f 𝕌(:num) 𝕌(:bool list option)` suffices_by fs[infinite_num_inj] >> 
           qexists_tac`SOME o n2bl` >> rw[INJ_DEF,n2bl_inj]) >> 
        `{SOME n | T} = 𝕌(:bool list option) DIFF {NONE}` by  
          (rw[EXTENSION] >> eq_tac >> rw[] >> Cases_on`x` >> fs[]) >> 
        `FINITE {NONE}` by fs[FINITE_SING] >> 
        rw[] >> fs[INFINITE_DIFF_down]) >> 
     `∃g. INJ g {SOME n | T} {f x | x | T} ∧ ∀y. y ∈ {SOME n | T} ⇒ (λx. U x) (g y) = y` by 
       (irule pred_setTheory.SURJ_INJ_INV >> fs[]) >> metis_tac[INFINITE_INJ] ) >>
  `FINITE {LENGTH i | ∃x. i = (f x)}` by 
    (`{LENGTH i | ∃x. i = (f x)} ⊆ count (2n**m + 2**m)` suffices_by 
       (metis_tac[SUBSET_FINITE_I,FINITE_COUNT]) >> simp[SUBSET_DEF] >> rw[] >> fs[] >>
     `LENGTH (f x') < m` by fs[] >> 
     `m < 2* 2n** m` suffices_by fs[] >> `m < 2n**m` by simp[X_LT_EXP_X_IFF] >> fs[]) >> 
   `SURJ (λx. x)  { i | (∃x. i = (f x))} {f x | x | T}` by 
    (fs[SURJ_DEF] >> rw[] ) >>
  `FINITE {i | (∃x. i = f x)}` by (`FINITE {(i:bool list) | LENGTH i < m}` by 
    fs[finite_bool_list_lt_n] >> 
  `{i | (∃x. i = f x)} ⊆ {i | LENGTH i < m}` by (fs[SUBSET_DEF] >> rw[] >> fs[]) >>
    metis_tac[SUBSET_FINITE]) >>
  metis_tac[FINITE_SURJ]
QED







Theorem f_n2bl_min_set_f:
  (∃x. (m:num) ≤ f x) ==> m ≤ f ( n2bl ( MIN_SET {bl2n n | m ≤ f n}))
Proof
  rw[] >> `{bl2n n | m ≤ f n} <> {}` by (fs[EXTENSION] >> metis_tac[]) >> 
  `n2bl (MIN_SET {bl2n n | m ≤ f n}) ∈ {n | m ≤ f n}` by 
    (`MIN_SET {bl2n n | m ≤ f n} ∈ {bl2n n | m ≤ f n}` by fs[MIN_SET_LEM] >>
     `n2bl (MIN_SET {bl2n n | m ≤ f n}) ∈ IMAGE n2bl {bl2n n | m ≤ f n}` by fs[] >> fs[IMAGE_DEF]) >> fs[]
QED



Theorem UKCfkmin_def_lb:
  univ_rf U ==> ∀m. m <= KC U (n2bl (UKCfkmin U m))
Proof
  rw[UKCfkmin_def] >> `(∃x. m ≤ KC U x)` by  fs[univ_rf_kolmog_lb_exists] >>
  `m ≤ (λx. KC U x) (n2bl (MIN_SET {bl2n n | m ≤ (λx. KC U x) n}))` suffices_by fs[] >>
  irule f_n2bl_min_set_f >> metis_tac[]
QED

val unbounded_def = Define`unbounded f = (∀m. ∃x. (m:num) <= f (x:num))`

val t = brackabs.brackabs_equiv[](ASSUME``LAM "x" (cfindleast 
             @@ (LAM "n" (cnot @@ (cless 
                              @@ (UM @@ (cnpair @@ (church i) @@ VAR "n") ) 
                              @@ (VAR "x") ) ) )
             @@ I ) == ZZ``) |> concl |> lhand




Theorem computable_arg_min_set:
  computable f ∧ unbounded f ==> ∃i. ∀x. Phi i x = SOME (MIN_SET {n | x <= f n})
Proof
  rw[computable_def,unbounded_def] >> 
  qexists_tac
  `dBnum (fromTerm ^t )` >>
  simp[Phi_def] >> asm_simp_tac (bsrw_ss()) [] >> qx_gen_tac`x` >>
  Q.HO_MATCH_ABBREV_TAC`∃z. bnf_of (cfindleast @@ P @@ I) = _ z ∧ _ z` >> 
  `∀n. P @@ church n == cB (x <= f n)` by 
    (asm_simp_tac (bsrw_ss()) [Abbr`P`] >> rw[] >> 
     last_x_assum (qspec_then `n` assume_tac) >>
     drule recfunsTheory.PhiSOME_UM_I >> asm_simp_tac (bsrw_ss()) [] >> fs[]) >>
  `(∀n. ∃b. P @@ church n == cB b) ∧ ∃n. P @@ church n == cB T` by 
    (asm_simp_tac (bsrw_ss()) [] >> rw[]) >> 
  drule_all_then assume_tac (GEN_ALL churchnumTheory.cfindleast_termI) >>
  asm_simp_tac (bsrw_ss()) [] >> fs[normal_orderTheory.bnf_bnf_of,MIN_SET_DEF] >> 
  asm_simp_tac (bsrw_ss()) [] >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED




Theorem computable_UKCfkmin:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==> computable (UKCfkmin U)
Proof
  rw[] >> `unbounded (λx. KC U (n2bl x))` by 
    (rw[unbounded_def] >> `∃y. m <= KC U y` by fs[univ_rf_kolmog_lb_exists] >> 
     qexists_tac`bl2n y` >> fs[]) >>
  simp[computable_def,UKCfkmin_def] >> 
  `∃i. ∀n. Phi i n = SOME (MIN_SET { n' | n ≤ (λx. KC U (n2bl x)) n'})` suffices_by 
    (rw[] >> qexists_tac`i` >> rw[] >> 
     `{n' | n ≤ KC U (n2bl n')} = {bl2n n' | n ≤ KC U n'}` suffices_by fs[] >> fs[EXTENSION] >> 
     rw[] >> eq_tac >- (rw[] >> qexists_tac`n2bl x` >> fs[]) >- (rw[] >> fs[])  ) >> 
  fs[computable_arg_min_set]
QED





Theorem UKCkol_fkmin_lb:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==> 
  ∃c. ∀m. (λx. KC U (n2bl x)) (UKCfkmin U m) <= (ℓ m)+ c
Proof
  rw[] >> `computable (UKCfkmin U)` by fs[computable_UKCfkmin] >> 
  `∃c. ∀m. (λx. KC U (n2bl x)) (UKCfkmin U m) ≤ (ℓ m) + c` by 
    metis_tac[univ_rf_kolmog_fn_ub] >> qexists_tac`c` >> rw[] >> fs[]
QED



Theorem UKCcompkol_lb:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==> ∃c. ∀m. m <=  2*(ℓ m) + c
Proof
  rw[] >> `∃c. ∀m. (λx. KC U (n2bl x)) (UKCfkmin U m) <= (ℓ m) + c` by fs[UKCkol_fkmin_lb]>>
  `∀m. m <= (λx. KC U (n2bl x)) (UKCfkmin U m)` by fs[UKCfkmin_def_lb]  >> qexists_tac`c` >> rw[] >>
  `m ≤ (λx. KC U (n2bl x)) (UKCfkmin U m)` by fs[] >> `(λx. KC U (n2bl x)) (UKCfkmin U m) ≤ c + ℓ m` by fs[] >>fs[]
QED

Theorem exists_log_lb:
  ∃m. ¬(m<= 2*(ℓ m) + c)
Proof
  CCONTR_TAC >> fs[] >>
  Cases_on`1<c` 
  >- (`ℓ c < c` by fs[ELL_LT] >> `11*c <= c + 2 * ℓ (11*c)` by fs[] >>
      `ℓ (11*c) <= ℓ 11 + ℓ c + 1` by fs[ell_mult1] >> 
      `11*c<= c+ 2* (ℓ 11 + ℓ c + 1)` by fs[] >>
      `5*c <= (ℓ 11 + ℓ c + 1)` by fs[] >>
      `ℓ 11 = 3` by EVAL_TAC >> fs[] >> `ℓ c + 4 < c + 4` by fs[ELL_LT] >> 
      `5*c < c+4` by metis_tac[LESS_EQ_LESS_TRANS] >> `c+4 < 4*c + c` by fs[] >> fs[]) 
  >- (`c<=1` by fs[] >> `c=0 ∨ c=1` by fs[] >> fs[] 
      >- (`100 <= 2 * ℓ 100` by fs[] >> pop_assum mp_tac >> EVAL_TAC)
      >- (`100 <= 2 * ℓ 100 + 1` by fs[] >> pop_assum mp_tac >> EVAL_TAC)  )
QED

Theorem part_hutter_UKC:
  univ_rf U ∧ computable (λx. KC U (n2bl x)) ==> F
Proof
  strip_tac >> `∃c. ∀m. m <=  2*(ℓ m) + c` by metis_tac[UKCcompkol_lb] >>
  `∃m. ¬(m<= 2*(ℓ m) + c)` by fs[exists_log_lb] >> metis_tac[]
QED

Theorem UKC_incomp:
  univ_rf U ==> ¬(computable (λx. KC U (n2bl x)))
Proof
  metis_tac[part_hutter_UKC]
QED





(* UCKC is conditional kolmogorov complexity, UKCB is kolmogorov complexity typed the right way *)


Definition univ_mach_def:
  univ_mach U <=> (∀i y x. U (pair y (pair i x)) = on2bl (Phi (bl2n i) (bl2n (pair y x)))) ∧ 
                  ∀m i y x. m <> pair y (pair i x) ==> U m = NONE
End

Theorem Tpow_0[simp]:
  Tpow 0 = []
Proof
  fs[Tpow_def]
QED

Theorem pair_nil[simp]:
  pair [] x = F::x
Proof
  fs[pair_def,bar_def]
QED

Definition subndiv2_def:
  subndiv2 n = recCn (recCn (SOME o pr_div) 
                            [SOME o proj 0;K (SOME 2)]) 
                     [recCn (SOME o (pr2 $-)) [SOME o proj 0;K (SOME n)]]
End

Theorem subndiv2_rec[simp]:
  recfn (subndiv2 n) 1
Proof
  simp[subndiv2_def] >> rpt (irule recfnCn >> rw[]) >> 
  irule primrec_recfn >> fs[primrec_rules]
QED

Theorem subndiv2_correct[simp]:
  subndiv2 n [m] = SOME ((m-n) DIV 2)
Proof
  fs[subndiv2_def, recursivefnsTheory.recCn_def]
QED

Theorem recfn_rec2_Phi[simp]:
  recfn (rec2 Phi) 2
Proof
  mp_tac prtermTheory.recfn_recPhi >> rw[Excl"recfn_recPhi"]
QED

Theorem unary_rec_fns_phi:
  recfn f 1 ==> ∃i. ∀x. Phi i x = f [x]
Proof
  rw[] >> drule_then strip_assume_tac recfns_in_Phi >> qexists_tac`i` >> rw[] >>
  `Phi i (fold [x]) = f [x]` by fs[] >> fs[unary_recfnsTheory.fold_def]
QED

Theorem univ_mach_rf:
  univ_mach U ==> univ_rf U
Proof
  rw[univ_mach_def,univ_rf_def] >> qabbrev_tac`G=recCn recPhi [K (SOME f);subndiv2 1]` >>
  `recfn G 1` by (simp[Abbr`G`] >> rpt (irule recfnCn >> rw[])) >>
  `∀x. G [bl2n (F::x)] = Phi f (bl2n x)` by 
    (simp[Abbr`G`,recCn_def,bool_list_to_num_def]) >> 
  drule_then strip_assume_tac recfns_in_Phi >> 
  LAST_X_ASSUM (qspecl_then [`n2bl i`,`[]`] mp_tac) >> rw[] >> fs[pair_def] >>
  qexists_tac`F::bar (n2bl i)` >> rw[] >> `Phi f x = Phi i (bl2n (F::n2bl x))` suffices_by fs[]>>
  `G [bl2n (F::n2bl x)] = Phi f (bl2n (n2bl x))` by fs[] >> 
  `Phi i (fold [bl2n (F::n2bl x)]) = G [bl2n (F::n2bl x)]` by simp[] >> fs[]
QED



Theorem univ_rf_pair_nonempty:
   univ_mach U  ⇒ {p | U (pair y p) = SOME x} ≠ ∅
Proof
  rw[] >> `{p | U p = SOME x} ≠ ∅` by fs[univ_rf_nonempty,univ_mach_rf] >> fs[EXTENSION] >> 
  fs[univ_mach_def] >> 
  `∃ b c. x' = pair y (pair b c)` by (FIRST_X_ASSUM (qspecl_then [`x'`] mp_tac) >> rw[])  >>
  qexists_tac`pair b c` >> fs[]
QED

(* rename pair to bl pair etc *)

Definition blsnd_def:
  blsnd l = let l' = dropWhile ((=) T) l; sz = LENGTH l - LENGTH l'; in DROP (sz+1) l'
End

Theorem dropWhile_Tpow:
  dropWhile ((=) T) (Tpow n ++ [F] ++ a ++ b) = [F]++a++b
Proof
  Induct_on`n` >> fs[tpow_suc]
QED

Theorem blsnd_pair[simp]:
  blsnd (pair a b) = b
Proof
  fs[blsnd_def,pair_def,bar_def,dropWhile_Tpow] >> qmatch_abbrev_tac`DROP m _ = _` >>
  `m = LENGTH a` suffices_by fs[rich_listTheory.DROP_LENGTH_APPEND] >>
  fs[Abbr`m`]
QED

Definition nblsnd0_def:
  nblsnd0 x = if EVEN x ∧ x<>0 then let (nr) = nblsnd0 ((x-2) DIV 2) in 
                ((nfst nr)+1) *, (nsnd nr)
              else 0 *, x
Termination
WF_REL_TAC`$<` >>rw[DIV_LT_X]
End

Theorem bl2n_eq0[simp]:
  bl2n x = 0 <=> x = []
Proof
  Cases_on`x` >> simp[bool_list_to_num_def] >> rw[]
QED

Theorem nblsnd0_correct:
  nblsnd0 (bl2n (Tpow n ++ [F] ++ x)) = n *, bl2n ([F] ++ x)
Proof
  Induct_on`n` >-  fs[Once nblsnd0_def,bool_list_to_num_def,tpow_suc,EVEN_ADD,EVEN_MULT] >>
  simp[Once nblsnd0_def] >> simp[bool_list_to_num_def,tpow_suc,EVEN_ADD,EVEN_MULT]  
QED

Definition nblsr_def[simp]:
  nblsr x 0 = x ∧
  nblsr x (SUC n) = nblsr ((x-1) DIV 2) n
End

Theorem nblsr0[simp]:
  nblsr 0 n = 0
Proof
  Induct_on`n` >> simp[]
QED



Theorem DROP_n2bl:
  ∀n x. DROP n (n2bl x) = n2bl (nblsr x n)
Proof
  Induct_on`n` >> simp[] >> rw[] >>
  Cases_on`x=0`  >> simp[]
  >- (rpt (simp[Once num_to_bool_list_def]) ) >>
  Cases_on`n2bl x` >> simp[] 
  >- (pop_assum (mp_tac o Q.AP_TERM `bl2n`) >> simp[bool_list_to_num_def,Excl"bl2n_11"] ) >>
  FIRST_X_ASSUM (qspecl_then [`bl2n t`] mp_tac) >> rw[] >> 
  `bl2n t = (x-1) DIV 2` suffices_by fs[] >>
  pop_assum kall_tac >> pop_assum (mp_tac o Q.AP_TERM `bl2n`) >> 
  simp[bool_list_to_num_def,Excl"bl2n_11"] >> rw[]
QED

Definition nblsnd_def:
  nblsnd x = let nr = nblsnd0 x; n = nfst nr; r = nsnd nr; in nblsr r (n+1)
End

Theorem nblsnd_correct:
  n2bl (nblsnd (bl2n (pair a b))) = b 
Proof
  fs[nblsnd_def,GSYM DROP_n2bl,pair_def,bar_def] >>
  ` DROP (nfst (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))))+1)
     (n2bl (nsnd (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b)))))) = b` suffices_by fs[] >>
  `nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))) =  (LENGTH a)  ⊗ bl2n ([F] ++ (a ++ b))` 
    by metis_tac[nblsnd0_correct] >> fs[rich_listTheory.DROP_LENGTH_APPEND]
QED


Definition pr_nblsr_def:
  pr_nblsr = Pr (proj 0) 
                (Cn (pr_div) [Cn (pr2 $-) [proj 1;K 1];K 2])
End

Theorem pr_nblsr_correct:
  ∀n r. pr_nblsr [n;r] = nblsr r n
Proof
  Induct_on`n` >> simp[pr_nblsr_def,nblsr_def] >> rw[] >>
  ` (Pr (proj 0) (Cn pr_div [Cn (pr2 $-) [proj 1; K 1]; K 2]) [n; r] − 1) DIV
        2 = pr_nblsr [n; (r − 1) DIV 2]` suffices_by fs[] >> pop_assum kall_tac >>
  rw[pr_nblsr_def] >> Induct_on`n` >> simp[]
QED

Theorem primrec_pr_nblsr:
  primrec (pr_nblsr) 2
Proof
  simp[pr_nblsr_def,primrec_rules]
QED

Theorem recfn_pr_nblsr:
  recfn (SOME o pr_nblsr) 2
Proof
  irule primrec_recfn >> simp[pr_nblsr_def,primrec_rules]
QED





Definition pr_nblsnd0_def:
  pr_nblsnd0 = 
  WFM (λf n. if (EVEN n ∧ n<>0) then (nfst (f ((n-2) DIV 2)) + 1) *, (nsnd (f ((n-2) DIV 2))) 
             else 0 *, n)
End

Theorem n_sub2_div2:
  ¬((n-2) DIV 2 < n) ==> n=0 
Proof
  rw[] >> `n <= (n-2) DIV 2` by fs[] >> `2*n <= 2* ((n-2) DIV 2)` by fs[] >>
  `2*n <= n-2` by fs[X_LE_DIV] >> Cases_on`n=0` >> simp[]
QED

Theorem pr_nblsnd0_correct:
  pr_nblsnd0 [n] = (pr1 nblsnd0) [n]
Proof
  completeInduct_on`n` >> simp[Once pr_nblsnd0_def,Once nblsnd0_def,Once prnlistTheory.WFM_correct] >> 
  rw[]
  >- (qmatch_abbrev_tac`nfst a = nfst b` >> `a=b` suffices_by fs[] >> simp[Abbr`a`,Abbr`b`] >>
      `pr_nblsnd0 [(n-2) DIV 2] = pr1 nblsnd0 [(n-2) DIV 2]` by fs[] >> fs[] >> fs[Once pr_nblsnd0_def])
  >- (qmatch_abbrev_tac`nsnd a = nsnd b` >> `a=b` suffices_by fs[] >> simp[Abbr`a`,Abbr`b`] >>
       `pr_nblsnd0 [(n-2) DIV 2] = pr1 nblsnd0 [(n-2) DIV 2]` by fs[] >> fs[] >> fs[Once pr_nblsnd0_def]) >> metis_tac[n_sub2_div2]
QED



Definition pr_pr_nblsnd0:
pr_pr_nblsnd0 = pr_cond (Cn pr_eq 
                          [Cn pr_mod 
                              [Cn succ 
                                  [proj 0];
                               K 2];
                           K 0])
                      (Cn (pr2 npair) 
                          [Cn succ 
                              [Cn (pr1 nfst) 
                                   [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ];
                           Cn (pr1 nsnd) 
                              [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ] )
                      (Cn (pr2 npair) 
                          [zerof;
                           Cn succ
                              [proj 0] ] )
End

Theorem primrec_restr_lem:
  primrec (λl. restr (proj 0 l) (proj 1 l) (proj 2 l)) 3
Proof
  `(λl. restr (proj 0 l) (proj 1 l) (proj 2 l)) = pr_cond (Cn pr_le [proj 2;proj 0]) (Cn (pr2 nel) [proj 2;proj 1]) (zerof)` by (fs[FUN_EQ_THM] >> rw[prnlistTheory.restr_def]) >> rw[] >>
  irule primrec_pr_cond >> rw[primrec_rules]
QED

Theorem primrec_pr_nblsnd0:
  primrec pr_nblsnd0 1
Proof
  fs[pr_nblsnd0_def] >> irule prnlistTheory.primrec_WFM >> irule primrec_pr2 >> fs[] >>
  qexists_tac`pr_cond (Cn pr_eq 
                          [Cn pr_mod 
                              [Cn succ 
                                  [proj 0];
                               K 2];
                           K 0])
                      (Cn (pr2 npair) 
                          [Cn succ 
                              [Cn (pr1 nfst) 
                                   [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) 
                                       [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ];
                           Cn (pr1 nsnd) 
                              [Cn (λl. restr (proj 0 l) (proj 1 l) (proj 2 l) ) 
                                  [proj 0;proj 1; Cn pr_div [Cn (pr1 PRE) [proj 0];K 2 ] ] ] ] )
                      (Cn (pr2 npair) 
                          [zerof;
                           Cn succ
                              [proj 0] ] )` >> rw[]
  >- (irule primrec_pr_cond >> rw[primrec_rules] >> rpt (irule unary_recfnsTheory.primrec_Cn >> 
      rw[primrec_rules]) >> fs[primrec_restr_lem] )
  >- (`¬EVEN (SUC m)` by fs[ADD1] >> fs[MOD_2] >> rw[ADD1])
  >- (`EVEN (SUC m)` by fs[ADD1] >> fs[MOD_2] >> rw[ADD1])
QED

Definition pr_nblsnd_def:
  pr_nblsnd = Cn pr_nblsr 
                 [Cn succ [Cn (pr1 nfst) 
                              [Cn pr_nblsnd0
                                  [proj 0]]];
                  Cn (pr1 nsnd) 
                     [Cn pr_nblsnd0
                         [proj 0] ] ]
End

(* UP TO HERE *)

Theorem pr_nblsnd_correct:
  pr_nblsnd [n] = (pr1 nblsnd) [n]
Proof
  fs[pr_nblsnd_def,nblsnd_def] >> 
  `nsnd (pr_nblsnd0 [n]) = nsnd (nblsnd0 n)` by simp[pr_nblsnd0_correct] >>
  `SUC (nfst (pr_nblsnd0 [n])) = nfst (nblsnd0 n) + 1` by simp[pr_nblsnd0_correct] >>
  simp[pr_nblsr_correct,Excl"nblsr_def"]
QED

Theorem primrec_nblsnd:
  primrec pr_nblsnd 1
Proof
  simp[pr_nblsnd_def] >> 
  rpt (irule unary_recfnsTheory.primrec_Cn >> 
       rw[primrec_rules,primrec_pr_nblsr,primrec_pr_nblsnd0])
QED

Theorem recfn_nblsnd:
  recfn (SOME o (pr1 nblsnd)) 1
Proof
  irule primrec_recfn >> irule primrecfnsTheory.primrec_pr1 >> qexists_tac`pr_nblsnd` >> rw[primrec_nblsnd,pr_nblsnd_correct]
QED

Theorem nblsnd_index:
  ∃i. ∀x. Phi i x = (SOME o (pr1 nblsnd)) [x]
Proof
  assume_tac recfn_nblsnd >> drule recfns_in_Phi >> rw[] >> qexists_tac`i` >> rw[] >>
  first_x_assum (qspec_then `[x]` mp_tac) >> rw[]
QED

Theorem pair_LENGTH:
  LENGTH (pair a b) = 2*LENGTH a + 1 + LENGTH b
Proof
  simp[pair_def]
QED

Theorem nblsnd_correct2 = nblsnd_correct |> AP_TERM``bl2n`` |> SIMP_RULE (srw_ss()) [Excl"bl2n_11"]

Theorem univ_mach_pair_pair:
  univ_mach U ==> ∀p x. U p = SOME x <=> 
                        ∃a i b. p = pair a (pair i b) ∧ 
                                Phi (bl2n i) (bl2n (pair a b)) = SOME (bl2n x)
Proof
  reverse (rw[univ_mach_def,EQ_IMP_THM]) >- rw[on2bl_def] >>
  `∃a b c. p=pair a (pair b c)` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  qexists_tac`a` >> qexists_tac`b` >> qexists_tac`c` >> rw[] >>
  `on2bl (Phi (bl2n b) (bl2n (pair a c)) ) = SOME x` by metis_tac[] >> fs[on2bl_def]
QED

Theorem pair_11:
  pair a b = pair c d <=> a=c ∧ b=d
Proof
  rw[EQ_IMP_THM,pair_def,bar_def] >> 
  `LENGTH a = LENGTH c ∧ a++b = c++d` by 
    (`Tpow (LENGTH a) ++ [F] ++ (a ++ b) = Tpow (LENGTH c) ++ [F] ++ (c ++ d)` by metis_tac[APPEND_ASSOC] >> metis_tac[Tpow_Fapp_eq]) >> 
  `DROP (LENGTH a) (a++b) = DROP (LENGTH c) (c++d)` by fs[] >> 
  `TAKE (LENGTH a) (a++b) = TAKE (LENGTH c) (c++d)` by fs[] >>
  fs[rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.TAKE_LENGTH_APPEND]
QED

Definition nblft_def:
  nblft x 0 = 0n ∧
  nblft x (SUC n) = if x=0 then 0 
                    else (if EVEN x then (2 + 2* (nblft ((x-2) DIV 2) n) )
                          else (1 + 2*(nblft ((x-1) DIV 2) n)))
End

Theorem nblft_zero[simp]:
  nblft 0 x = 0
Proof
  Induct_on`x` >> fs[nblft_def]
QED

Theorem n2bl_zero[simp]:
  n2bl 0 = []
Proof
  simp[Once num_to_bool_list_def]
QED


Theorem n2bl_2_EVEN_lem:
   T::n2bl (x) = n2bl (2 * x + 2)
Proof
  `EVEN (2 * x + 2)` by 
    (`EVEN (2*(x+1))` suffices_by rw[LEFT_ADD_DISTRIB] >> metis_tac[EVEN_DOUBLE]) >>
  `n2bl (2*x + 2) = T::(n2bl x)` by (simp[Once num_to_bool_list_def]) >> metis_tac[]
QED

Theorem n2bl_1_ODD_lem:
   F::n2bl (x) = n2bl (2 * x + 1)
Proof
  `ODD (2 * x + 1)` by 
    (`∃m. 2*x + 1 = SUC (2*m)` by (qexists_tac`x` >> fs[]) >> metis_tac[ODD_EXISTS] ) >>
  `~EVEN (2 * x + 1)` by fs[ODD_EVEN] >>
  `n2bl (2*x + 1) = F::(n2bl x)` by (simp[Once num_to_bool_list_def]) >> metis_tac[]
QED

Theorem TAKE_n2bl:
  ∀n x. TAKE n (n2bl x) = n2bl (nblft x n)
Proof
  Induct_on`n` >> simp[] >> rw[]  >> 
  simp[nblft_def] >>rw[] >>
  simp[Once num_to_bool_list_def] >> rw[n2bl_1_ODD_lem,n2bl_2_EVEN_lem]
QED

Definition nblfst_def:
  nblfst x = (let nr = nblsnd0 x;n=nfst nr;r = nsnd nr in nblft (nblsr r (1)) n)
End

Theorem DROP_bl2n:
  ∀x n. DROP n x = n2bl (nblsr (bl2n x) n)
Proof
  rw[] >> `DROP n (n2bl (bl2n x)) = n2bl (nblsr (bl2n (n2bl (bl2n x))) n)` suffices_by 
    (rw[] >> fs[bool_num_inv]) >>
  metis_tac[DROP_n2bl,bool_num_inv]
QED

Theorem nblfst_correct:
  nblfst (bl2n (pair a b)) = bl2n a
Proof
  `n2bl (nblfst (bl2n (pair a b))) = a` suffices_by 
    (rw[] >> `bl2n (n2bl (nblfst (bl2n (pair a b)))) = bl2n a` by fs[] >> 
     metis_tac[bool_num_inv]) >>
  fs[nblfst_def,nblsnd_def,GSYM TAKE_n2bl,pair_def,bar_def] >>
  `TAKE (nfst (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b) ))))
     (n2bl
        (nblsr (nsnd (nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))))) 1)) =
   a` suffices_by fs[] >>
  `nblsnd0 (bl2n (Tpow (LENGTH a) ++ [F] ++ (a ++ b))) =  (LENGTH a)  ⊗ bl2n ([F] ++ (a ++ b))` 
    by metis_tac[nblsnd0_correct] >> fs[rich_listTheory.TAKE_LENGTH_APPEND] >>
  simp[GSYM DROP_bl2n] >> fs[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Definition rUMibl_def:
  rUMibl = recCn recPhi 
                [recCn (SOME o (pr1 nblfst)) 
                       [SOME o proj 0];
                 recCn (SOME o (pr1 nblsnd)) 
                       [SOME o proj 0]]
End

Theorem rUMibl_correct:
  rUMibl [bl2n (pair a b)] = Phi (bl2n a) (bl2n b)
Proof
  fs[rUMibl_def,rec2_def,recCn_def,nblfst_correct,nblsnd_correct2]
QED

Definition lam_nblft_def:
  lam_nblft = LAM "x" (
    LAM "y" (
      VAR "y" 
       @@ (K @@ church 0)
       @@ (LAM "r" ( 
             LAM "x'" (
               cis_zero @@ VAR "x'" 
                        @@ church 0
                        @@ (cis_zero 
                             @@ (cmod @@ VAR "x'" @@ church 2)
                             @@ (cplus @@ church 2 
                                       @@ (cmult @@ church 2 
                                                 @@ (VAR "r" @@ (cdiv @@ (cminus @@ VAR"x'" 
                                                                                 @@ church 2) 
                                                                      @@ church 2) )  ) )
                             @@ (cplus @@ church 1 
                                       @@ (cmult @@ church 2 
                                                 @@ (VAR "r" @@ (cdiv @@ (cminus @@ VAR"x'" 
                                                                                 @@ church 1) 
                                                                      @@ church 2) )  ) )  ) )))
       @@ VAR "x"
    )
  )
End

Theorem FV_lam_nblft:
  FV lam_nblft = {}
Proof
  simp[lam_nblft_def,EXTENSION]
QED

Theorem lam_nblft_equiv = brackabs.brackabs_equiv [] lam_nblft_def

Theorem lam_nblft_behaviour:
   ∀x y. lam_nblft @@ church x @@ church y == church (nblft x y)
Proof
  Induct_on`y` >> simp_tac (bsrw_ss()) [lam_nblft_equiv,nblft_def] >> rw[] >>
  simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour] >> fs[EVEN_MOD2] >>
  simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour] >>
  full_simp_tac (bsrw_ss()) [lam_nblft_equiv] >> simp[]
QED

Theorem lam_nblft_phi:
  Phi (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) (m *, n) = SOME (nblft m n)
Proof
  simp[Phi_def] >> simp_tac (bsrw_ss()) [lam_nblft_behaviour,normal_orderTheory.bnf_bnf_of]
QED



Theorem nblft_phiii:
  ∀z1 z2. rec2 (λx y. SOME (nblft x y)) [z1;z2] = 
  recCn 
    (recCn 
       recPhi 
       [(λx. SOME (K (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) x ) ) ;
        SOME o proj 0 ]) [(SOME ∘ pr2 $*,)] [z1;z2]
Proof
  rpt strip_tac >> simp[Excl"fromTerm_def",recPhi_correct,recCn_def,lam_nblft_phi ]
QED

Theorem nblft_phi_lem:
rec2 (λx y. SOME (nblft x y)) = 
  recCn 
    (recCn 
       recPhi 
       [(λx. SOME (K (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd) ) ) x ) ) ;
        SOME o proj 0 ]) [(SOME ∘ pr2 $*,)]
Proof
  rw[FUN_EQ_THM,Excl"fromTerm_def"] >> Cases_on`x` >> rw[Excl"fromTerm_def"] 
  >-(simp[recCn_def,Excl"fromTerm_def"] >> `SOME 0 =
     Phi (dBnum (fromTerm (S @@ (B @@ lam_nblft @@ cnfst) @@ cnsnd))) (0 *, 0)` 
       suffices_by simp[Excl"fromTerm_def"] >> simp[lam_nblft_phi]) >> 
  Cases_on`t` >> rw[Excl"fromTerm_def"]  
  >-(simp[recCn_def,Excl"fromTerm_def"] >> simp[lam_nblft_phi]) >>
  simp[recCn_def,Excl"fromTerm_def"] >> simp[lam_nblft_phi]
QED

Theorem recfn_some_num:
  recfn (λx. SOME (a:num)) 1
Proof
  `(λ(x:num list). SOME a) = K (SOME a)` by (simp[FUN_EQ_THM,combinTheory.K_THM]) >> 
  `recfn (K (SOME a)) 1` suffices_by simp[] >> simp[recfn_K]
QED

Theorem recfn_nblfst:
  recfn (rec1 (SOME o nblfst)) 1
Proof
  irule recfn_rec1 >> fs[nblfst_def] >>
  qexists_tac`recCn (rec2 (λx y. SOME (nblft x y) )) [SOME o Cn pr_nblsr [K 1;Cn (pr1 nsnd) [Cn pr_nblsnd0 [proj 0]] ];
                    SOME o Cn (pr1 nfst) [Cn pr_nblsnd0 [proj 0]] ]` >> rw[]
  >- (irule recfnCn >> rw[recfn_rules]
      >- (irule primrec_recfn >> 
          rpt (irule unary_recfnsTheory.primrec_Cn >> simp[primrec_pr_nblsr,primrec_rules,primrec_pr_nblsnd0]) )
      >- (irule primrec_recfn >> 
          rpt (irule unary_recfnsTheory.primrec_Cn >> simp[primrec_pr_nblsr,primrec_rules,primrec_pr_nblsnd0]))
      >- (simp[nblft_phi_lem,Excl"fromTerm_def"] >> irule recfnCn >> 
          rw[recfn_rules,Excl"fromTerm_def"]
          >- (irule primrec_recfn >> simp[primrec_npair]) >> irule recfnCn >> 
         rw[recfn_rules,Excl"fromTerm_def"] >> simp[recfn_some_num] )  )
  >- (simp[recCn_def] >>  simp[pr_nblsr_correct,Excl"nblsr_def",ADD1,pr_nblsnd0_correct])
QED

Theorem rec1_pr1:
  SOME o pr1 f = rec1 (SOME o f)
Proof
  simp[FUN_EQ_THM] >> Cases_on`x` >> rw[rec1_def,pr1_def]
QED

Theorem rUMibl_recfn:
  recfn rUMibl 1
Proof
  fs[rUMibl_def] >> irule recfnCn >> rw[] >> irule recfnCn >> rw[recfn_rules,recfn_nblsnd,recfn_nblfst] >> `(SOME ∘ pr1 nblfst) = rec1 (SOME o nblfst)` suffices_by fs[recfn_nblfst] >> fs[rec1_pr1]
QED

Theorem rUMibl_index:
  ∃i. ∀x. Phi i x = rUMibl [x]
Proof
  fs[unary_rec_fns_phi,rUMibl_recfn]
QED

Theorem extra_information1:
  univ_mach U ==> ∃c. ∀x y. (CKC U x y) <= (KC U x) + c
Proof
  rw[KC_def,CKC_def,cond_core_complexity_def,core_complexity_def] >> 
  fs[univ_rf_nonempty,univ_rf_pair_nonempty,univ_mach_rf] >> 
  `univ_rf U` by fs[univ_mach_rf] >> 
  strip_assume_tac nblsnd_index >>
  pop_assum (qspec_then `bl2n (pair a b)` (assume_tac o Q.GENL[`a`,`b`])) >> 
  fs[nblsnd_correct2]>> fs[univ_mach_def] >> 
  `∀a b. U (pair b (pair (n2bl i) a)) = SOME a` by fs[on2bl_def] >> 
  assume_tac rUMibl_index >> fs[] >> rename [`∀x. Phi rUMi x = rUMibl [x]`] >>

  qabbrev_tac`j = rUMi o i` >> 
  `∀x y. Phi j (bl2n (pair x y)) = Phi rUMi (bl2n y)` by 
    (simp[Abbr`j`,computable_composition_def,nblsnd_correct2]) >> 
  pop_assum (qspecl_then [`x`,`pair a b`] (assume_tac o Q.GENL[`x`,`a`,`b`])) >>
  `∀x a b. U (pair x (pair (n2bl j) (pair a b))) = U (pair a (pair (n2bl rUMi) b))` by fs[] >>
  `univ_mach U` by metis_tac[GSYM univ_mach_def] >>
  `∀x a b. Phi j (bl2n (pair x (pair a b))) = Phi (bl2n a) (bl2n b)` by fs[rUMibl_correct] >>

  qexists_tac`2*(LENGTH (n2bl j)) + 1` >> rw[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (simp[EXTENSION] >> metis_tac[]) >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[] 
  >-(fs[EXTENSION] >> `{p | U p = SOME x} ≠ ∅` by fs[univ_rf_nonempty] >> 
     fs[EXTENSION] >> metis_tac[] ) >> fs[PULL_EXISTS] >>
  `U (pair y (pair (n2bl j) p')) = SOME x` by metis_tac[] >> 
  last_x_assum drule >> simp[pair_LENGTH]
QED


val nblfst_i_def =  new_specification ("nblfst_i_def",["nblfst_i"],MATCH_MP unary_rec_fns_phi recfn_nblfst |> SIMP_RULE (srw_ss()) [rec1_def] )

(* Up to here *)

Theorem extra_information2:
  univ_mach U ==> ∃c. ∀x y. KC U x <= KC U (pair x y) + c
Proof
  rw[KC_def,core_complexity_def] >>
  fs[univ_rf_nonempty,univ_rf_pair_nonempty,univ_mach_rf] >> 
  `univ_rf U` by fs[univ_mach_rf] >> fs[univ_mach_def] >>
  assume_tac rUMibl_index >> fs[] >> rename [`∀x. Phi rUMi x = rUMibl [x]`] >>
  qabbrev_tac`j = nblfst_i o rUMi` >> 
  qexists_tac`2*(LENGTH (n2bl j)) + 1` >> rw[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[] 
  >-(fs[EXTENSION] >> `{p | U p = SOME x} ≠ ∅` by fs[univ_rf_nonempty] >> 
     fs[EXTENSION] >> metis_tac[] ) >>
  DEEP_INTRO_TAC MIN_SET_ELIM >> rw[] 
  >-(fs[EXTENSION] >> `{p | U p = SOME (pair x y)} ≠ ∅` by fs[univ_rf_nonempty] >> 
     fs[EXTENSION] >> metis_tac[] ) >> fs[PULL_EXISTS] >> 
  `U (`
QED

Theorem subadditivity1:
  univ_mach U ==> ∃c. ∀x y. KC U (x++y) <= KC U (pair x y) + c
Proof

QED

Theorem subadditivity2:
  univ_mach U ==> ∃c. ∀x y. KC U (pair x y) <= KC U x +  CKC U y x + c
Proof

QED

Theorem subadditivity3:
  univ_mach U ==> ∃c. ∀x y. KC U x +  CKC U y x <= KC U x + KC U y + c
Proof

QED


Theorem symmetry_of_information1a:
  unif_mach U ==> ∃c. ∀x y.  CKC U x (pair y (KC U y)) + KC U y <= KC U (pair x y) + c
Proof

QED

Theorem symmetry_of_information1b:
  unif_mach U ==> ∃c. ∀x y. KC U (pair x y) <=  CKC U x (pair y (KC U y)) + KC U y + c
Proof

QED

Theorem symmetry_of_information2:
  unif_mach U ==> ∃c. ∀x y. KC U (pair x y) <= KC U (pair y x) + c
Proof

QED

Theorem symmetry_of_information1b:
  unif_mach U ==> ∃c. ∀x y.  CKC U y (pair x (KC U x)) + KC U x <= 
                           CKC U x (pair y (KC U y)) + KC U y + c
Proof

QED



val _ = export_theory()
