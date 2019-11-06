open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmogorov_complexityTheory kraft_ineqTheory invarianceResultsTheory
open churchDBTheory

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

val narg_kolmog_def = Define`narg_kolmog x = bl2n (arg_kolmog x)`;

val plain_kolmog_def = Define`
  plain_kolmog x = THE (kolmog_complexity x (λy. Phi (bl2n y) 0))
`;

Theorem plain_kolmog_exists:
  ∀x. ∃y. kolmog_complexity x (λy. Phi (bl2n y) 0) = SOME y
Proof
  rw[kolmog_complexity_def,EXTENSION] >> simp[Phi_def] >>
  qexists_tac`n2bl (dBnum (fromTerm (K @@ church x)))` >> simp[] >>
  qexists_tac`church x` >>
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

Theorem plain_kolmog_thm:
  plain_kolmog x = (MIN_SET {LENGTH p |  Phi (bl2n p) 0 = SOME x})
Proof
  fs[plain_kolmog_def,kolmog_complexity_def] >>
  Cases_on`{y | Phi (bl2n y) 0 = SOME x} = ∅` >>
  fs[] >> `∃y. Phi (bl2n y) 0 = SOME x` by fs[Phi_bl2nx_0] >>
  `y∈{y | Phi (bl2n y) 0 = SOME x}` by fs[] >> metis_tac[MEMBER_NOT_EMPTY]
QED



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

Theorem plain_kolmog_smallest:
  Phi k 0 = SOME y ⇒ plain_kolmog y ≤ ℓ k
Proof
  simp[plain_kolmog_thm] >> strip_tac >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (simp[EXTENSION] >> metis_tac[Phi_bl2nx_0]) >>
  fs[PULL_EXISTS]
QED

Theorem plain_kolmog_props:
  ∀y. ∃z. plain_kolmog y = ℓ z ∧ Phi z 0 = SOME y
Proof
  simp[plain_kolmog_thm] >> strip_tac >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- simp[MIN_SET_L_PHI_NON_EMPTY] >> qexists_tac ‘bl2n p’ >> simp[]
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

Theorem EL_log2list :
  n < 2 ** i ⇒ EL n (log2list i) = n + 2 ** i
Proof
  simp[log2list_def, EL_GENLIST]
QED

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

(* proven *)
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




(* might not need above here *)

val fkmin_def = Define`fkmin m = MIN_SET {n | m<= plain_kolmog n}`

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
(*

Theorem plain_kolmog_lb_exists:
  ∃x. m <= plain_kolmog x
Proof
  CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
  `∀x. ∃i. Phi i 0 = SOME x ∧ ℓ i < m` by metis_tac[plain_kolmog_props] >>
  fs[SKOLEM_THM] >> 
  `FINITE (count m)` by fs[FINITE_COUNT] >>
  `INFINITE {f x | x | T}` by 
    (`SURJ (λx. Phi (f x) 0) UNIV {SOME n|T}` by 
       (fs[SURJ_DEF] >> rw[]) >> `IMAGE (λx. Phi (f x) 0) UNIV = {SOME n|T}` by fs[IMAGE_SURJ]>>
     fs[IMAGE_DEF] >> 
     `{SOME n | T} = IMAGE (λx. Phi x 0) {f x | x | T}` by 
       (fs[IMAGE_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[] 
        >- (qexists_tac`f n` >> metis_tac[]) 
        >- (qexists_tac`x''` >> metis_tac[]) ) >> 
     `SURJ (λx. Phi x 0) {f x | x | T} {SOME n | T}` by fs[SURJ_IMAGE] >>
     `¬(FINITE {SOME (n:num) | T})` by 
       (`INFINITE 𝕌(:num option)` by 
          (fs[infinite_num_inj] >> qexists_tac`SOME` >> rw[INJ_DEF]) >> 
        `{SOME n | T} = 𝕌(:num option) DIFF {NONE}` by  
          (rw[EXTENSION] >> eq_tac >> rw[] >> Cases_on`x` >> fs[]) >> 
        `FINITE {NONE}` by fs[FINITE_SING] >> 
        rw[] >> fs[INFINITE_DIFF_down]) >> 
     `∃g. INJ g {SOME n | T} {f x | x | T} ∧ ∀y. y ∈ {SOME n | T} ⇒ (λx. Phi x 0) (g y) = y` by 
       (irule pred_setTheory.SURJ_INJ_INV >> fs[]) >> metis_tac[INFINITE_INJ] ) >>
  `FINITE {i | ∃x. i = (f x)}` by 
    (`{i | ∃x. i = (f x)} ⊆ count (2**m + 2**m)` suffices_by 
       metis_tac[SUBSET_FINITE_I,FINITE_COUNT] >> simp[SUBSET_DEF] >> rw[] >> fs[] >>
     `ℓ (f x') < m` by fs[] >> 
     `MEM ((f x') + 1) (log2list (ℓ (f x')))` by metis_tac[ELL_log2list] >> 
     fs[log2list_def,MEM_GENLIST] >> 
     `f x' < 2 ** ℓ (f x') + 2 ** ℓ (f x')` by fs[] >>
     `2 ** (ℓ (f x'))+2 ** (ℓ (f x')) < 2 ** m+2 ** m` by fs[] >> 
     `f x' < 2 ** m + 2 ** m` by metis_tac[LESS_TRANS] >> fs[]) >> 
   `SURJ (λx. x)  {i | (∃x. i = (f x))} {f x | x | T}` by 
    (fs[SURJ_DEF] >> rw[] ) >>
  `FINITE {f x | x | T}` by metis_tac[FINITE_SURJ]
QED

Theorem kfkmin_lb:
  ∀m. m <= plain_kolmog (fkmin m)
Proof
  rw[fkmin_def] >> irule f_min_set_f >> fs[plain_kolmog_lb_exists]
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
  >- (`x'+2**i < 2** i + 2**i` by fs[] >> `2**i + 2**i = 2*2**i` by fs[GSYM TIMES2] >>
      `2**i + 2**i = 2 ** SUC i` by fs[EXP] >> fs[ADD1])
  >- (qexists_tac`x-2**i` >> fs[] >> `2*2**i = 2 ** SUC i` by fs[EXP] >> fs[ADD1])
QED

Theorem exp_ELL1:
  2 ** ℓ x <= x+1
Proof
  `MEM (x+1) (log2list (ℓ x))` by metis_tac[ELL_log2list] >>
  fs[MEM_GENLIST,log2list_def]
QED

Theorem exp_ELL2:
  x+1 < 2 ** ((ℓ x)+1 )
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
  `2 ** ℓ x <= x+1 ∧ 2 ** ℓ y <= y+1 ∧ 2 ** ℓ (x*y) <= (x*y)+1` by fs[exp_ELL1] >>
  `x + 1 < 2 ** (ℓ x + 1) ∧ y + 1 < 2 ** (ℓ y + 1) ∧ (x*y) + 1 < 2 ** (ℓ (x*y) + 1)` by fs[exp_ELL2] >> 
  `ℓ x + ℓ y + 2 <= ℓ (x * y)` by fs[] >> 
  `2 ** (ℓ x + ℓ y) <= (x+1) * (y+1) ∧ (x + 1) * (y + 1) < 2 ** (ℓ x + ℓ y + 2)` by 
  (fs[LESS_MONO_MULT2,EXP_ADD] >> 
   `(x + 1 ) * (y + 1) < (2 * 2 ** ℓ x) * (y+1)` by fs[LT_MULT_LCANCEL] >>
   `0<(2 * 2 ** ℓ x)` by fs[] >>
   `(2 * 2 ** ℓ x) * (y+1) < (2 * 2 ** ℓ x ) *  (2 * 2 ** ℓ y)` by rw[LT_MULT_LCANCEL] >> 
   `(x + 1) * (y + 1) < 2 * 2 ** ℓ x * (2 * 2 ** ℓ y)` by rw[] >> rw[]) >>
  `x*y+1 <= (x+1)*(y+1)` by fs[] >> 
  `(x + 1) * (y + 1) < 2 ** (ℓ (x*y) )` by 
    (`2 ** (ℓ x + ℓ y + 2) <= 2 ** (ℓ (x*y))` by fs[] >> rw[]) >> fs[]
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



val _ = overload_on ("UKC",``(λx. THE (kolmog_complexity (x:num) (U:bool list -> num option ) ))``)

Theorem univ_rf_smallest:
  univ_rf U ∧ U k = SOME y ⇒ UKC y ≤ LENGTH k
Proof
  rw[univ_rf_def] >> simp[kolmog_complexity_def] >> 
  `{p | U p = SOME y} <> ∅` by (fs[EXTENSION] >> metis_tac[]) >>
  simp[] >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (simp[EXTENSION] >> metis_tac[]) >>
  fs[PULL_EXISTS]
QED


Theorem univ_rf_kolmog_fn_ub:
  computable f ∧ univ_rf U ==> 
  ∃c. ∀m. 
    UKC (f m) <=  ℓ (m)  + c
Proof
  rw[] >> 
   `(∀n. Phi (recfn_index2 f) n = SOME (f n)) ∧
    ∀j. (∀n. Phi j n = SOME (f n)) ⇒ recfn_index2 f ≤ j` by fs[recfn_index2_def]>>
  `∀m. Phi (recfn_index2 f) (m) = SOME (f m)` by fs[] >>
  `∃g. ∀m. Phi (recfn_index2 f) m = U (g ++ n2bl m)` by 
    (fs[univ_rf_def] >> `∃g. ∀x. Phi (recfn_index2 f) x = U (g ++ n2bl x)` by fs[])>>
  qexists_tac`LENGTH g` >> rw[] >>
  `UKC (f m) ≤ LENGTH (g ++ n2bl m)` by fs[univ_rf_smallest] >> fs[]
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
  univ_rf U ==> ∃c. ∀m. UKC (m) <= (ℓ (m) ) + c
Proof
  rw[] >> `computable (λx. x)` by fs[computable_id] >> 
  qabbrev_tac`f = (λx. (x:num))` >> 
  `∃c. ∀m. UKC (f m) <=  ℓ (m)  + c` by 
    metis_tac[univ_rf_kolmog_fn_ub]  >>metis_tac[ADD_COMM]
QED



Definition UKCfkmin_def:
  UKCfkmin (U:bool list->num option) m = MIN_SET {n | m <= UKC n}
End

Theorem MIN_SET_L_PHI_NPAIR_NON_EMPTY:
  {LENGTH p | Phi (nfst (bl2n p)) (nsnd (bl2n p)) = SOME y} <> {}
Proof
  fs[EXTENSION,Phi_bl2nx_npair]
QED


Theorem univ_rf_kolmog_props:
  univ_rf U ==> ∀y. ∃z. UKC y = LENGTH z ∧ U z = SOME y
Proof
  rw[] >> fs[kolmog_complexity_def,univ_rf_nonempty] >>  
  DEEP_INTRO_TAC MIN_SET_ELIM >>  
  rw[] >> `{p | U p = SOME y} ≠ ∅` by fs[univ_rf_nonempty] >> 
  fs[EXTENSION] >> metis_tac[]
QED


Theorem univ_rf_kolmog_lb_exists:
  univ_rf U ==> ∃x. m <= UKC x
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
     `¬(FINITE {SOME (n:num) | T})` by 
       (`INFINITE 𝕌(:num option)` by 
          (fs[infinite_num_inj] >> qexists_tac`SOME` >> rw[INJ_DEF]) >> 
        `{SOME n | T} = 𝕌(:num option) DIFF {NONE}` by  
          (rw[EXTENSION] >> eq_tac >> rw[] >> Cases_on`x` >> fs[]) >> 
        `FINITE {NONE}` by fs[FINITE_SING] >> 
        rw[] >> fs[INFINITE_DIFF_down]) >> 
     `∃g. INJ g {SOME n | T} {f x | x | T} ∧ ∀y. y ∈ {SOME n | T} ⇒ (λx. U x) (g y) = y` by 
       (irule pred_setTheory.SURJ_INJ_INV >> fs[]) >> metis_tac[INFINITE_INJ] ) >>
  `FINITE {LENGTH i | ∃x. i = (f x)}` by 
    (`{LENGTH i | ∃x. i = (f x)} ⊆ count (2**m + 2**m)` suffices_by 
       (metis_tac[SUBSET_FINITE_I,FINITE_COUNT]) >> simp[SUBSET_DEF] >> rw[] >> fs[] >>
     `LENGTH (f x') < m` by fs[] >> 
     `m < 2* 2** m` suffices_by fs[] >> `m < 2**m` by simp[X_LT_EXP_X_IFF] >> fs[]) >> 
   `SURJ (λx. x)  { i | (∃x. i = (f x))} {f x | x | T}` by 
    (fs[SURJ_DEF] >> rw[] ) >>
  `FINITE {i | (∃x. i = f x)}` by (`FINITE {(i:bool list) | LENGTH i < m}` by 
    fs[finite_bool_list_lt_n] >> 
  `{i | (∃x. i = f x)} ⊆ {i | LENGTH i < m}` by (fs[SUBSET_DEF] >> rw[] >> fs[]) >>
    metis_tac[SUBSET_FINITE]) >>
  metis_tac[FINITE_SURJ]
QED


Theorem UKCfkmin_def_lb:
  univ_rf U ==> ∀m. m <= UKC (UKCfkmin U m)
Proof
  rw[UKCfkmin_def] >> `(∃x. m ≤ UKC x)` by  fs[univ_rf_kolmog_lb_exists]>>
  `m ≤ (λx. UKC x) (MIN_SET {n | m ≤ (λx. UKC x) n})` by (irule f_min_set_f >> metis_tac[]) >>fs[]
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
  univ_rf U ∧ computable UKC ==> computable (UKCfkmin U)
Proof
  rw[] >> `unbounded UKC` by fs[unbounded_def,univ_rf_kolmog_lb_exists] >>
  simp[computable_def,UKCfkmin_def] >> fs[computable_arg_min_set]
QED



Theorem UKCkol_fkmin_lb:
  univ_rf U ∧ computable UKC ==> 
  ∃c. ∀m. UKC (UKCfkmin U m) <= (ℓ m)+ c
Proof
  rw[] >> `computable (UKCfkmin U)` by fs[computable_UKCfkmin] >> 
  `∃c. ∀m. UKC (UKCfkmin U m) ≤ (ℓ m) + c` by 
    metis_tac[univ_rf_kolmog_fn_ub] >> qexists_tac`c` >> rw[] >> fs[]
QED



Theorem UKCcompkol_lb:
  univ_rf U ∧ computable UKC ==> ∃c. ∀m. m <=  2*(ℓ m) + c
Proof
  rw[] >> `∃c. ∀m. UKC (UKCfkmin U m) <= (ℓ m) + c` by fs[UKCkol_fkmin_lb]>>
  `∀m. m <= UKC (UKCfkmin U m)` by fs[UKCfkmin_def_lb]  >> qexists_tac`c` >> rw[] >>
  `m ≤ UKC (UKCfkmin U m)` by fs[] >> `UKC (UKCfkmin U m) ≤ c + ℓ m` by fs[] >>fs[]
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
  univ_rf U ∧ computable UKC ==> F
Proof
  strip_tac >> `∃c. ∀m. m <=  2*(ℓ m) + c` by metis_tac[UKCcompkol_lb] >>
  `∃m. ¬(m<= 2*(ℓ m) + c)` by fs[exists_log_lb] >> metis_tac[]
QED

Theorem UKC_incomp:
  univ_rf U ==> ¬(computable UKC)
Proof
  metis_tac[part_hutter_UKC]
QED




val _ = overload_on ("UKCB",``(λx. THE (kolmog_complexity_new (x:bool list) (U:bool list -> bool list option ) ))``)


val _ = overload_on ("UCKC",``(λx y. THE (cond_kolmog_complexity (x:bool list) (y:bool list)  (U:bool list -> bool list option ) ))``)

Definition univ_rf_bl:
  univ_rf_bl U <=> univ_rf (λy. obl2n (U y))
End



(* up to here *)

Definition ignore_machine:
  ignore x n = if ∃k. x = 2 ** k then x/(2**(2*n + 1)) else ignore (x-2**n) (n+1)
End

Definition ig_n_mach_def:
  ig_n_mach (x:num) (n:num) = x DIV (2**n)
End


Theorem ig_n_mach_corr:
  ig_n_mach (bl2n (x++y)) (LENGTH x) = bl2n y
Proof
  Induct_on`x` >> fs[bool_list_to_num_def,ig_n_mach_def] >> rw[]
  >- (rename[`(2 * a + 2) DIV 2 ** (SUC b) = c`] >> 
      `(2*a+2) DIV 2 ** SUC b = a DIV 2 ** b` suffices_by fs[] >> 
      `((2*a+2) DIV 2) DIV 2 ** b = a DIV 2 ** b` suffices_by 
        (fs[] >> `(2*a+2) = 2*(a+1)` by fs[] >> `2 ** SUC b = 2 * (2 ** b)` by fs[EXP] >> rw[]>>
         fs[] >>  ) >> )
  >- (rename[`(2 * a + 1) DIV 2 ** (SUC b) = c`])
QED

Theorem ignore_correct:
  ignore (bl2n (pair a b)) 0 = b
Proof
  simp[bool_list_to_num_de,pair_def,bar_def]
QED

(* UCKC is conditional kolmogorov complexity, UKCB is kolmogorov complexity typed the right way *)

Theorem extra_information1:
  univ_rf_bl U ==> ∃c. ∀x y. (UCKC x y) <= (UKCB x) + c
Proof
  rw[ univ_rf_bl,univ_rf_def,kolmog_complexity_new_def,cond_kolmog_complexity_def,kolmog_complexity_def] >> fs[obl2n]
  (* The f we need to construct is the function which ignores the 1^|x|x on the input and runs the remainder  *)
QED

Theorem extra_information2:
  univ_rf U ==> ∃c. ∀x y. UKCB x <= UKCB (pair x y) + c
Proof

QED

Theorem subadditivity1:
  univ_rf U ==> ∃c. ∀x y. UKCB (x++y) <= UKCB (pair x y) + c
Proof

QED

Theorem subadditivity2:
  univ_rf U ==> ∃c. ∀x y. UKCB (pair x y) <= UKCB x + UCKC y x + c
Proof

QED

Theorem subadditivity3:
  univ_rf U ==> ∃c. ∀x y. UKCB x + UCKC y x <= UKCB x + UKCB y + c
Proof

QED


Theorem symmetry_of_information1a:
  unif_rf U ==> ∃c. ∀x y. UCKC x (pair y (UKCB y)) + UKCB y <= UKCB (pair x y) + c
Proof

QED

Theorem symmetry_of_information1b:
  unif_rf U ==> ∃c. ∀x y. UKCB (pair x y) <= UCKC x (pair y (UKCB y)) + UKCB y + c
Proof

QED

Theorem symmetry_of_information2:
  unif_rf U ==> ∃c. ∀x y. UKCB (pair x y) <= UKCB (pair y x) + c
Proof

QED

Theorem symmetry_of_information1b:
  unif_rf U ==> ∃c. ∀x y. UCKC y (pair x (UKCB x)) + UKCB x <= 
                          UCKC x (pair y (UKCB y)) + UKCB y + c
Proof

QED



val _ = export_theory()
