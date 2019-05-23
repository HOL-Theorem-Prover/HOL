open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmog_complexTheory kraft_ineqTheory
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
  >- (`x'+2**i < 2** i + 2**i` by fs[] >> `2**i + 2**i = 2*2**i` by simp[GSYM TIMES2] >>
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

val np_kolmog_def = Define`
  np_kolmog x = THE (kolmog_complexity x (λy. Phi (nfst (bl2n y)) (nsnd (bl2n y))))
`;

Theorem np_kolmog_exists:
  ∀x. ∃y. kolmog_complexity x (λy. Phi (nfst (bl2n y)) (nsnd (bl2n y))) = SOME y
Proof
  rw[kolmog_complexity_def,EXTENSION] >> simp[Phi_def] >>
  qexists_tac`n2bl (npair (dBnum (fromTerm (K @@ church x))) (dBnum (fromTerm (K @@ church x))))` >> simp[] >>
  qexists_tac`church x` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
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

Theorem np_kolmog_thm:
  np_kolmog x = (MIN_SET {LENGTH p |  Phi (nfst (bl2n p)) (nsnd (bl2n p)) = SOME x})
Proof
  fs[np_kolmog_def,kolmog_complexity_def] >>
  Cases_on`{y | Phi (nfst (bl2n y)) (nsnd (bl2n y)) = SOME x} = ∅` >>
  fs[] >> `∃y. Phi (nfst (bl2n y)) (nsnd (bl2n y)) = SOME x` by fs[Phi_bl2nx_npair] >>
  `y∈{y | Phi (nfst (bl2n y)) (nsnd (bl2n y)) = SOME x}` by fs[] >> metis_tac[MEMBER_NOT_EMPTY]
QED


Theorem np_kolmog_smallest:
  Phi (nfst k) (nsnd k) = SOME y ⇒ np_kolmog y ≤ ℓ k
Proof
  simp[np_kolmog_thm] >> strip_tac >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- (simp[EXTENSION] >> metis_tac[Phi_bl2nx_npair]) >>
  fs[PULL_EXISTS]
QED


Theorem np_kolmog_fn_ub:
  computable f ==> 
  ∃c. ∀m. 
    np_kolmog (f m) <= 2 * (ℓ (m) + ℓ (THE (kolmog_fn2 f)) ) + c
Proof
  `∃k. ∀x y. ℓ (x ⊗ y) <= 2*(ℓ x + ℓ y) + k` by fs[ell_npair] >> 
  rw[] >> qexists_tac`k` >> rw[] >>
  `(∀n. Phi (recfn_index2 f) n = SOME (f n)) ∧
         ∀j. (∀n. Phi j n = SOME (f n)) ⇒ recfn_index2 f ≤ j` by fs[recfn_index2_def] >>
  `Phi (recfn_index2 f) m = SOME (f m)` by fs[] >>
  `Phi (nfst (npair (THE (kolmog_fn2 f)) m)) (nsnd (npair (THE (kolmog_fn2 f)) m)) = SOME (f m)` by fs[kolmog_fn2_def] >>
  `np_kolmog (f m) ≤ ℓ (npair (THE (kolmog_fn2 f)) m)` by fs[np_kolmog_smallest] >>
  `ℓ (npair (THE (kolmog_fn2 f)) m) <= 2 * (ℓ (THE (kolmog_fn2 f)) + ℓ (m)) + k` 
    suffices_by fs[] >> metis_tac[]
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

Theorem np_kolmog_ub:
  ∃c. ∀m. np_kolmog (m) <= 2 * (ℓ (m) ) + c
Proof
  `computable (λx. x)` by fs[computable_id] >> qabbrev_tac`f = (λx. (x:num))` >> 
  `∃c. ∀m. np_kolmog (f m) <= 2 * (ℓ (m) + ℓ (THE (kolmog_fn2 f)) ) + c` by 
    metis_tac[np_kolmog_fn_ub]  >> qexists_tac`c+2 * ℓ (THE (kolmog_fn2 f))` >> fs[Abbr`f`]>>
  rw[] >> `np_kolmog m ≤ c + 2 * (ℓ m + ℓ (THE (kolmog_fn2 (λx. x))))` by fs[] >> fs[]
QED

val npfkmin_def = Define`npfkmin m = MIN_SET {n | m<= np_kolmog n}`

Theorem MIN_SET_L_PHI_NPAIR_NON_EMPTY:
  {LENGTH p | Phi (nfst (bl2n p)) (nsnd (bl2n p)) = SOME y} <> {}
Proof
  fs[EXTENSION,Phi_bl2nx_npair]
QED

Theorem np_kolmog_props:
  ∀y. ∃z. np_kolmog y = ℓ z ∧ Phi (nfst z) (nsnd z) = SOME y
Proof
  simp[np_kolmog_thm] >> strip_tac >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw[]
  >- simp[MIN_SET_L_PHI_NPAIR_NON_EMPTY] >> qexists_tac ‘bl2n p’ >> simp[]
QED

Theorem np_kolmog_lb_exists:
  ∃x. m <= np_kolmog x
Proof
  CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
  `∀x. ∃i. Phi (nfst i) (nsnd i) = SOME x ∧ ℓ i < m` by metis_tac[np_kolmog_props] >>
  fs[SKOLEM_THM] >> 
  `FINITE (count m)` by fs[FINITE_COUNT] >>
  `INFINITE {f x | x | T}` by 
    (`SURJ (λx. Phi (nfst (f x)) (nsnd (f x))) UNIV {SOME n|T}` by 
       (fs[SURJ_DEF] >> rw[]) >> 
     `IMAGE (λx. Phi (nfst (f x)) (nsnd (f x))) UNIV = {SOME n|T}` by fs[IMAGE_SURJ]>>
     fs[IMAGE_DEF] >> 
     `{SOME n | T} = IMAGE (λx. Phi (nfst x) (nsnd x)) {f x | x | T}` by 
       (fs[IMAGE_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[] 
        >- (qexists_tac`f n` >> metis_tac[]) 
        >- (qexists_tac`x''` >> metis_tac[]) ) >> 
     `SURJ (λx. Phi (nfst x) (nsnd x)) {f x | x | T} {SOME n | T}` by fs[SURJ_IMAGE] >>
     `¬(FINITE {SOME (n:num) | T})` by 
       (`INFINITE 𝕌(:num option)` by 
          (fs[infinite_num_inj] >> qexists_tac`SOME` >> rw[INJ_DEF]) >> 
        `{SOME n | T} = 𝕌(:num option) DIFF {NONE}` by  
          (rw[EXTENSION] >> eq_tac >> rw[] >> Cases_on`x` >> fs[]) >> 
        `FINITE {NONE}` by fs[FINITE_SING] >> 
        rw[] >> fs[INFINITE_DIFF_down]) >> 
     `∃g. INJ g {SOME n | T} {f x | x | T} ∧ ∀y. y ∈ {SOME n | T} ⇒ (λx. Phi (nfst x) (nsnd x)) (g y) = y` by 
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

Theorem npkfkmin_lb:
  ∀m. m <= np_kolmog (npfkmin m)
Proof
  rw[npfkmin_def] >> irule f_min_set_f >> fs[np_kolmog_lb_exists]
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

(* Up to here *)
(* only theorem left to prove *)
Theorem computable_npfkmin:
  computable np_kolmog ==> computable npfkmin
Proof
  rw[] >> `unbounded np_kolmog` by metis_tac[unbounded_def,np_kolmog_lb_exists] >>
  simp[computable_def,npfkmin_def] >> fs[computable_arg_min_set]
QED

Theorem npkol_fkmin_lb:
  computable np_kolmog ==> 
  ∃c. ∀m. np_kolmog (npfkmin m) <= 2*((ℓ m) + ℓ (THE (kolmog_fn2 npfkmin))) + c
Proof
  rw[] >> `computable npfkmin` by fs[computable_npfkmin] >> 
  `∃c. ∀m. np_kolmog (npfkmin m) ≤ 2 * (ℓ m + ℓ (THE (kolmog_fn2 npfkmin))) + c` by 
    fs[np_kolmog_fn_ub] >> qexists_tac`c` >> rw[] >> fs[]
QED

Theorem npkolmog_length_ub_corrol:
  computable np_kolmog ==> ∃c. ∀m. np_kolmog (npfkmin m) <= 2*(ℓ m) + c
Proof
  rw[] >> 
  `∃c. ∀m. np_kolmog (npfkmin m) <= 2*((ℓ m) + ℓ (THE (kolmog_fn2 npfkmin))) + c` by 
    fs[npkol_fkmin_lb] >> qexists_tac` 2 * (ℓ (THE (kolmog_fn2 npfkmin))) + c` >> rw[] >> 
  fs[GSYM LEFT_ADD_DISTRIB]
QED


Theorem compkol_lb:
  computable np_kolmog ==> ∃c. ∀m. m <=  2*(ℓ m) + c
Proof
  rw[] >> `∃c. ∀m. np_kolmog (npfkmin m) <= 2*(ℓ m) + c` by fs[npkolmog_length_ub_corrol]>>
  `∀m. m <= np_kolmog (npfkmin m)` by fs[npkfkmin_lb]  >> qexists_tac`c` >> rw[] >>
  `m ≤ np_kolmog (npfkmin m)` by fs[] >> `np_kolmog (npfkmin m) ≤ c + 2 * ℓ m` by fs[] >>fs[]
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

Theorem part_hutter:
  computable np_kolmog ==> F
Proof
  strip_tac >> `∃c. ∀m. m <=  2*(ℓ m) + c` by  fs[compkol_lb] >>
  `∃m. ¬(m<= 2*(ℓ m) + c)` by fs[exists_log_lb] >> metis_tac[]
QED

(* up to here *)
(*
Theorem comp_univ_comp_npkolmog:
  univ_rf U ∧ (computable (λx. THE (kolmog_complexity x U) ) ) ==> computable np_kolmog 
Proof
  rw[] >> simp[computable_def,np_kolmog_def] >> fs[univ_rf_def,computable_def] >>

  `∃g. ∀x. Phi i x = U (g ++ n2bl x)` by fs[] >>
  `∀x. SOME (THE (kolmog_complexity x U)) = U (g ++ n2bl x)` by fs[] >>
  fs[kolmog_complexity_def] >> `univ_rf U` by fs[univ_rf_def] >> 
  Cases_on`∀x. {p | U p = SOME x} <> ∅` 
  >- (`SOME (MIN_SET {LENGTH p | U p = SOME x}) = U (g ++ n2bl x)` by fs[] >> 
      `∀n. {y | Phi (nfst (bl2n y)) (nsnd (bl2n y)) = SOME n} <> ∅` by 
        fs[EXTENSION,Phi_bl2nx_npair] >> qexists_tac`i` >> rw[]) 
  >- metis_tac[univ_rf_nonempty] 
QED

Theorem univ_comp_kol_incomp:
  univ_rf U ==> ¬(computable (λx. THE (kolmog_complexity x U) ) )
Proof

QED

*)

(*
(*  TODO next, show any kolmogorov complexity for a universal function is incomputable *)



Theorem incomp_all_kolmog:
  univ_rf U ==> ¬(computable (λx. THE (kolmog_complexity x U) ) )
Proof
  rw[] >> strip_tac >> 
QED

*)


(* not sure if needed anymore 
Theorem dBnum_fromTerm_church:
  dBnum (fromTerm (church y)) = 35
Proof
  Induct_on`y` >> 
  fs[churchnumTheory.church_def] >> 
  fs[churchDBTheory.fromTerm_funpow_app] >>
  fs[pure_dBTheory.dLAM_def] >>
  fs[enumerationsTheory.dBnum_def] >>
  fs[pure_dBTheory.lift_sub]
QED

Theorem prime_tm_npair:
  prime_tm x y = npair x y
Proof
  simp[prime_tm_def] >> 
  simp[enumerationsTheory.dBnum_def,pure_dBTheory.fromTerm_thm] >>
  simp[churchnumTheory.church_def] >> 
  simp[churchDBTheory.fromTerm_funpow_app] >> 
  pure_dBTheory.fromTerm_thm,pure_dBTheory.fromTerm_eqn
QED



Theorem kolmog_fn_ub:
  computable f ==> ∃c. ∀m. 
  plain_kolmog (f m) <= 2 * ((plain_kolmog m) + THE (kolmog_fn2 f)) + c
Proof
  rw[] >> qexists_tac`10` >> rw[] >>
  `(∀n. Phi (recfn_index2 f) n = SOME (f n)) ∧
         ∀j. (∀n. Phi j n = SOME (f n)) ⇒ recfn_index2 f ≤ j` by fs[recfn_index2_def] >>
  `Phi (recfn_index2 f) m = SOME (f m)` by fs[] >>
  `Phi (prime_tm (THE (kolmog_fn2 f)) m) 0 = SOME (f m)` by fs[kolmog_fn2_def,prime_tm_corr] >>
  `plain_kolmog (f m) ≤ ℓ (prime_tm (THE (kolmog_fn2 f)) m)` by fs[plain_kolmog_smallest] >>
  `ℓ (prime_tm (THE (kolmog_fn2 f)) m) <= 2 * (THE (kolmog_fn2 f) + plain_kolmog m) + 10` 
    suffices_by fs[] >> 
  
QED

Theorem kol_fkmin_lb:
  computable plain_kolmog ==> ∃c. ∀m. plain_kolmog (fkmin m) <= (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) + c
Proof
  rw[] >> qexists_tac`m` >> rw[] >> cheat
QED

Theorem kolmog_length_ub:
  ∃c. ∀m. plain_kolmog m <= (ℓ m) + c
Proof
  `∃i0. ∀x. Phi i0 x = SOME x` by stuff >> 
  `∀m. plain_kolmog m <= ℓ (prime_tm i0 m)` 
    by (rw[] >> `Phi (prime_tm i0 m) 0 = SOME m` by fs[prime_tm_corr] >> fs[plain_kolmog_smallest]) >>
  `∃k. ∀m. ℓ (prime_tm i0 m) <= LENGTH ((n2bl m) ++ (n2bl i0)) +k` 
    by (simp[prime_tm_def,pure_dBTheory.fromTerm_def,enumerationsTheory.dBnum_def] >> ) >>
  `∀m. LENGTH ((n2bl m) ++ (n2bl i0)) +k  <= (ℓ m) + ((ℓ i0) + k)` by (rw[]>>fs[LENGTH_APPEND]) >>
  qexists_tac`ℓ i0 + k` >> strip_tac >> metis_tac[LESS_EQ_TRANS]
QED

Theorem kolmog_length_ub_corrol:
  ∃c. ∀m. plain_kolmog m <= 2*(ℓ m) + c
Proof

QED

Theorem kol_fkmin_ub:
  computable plain_kolmog ==> ∃c. ∀m. (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) <= 2*(LENGTH (n2bl m)) + c 
Proof
  cheat
QED

Theorem compkol_lb:
  computable plain_kolmog ==> ∃c. ∀m. m <=  2*(LENGTH (n2bl m)) + c
Proof
  rw[] >> `∃c. ∀m. m <= (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) + c ` by 
            metis_tac[kfkmin_lb,kol_fkmin_lb,LESS_EQ_TRANS] >>
  `∃c. ∀m. (plain_kolmog m) + THE (kolmog_fn (λx. (SOME o fkmin) (HD x) )) <= 2*(LENGTH (n2bl m)) + c ` by metis_tac[kol_fkmin_ub] >> qexists_tac`c+c'` >> 
  `∀m. plain_kolmog m + THE (kolmog_fn (λx. (SOME ∘ fkmin) (HD x)))+c ≤
         2 * ℓ m + c'+c` by fs[] >>
  rw[] >> `plain_kolmog m + THE (kolmog_fn (λx. (SOME ∘ fkmin) (HD x))) + c ≤
             2 * ℓ m + c' + c` by fs[] >> 
  `m ≤ plain_kolmog m + THE (kolmog_fn (λx. (SOME ∘ fkmin) (HD x))) + c` by fs[] >> 
  fs[LESS_EQ_TRANS]
QED

Theorem exists_log_lb:
  ∃m. ¬(m<= 2*(LENGTH (n2bl m)) + c)
Proof
  cheat
QED

Theorem part_hutter:
  computable plain_kolmog ==> F
Proof
  strip_tac >> `∃c. ∀m. m <=  2*(LENGTH (n2bl m)) + c` by  fs[compkol_lb] >>
  `∃m. ¬(m<= 2*(LENGTH (n2bl m)) + c)` by fs[exists_log_lb] >> metis_tac[]
QED

*)


(* unproven *)

(* j-machine is passed an n.

   Then, for every string y of length 2n with complexity < 2n, then generate
   the list of triples (yi,Mi,ti), where yi is one of the ys, and
   Mi (0) = SOME yi, and that computation takes ti steps
*)

(*
Theorem part2:
  computable kolmog ==>
  ∃j. ∀n. ∃l. Phi j n = SOME (nlist_of l) ∧
              (∀e. MEM e l <=> ∃yi Mi ti. yMt_pred e n yi Mi ti)
Proof
     rw[computable_def] >> arg_plain_kolmog2_def]
QED
*)

(* unproven *)

(* Not needed *)

(*
val yMt_set_def = Define‘
  yMt_set n = {(yi,Mi,t) | ∃e. yMt_pred e n yi Mi t }
’;

val big_T_def = Define`big_T n = MAX_SET (IMAGE SND (IMAGE SND (yMt_set n)))`
*)
(*

For our argument, we basically need to show that big_T is computable,
Therefore using part3 and part4 we can run our computable TM (prime_tm M x) for a computable time
(big_T) and we will be able to determine whether or not (M,x) halted

Since max and nsnd are comptuable, we should be able to use part22 to show big_T is computable

prtermTheory.primrec_max,primrecfnsTheory.primrec_nsnd

*)

(* unproven *)



Theorem terminated_ge:
  (b < a) ==> (terminated (steps b cs) ==> terminated (steps a cs))
Proof
  rw[] >> `∃c. c>0 ∧  a = b+c` by (qexists_tac`a-b` >> fs[]) >> rw[] >>
  `step1 (steps b cs) = steps b cs` by fs[terminated_step_in_place] >>
  `terminated (steps (c + b) cs)` suffices_by fs[] >>
  simp[steps_def,FUNPOW_ADD] >>
  Induct_on`c` >> rw[] >> Cases_on`c` >> fs[]
  >- (fs[steps_def])
  >- (fs[FUNPOW,steps_def] >> metis_tac[])
QED

Theorem log_ub:
  1<a ∧ 0 < b ==> (LOG a b = m ==> b<a ** SUC m)
Proof
  rw[] >> fs[LOG]
QED

Theorem finite_logeq:
  1<a ==> FINITE {b | LOG a b = m}
Proof
  rw[] >> `{b | LOG a b = m} SUBSET {b | b<a ** SUC m}` by
             (fs[SUBSET_DEF] >> rw[]>> Cases_on`x` >> fs[LOG]) >>
  `FINITE {b | b < a ** SUC m}` by (`FINITE (count (a ** SUC m))`
     suffices_by metis_tac[count_def] >>
  fs[FINITE_COUNT] ) >> metis_tac[SUBSET_FINITE_I]
QED

Theorem finite_log2:
  FINITE {x | LOG 2 x = LOG 2 (SUC m)}
Proof
  qabbrev_tac`n = LOG 2 (SUC m) ` >> `(1:num)<2` by fs[] >> fs[finite_logeq]
QED

Theorem FUNPOW_id:
  f x = x ==> FUNPOW f n x = x
Proof
  rw[] >> Induct_on`n` >> fs[] >> rw[FUNPOW]
QED

Theorem terminated_imp:
  ¬terminated (steps (t-1) (mk_initial_state M x)) ∧
  terminated (steps t (mk_initial_state M x))
    ==>
  Phi M x = SOME (cs_to_num (steps t (mk_initial_state M x)))
Proof
  rw[] >> fs[Phi_steps] >> `comp_count (mk_initial_state M x) = SOME t`
    suffices_by fs[] >>
  fs[comp_count_def] >> fs[OLEAST_EQ_SOME] >> rw[] >> strip_tac >>
  `∃c.0<c ∧ n+c = t` by (qexists_tac`t-n` >> fs[]) >> rw[] >>
  ‘steps (n + c) (mk_initial_state M x) =
   steps (n + c - 1) (mk_initial_state M x)’
  by (
   `step1 (steps n (mk_initial_state M x)) = (steps n (mk_initial_state M x))`
     by fs[terminated_step_in_place] >> fs[steps_def] >>
   `FUNPOW step1 (c + n) (mk_initial_state M x) =
      FUNPOW step1 ((c-1) + n) (mk_initial_state M x)`
   suffices_by fs[] >>fs[FUNPOW_ADD] >>
   fs[FUNPOW_id]
  ) >> metis_tac[]
QED

Theorem terminated_down:
  (¬(terminated (steps 0 (mk_initial_state M x)) ) ∧ terminated (steps t (mk_initial_state M x)))
    ==> ∃tl. tl<t ∧ ¬terminated (steps tl (mk_initial_state M x)) ∧  terminated (steps (tl+1) (mk_initial_state M x))
Proof
  rw[] >> Induct_on`t` >> fs[] >>
  rw[] >> Cases_on` terminated (steps t (mk_initial_state M x))` >>  fs[]
  >- (qexists_tac`tl` >> fs[])
  >- (qexists_tac`t` >> fs[ADD1])
QED

Theorem terminated_impdown:
  (¬(terminated (steps 0 (mk_initial_state M x)) ) ∧ terminated (steps t (mk_initial_state M x)))
    ==> ∃tl. Phi M x = SOME (cs_to_num (steps tl (mk_initial_state M x) ))
Proof
  rw[] >> `∃tll. tll<t ∧ ¬terminated (steps tll (mk_initial_state M x)) ∧
                 terminated (steps (tll+1) (mk_initial_state M x))` by
            metis_tac[terminated_down] >> qabbrev_tac`tk = tll+1` >>
  `tk-1 = tll` by fs[Abbr`tk`] >> rw[] >>
  `Phi M x = SOME (cs_to_num (steps (tk) (mk_initial_state M x) ))` by
    metis_tac[terminated_imp]>> qexists_tac`tk` >> fs[]
QED

Theorem correctness_on_nontermination_contrapos:
 (∃x. Phi i n = SOME x) ==> ∃y. comp_count (mk_initial_state i n) = SOME y
Proof
  metis_tac[correctness_on_nontermination,optionTheory.option_CLAUSES]
QED

Theorem correctness_on_termination_contrapos:
 ( Phi i n = NONE) ==> comp_count (mk_initial_state i n) = NONE
Proof
  metis_tac[correctness_on_termination,optionTheory.option_CLAUSES]
QED

Theorem prime_tm_mk_comp_initial_state_NONE:
  comp_count (mk_initial_state (prime_tm M x) 0) = NONE <=> 
  comp_count (mk_initial_state M x) = NONE
Proof
  eq_tac >> rw[]
  >- (`Phi (prime_tm M x) 0 = NONE` by fs[correctness_on_nontermination] >>
      `Phi M x = NONE` by fs[prime_tm_corr] >>
      fs[correctness_on_termination_contrapos])
  >- (`Phi M x = NONE` by fs[correctness_on_nontermination] >>
      `Phi (prime_tm M x) 0 = NONE` by fs[prime_tm_corr] >>
      fs[correctness_on_termination_contrapos])
QED

Theorem prime_tm_mk_comp_initial_state_SOME:
  (∃t1. comp_count (mk_initial_state (prime_tm M x) 0) = SOME t1) <=> 
  (∃t2. comp_count (mk_initial_state M x) = SOME t2)
Proof
  eq_tac >> rw[]
  >- (`terminated (steps t1 (mk_initial_state (prime_tm M x) 0)) ∧ 
       Phi (prime_tm M x) 0 = SOME (cs_to_num (steps t1 (mk_initial_state (prime_tm M x) 0)))` by 
        metis_tac[correctness_on_termination] >>
      `Phi M x = SOME (cs_to_num (steps t1 (mk_initial_state (prime_tm M x) 0)))` by 
        fs[prime_tm_corr] >> 
      fs[correctness_on_nontermination_contrapos])
  >- (`terminated (steps t2 (mk_initial_state M x)) ∧ 
       Phi M x = SOME (cs_to_num (steps t2 (mk_initial_state M x)))` by 
         metis_tac[correctness_on_termination] >>
      `Phi (prime_tm M x) 0 = SOME (cs_to_num (steps t2 (mk_initial_state M x)))` by 
        fs[prime_tm_corr] >> 
      fs[correctness_on_nontermination_contrapos])  
QED

Theorem prime_tm_termination:
  (∃t1. terminated (steps t1 (mk_initial_state (prime_tm M x) 0))) <=>
  (∃t2. terminated (steps t2 (mk_initial_state M x)))
Proof
  `(∃t1. comp_count (mk_initial_state (prime_tm M x) 0) = SOME t1) <=> 
  (∃t2. comp_count (mk_initial_state M x) = SOME t2)` by fs[prime_tm_mk_comp_initial_state_SOME] >>
  fs[comp_count_def,OLEAST_def]
QED


Theorem terminated_le:
  (b <= a) ==> (terminated (steps b cs) ==> terminated (steps a cs))
Proof
  rw[] >> Cases_on`a=b` >> fs[] >> `b<a` by fs[] >> metis_tac[terminated_ge]
QED


Theorem ELL_FINITE:
  FINITE {m | ℓ m = k}
Proof
  simp[ELL_log2list] >> irule SUBSET_FINITE_I >>
  qexists_tac`IMAGE PRE (set (log2list k))` >> simp[SUBSET_DEF] >> rw[] >> qexists_tac`x+1`>>fs[]
QED

Theorem ELL_terminated_FINITE:
  FINITE {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧ 
                  ¬terminated (steps (t − 1) (mk_initial_state m 0))) ∧ ℓ m = k}
Proof
  fs[finite_and,ELL_FINITE]
QED

Theorem non_terminated_down:
  (¬terminated (steps t (mk_initial_state m x))) ==> 
  (∀a. a<=t ==>  (¬terminated (steps a (mk_initial_state m x))))
Proof
  rw[] >> strip_tac >> metis_tac[terminated_le]
QED

Theorem comp_count_terminated:
  (terminated (steps x (mk_initial_state m y)) ∧ 
  ¬terminated (steps (x − 1) (mk_initial_state m y))) ==> 
  THE (comp_count (mk_initial_state m y)) = x
Proof
  rw[] >> `Phi m y = SOME (cs_to_num (steps x (mk_initial_state m y)))` by fs[terminated_imp]>>
  fs[Phi_steps] >> Cases_on`comp_count (mk_initial_state m y)` >> fs[] >> 
  `(∀a. a<=x-1 ==> (¬terminated (steps a (mk_initial_state m y))))` by 
    metis_tac[non_terminated_down] >>  fs[comp_count_def,OLEAST_def] >> rw[]>>
  numLib.LEAST_ELIM_TAC >> rw[] >- metis_tac[] >>
  `(∀a. a<x ==> (¬terminated (steps a (mk_initial_state m y))))` by fs[] >>
  metis_tac[DECIDE``x:num < y ∨ x=y ∨ y<x ``]
QED

Theorem ELL_SURJ_terminate:
  SURJ (λm. THE (comp_count (mk_initial_state m 0))) 
  {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧ 
                  ¬terminated (steps (t − 1) (mk_initial_state m 0))) ∧ ℓ m = k}  
  {t |(∃m.  terminated (steps t (mk_initial_state m 0)) ∧
           ¬terminated (steps (t − 1) (mk_initial_state m 0)) ∧
           ℓ m = k)}
Proof
  fs[SURJ_DEF] >> rw[] >> qexists_tac`m`
  >- (metis_tac[comp_count_terminated])
  >- (rw[] >- (qexists_tac`x` >> fs[comp_count_terminated]) 
      >- (fs[comp_count_terminated] ) )
QED

Theorem terminated_imp2:
 ((∀t'. terminated (steps t' (mk_initial_state M x)) ⇒ t ≤ t') ∧
     terminated (steps t (mk_initial_state M x))) ⇒
     Phi M x = SOME (cs_to_num (steps t (mk_initial_state M x)))
Proof
  rw[] >> Cases_on`t=0` 
  >- ( fs[Phi_steps] >> `comp_count (mk_initial_state M x) = SOME t`
      suffices_by fs[] >>
      fs[comp_count_def] >> fs[OLEAST_EQ_SOME] >> rw[] >> strip_tac  ) >>
  `¬terminated (steps (t − 1) (mk_initial_state M x))` by 
    (strip_tac >> fs[] >> `t<=t-1` by fs[] >> fs[PRE_SUB1])  >>
  fs[terminated_imp]
QED

Theorem comp_count_terminated2:
  (terminated (steps t (mk_initial_state m y)) ∧
  (∀t'. terminated (steps t' (mk_initial_state m y)) ⇒ t ≤ t')) ==>
  THE (comp_count (mk_initial_state m y)) = t
Proof
  rw[] >> Cases_on`t=0`
  >- (`Phi m y = SOME (cs_to_num (steps t (mk_initial_state m y)))` by fs[terminated_imp2]>>
      `comp_count (mk_initial_state m y) = SOME t` suffices_by fs[] >>
      fs[comp_count_def] >> fs[OLEAST_EQ_SOME] >> rw[] >> strip_tac  ) >> 
  `¬terminated (steps (t − 1) (mk_initial_state m y))` by 
    (strip_tac >> fs[] >> `t<=t-1` by fs[] >> fs[])  >> fs[comp_count_terminated]
QED


Theorem ELL_terminated_FINITE2:
  FINITE {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧ 
               (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ) ∧ ℓ m = k} 
Proof
  fs[finite_and,ELL_FINITE]
QED

Theorem ELL_SURJ_terminate2:
  SURJ (λm. THE (comp_count (mk_initial_state m 0))) 
  {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧ 
                 (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ) ∧ ℓ m = k}  
  {t |(∃m. terminated (steps t (mk_initial_state m 0)) ∧
           (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ∧
           ℓ m = k)}
Proof
  fs[SURJ_DEF] >> rw[] >> qexists_tac`m`
  >- (metis_tac[comp_count_terminated2])
  >- (rw[] >- (qexists_tac`x` >> fs[comp_count_terminated2]) 
      >- (fs[comp_count_terminated2] ) )
QED


Theorem terminated_tmax:
  (∃t. terminated (steps t (mk_initial_state (prime_tm M x) 0))) ==>
  terminated (steps (tmax (ℓ (prime_tm M x))) (mk_initial_state (prime_tm M x) 0))
Proof
  rw[] >> Cases_on`terminated (steps 0 (mk_initial_state (prime_tm M x) 0))`
  >- (Cases_on`0<tmax (ℓ (prime_tm M x))` >>fs[]>> metis_tac[terminated_ge]) >> 
  `∃tl. tl < t ∧ ¬terminated (steps tl (mk_initial_state (prime_tm M x) 0)) ∧
        terminated (steps (tl + 1) (mk_initial_state (prime_tm M x) 0))` by 
    fs[terminated_down] >> 
  rw[tmax_def]>> qabbrev_tac`s = {t |
            (∃m.
                 terminated (steps t (mk_initial_state m 0)) ∧
                 (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t') ∧
                 ℓ m = ℓ (prime_tm M x))}` >>
  `s <> {}` by 
    (fs[Abbr`s`,EXTENSION] >> qexists_tac`tl+1` >> qexists_tac`prime_tm M x` >> rw[] >>
     `∀a. a ≤ tl ⇒ ¬terminated (steps a (mk_initial_state (prime_tm M x) 0))` by 
       metis_tac[non_terminated_down] >> Cases_on`tl + 1 ≤ t'` >> rw[] ) >>
  `(tl+1) ∈ s` by (fs[Abbr`s`,IN_DEF] >> qexists_tac`prime_tm M x` >> rw[] >> 
                   Cases_on`tl + 1 ≤ t'` >> fs[] >> `t'<=tl` by fs[]>> metis_tac[non_terminated_down])>>
  `FINITE s` by (fs[Abbr`s`] >> 
                 metis_tac[ELL_SURJ_terminate2,FINITE_SURJ,ELL_terminated_FINITE2]) >> 
  `tl+1<=MAX_SET s` by metis_tac[in_max_set] >>metis_tac[terminated_le]
QED



Theorem part4:
  tmax (ℓ (prime_tm M x) ) < n ⇒
  (terminated (steps n
                     (mk_initial_state (prime_tm M x) 0 ))
      <=>
   (M,x) ∈ HALT)
Proof
  rw[] >> eq_tac >> rw[HALT_def]
  >- (metis_tac[prime_tm_termination])
  >- (`terminated (steps (tmax (ℓ (prime_tm M x))) (mk_initial_state (prime_tm M x) 0))` 
        suffices_by (metis_tac[terminated_ge]) >>
      `∃t1. terminated (steps t1 (mk_initial_state (prime_tm M x) 0))` by 
        metis_tac[prime_tm_termination] >> 
      metis_tac[terminated_tmax])
QED

(*

Theorem Phi_halt:
  Phi (THE (Phi i x)) y = Phi i y ==> 
Proof

QED

Theorem partall:
  (computable plain_kolmog ∧ computable arg_plain_kolmog) ==> F
Proof
  strip_tac >> fs[computable_def] >>
  `Phi i 0 = SOME (plain_kolmog 0)` by fs[] >>
  `Phi i' 0 = SOME (arg_plain_kolmog 0)`by fs[] >>
  `Phi (arg_plain_kolmog ((plain_kolmog 0))) 0 = SOME (plain_kolmog 0)` by fs[] >> 
  `Phi (arg_plain_kolmog (plain_kolmog 0)) 0  = Phi i 0` by fs[] >> 
  
  `Phi (arg_plain_kolmog (arg_plain_kolmog 0)) 0 = SOME (arg_plain_kolmog 0)` by fs[]>>
  `Phi (arg_plain_kolmog (arg_plain_kolmog 0)) 0 = Phi i' 0` by fs[] >>

  `Phi i' (arg_plain_kolmog 0) = SOME (arg_plain_kolmog (arg_plain_kolmog 0))` by fs[] >>

  `Phi (THE (Phi i' (arg_plain_kolmog 0))) 0 = Phi i' 0` by metis_tac[optionTheory.THE_DEF]>>
  
  pop_assum (K ALL_TAC) >> simp[plain_kolmog_def,kolmog_complexity_def]
QED



val newymt_def = Define`newymt e n yi Mi ti ⇔
         plain_kolmog yi <= 2 * n ∧ 
         terminated (steps ti (mk_initial_state Mi 0)) ∧
         cs_to_num (steps ti (mk_initial_state Mi 0)) = yi ∧
         (∀t'. terminated (steps t' (mk_initial_state Mi 0)) ⇒ ti ≤ t') ∧
         e = yi ⊗ Mi ⊗ ti`

val newymt_set_def = Define‘
  newymt_set n = {(yi,Mi,t) | ∃e. newymt e n yi Mi t }
’;

val newbig_T_def = Define`newbig_T n = MAX_SET (IMAGE SND (IMAGE SND (newymt_set n)))`

Theorem plain_kolmog_ub:
  comp_count (mk_initial_state m 0) = SOME t ==> plain_kolmog
     (cs_to_num
        (steps (THE (comp_count (mk_initial_state m 0)))
           (mk_initial_state m 0))) <= ℓ m
Proof
  rw[] >> fs[plain_kolmog_def,kolmog_complexity_def] >> rw[Phi_bl2nx_0] 
  >- (`∃x. Phi (bl2n x) 0 = SOME (cs_to_num
          (steps t
             (mk_initial_state m 0)))` by fs[Phi_bl2nx_0] >> fs[EXTENSION] >> metis_tac[])>>
  qabbrev_tac`s = {LENGTH y | Phi (bl2n y) 0 = SOME (cs_to_num
           (steps t
              (mk_initial_state m 0)))}` >> `s<> {}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0]>>
  `∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >>
  `ℓ m ∈ s` suffices_by fs[] >> 
  `(n2bl m) ∈ {y | Phi (bl2n y) 0 =SOME
            (cs_to_num
               (steps t
                  (mk_initial_state m 0)))}` by 
         fs[IN_DEF,Phi_steps] >>  
       `LENGTH (n2bl m) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl m` >> fs[]) 
QED



Theorem newymt_SURJ:
  SURJ 
  (λm. (cs_to_num (steps (THE (comp_count (mk_initial_state m 0))) (mk_initial_state m 0)),
        m,
        THE (comp_count (mk_initial_state m 0)) ) ) 
  {m | (∃t. terminated (steps t (mk_initial_state m 0)) ∧ 
           (∀t'. terminated (steps t' (mk_initial_state m 0)) ⇒ t ≤ t')) ∧ ℓ m <= 2 * n}   
  (newymt_set n)
Proof
  fs[SURJ_DEF] >> rw[]
  >- (fs[IN_DEF,newymt_set_def,newymt_def] >> 
      qexists_tac`(cs_to_num (steps (THE (comp_count (mk_initial_state m 0)))
                                    (mk_initial_state m 0)),
                   m,
                   THE (comp_count (mk_initial_state m 0)))` >> simp[] >>rw[]
      >- (`THE (comp_count (mk_initial_state m 0))=t` by fs[comp_count_terminated2] >>
          `plain_kolmog (cs_to_num (steps (THE (comp_count (mk_initial_state m 0))) 
            (mk_initial_state m 0))) <= ℓ m` suffices_by (fs[]) >> 
          irule plain_kolmog_ub >> irule correctness_on_nontermination_contrapos >> 
          qexists_tac`cs_to_num (steps t (mk_initial_state m 0))` >> fs[terminated_imp2] ) 
      >- (simp[comp_count_def,OLEAST_def] >> rw[] >> fs[] >> numLib.LEAST_ELIM_TAC >>
          rw[] >> qexists_tac`t` >> fs[] ) 
      >- (`THE (comp_count (mk_initial_state m 0))=t` by fs[comp_count_terminated2] >> 
          `t<= t'` suffices_by fs[] >>  fs[] ) ) >>
  qexists_tac`FST (SND x)` >> rw[]
  >- (qexists_tac`SND (SND x)` >> rw[] >> fs[newymt_set_def,newymt_def] >> 
      `FST (SND x) = Mi` by fs[] >> fs[] )
  >- (fs[newymt_set_def,newymt_def] >> 
      `THE (comp_count (mk_initial_state Mi 0))=t` by fs[comp_count_terminated2] >> 
          irule plain_kolmog_ub       fs[plain_kolmog_ub])
  >- (fs[newymt_set_def,newymt_def] >> rw[comp_count_terminated2] >> 
      `THE (comp_count (mk_initial_state Mi 0)) = t` by fs[comp_count_terminated2] >> fs[])
QED

Theorem FINITE_newymt_set:
  FINITE (newymt_set n)
Proof
  fs[newymt_set_def,newymt_def]
QED

Theorem newpart3plus:
  tmax (ℓ (prime_tm M x) ) <= newbig_T (prime_tm M x)
Proof
  rw[] >> fs[tmax_def,newbig_T_def] >> irule SUBSET_MAX_SET >>
  rw[] >- metis_tac[ELL_SURJ_terminate,FINITE_SURJ,ELL_terminated_FINITE] 
  >- metis_tac[FINITE_newymt_set,IMAGE_FINITE] >> fs[SUBSET_DEF] >> rw[] >>
  simp[newymt_set_def,newymt_def] >> 
  qexists_tac`(m,x')` >> rw[] >> 
  qexists_tac`(cs_to_num (steps x' (mk_initial_state m 0)),m,x')` >> rw[]
  >- (fs[plain_kolmog_def,kolmog_complexity_def] >>
      `{y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))} <> ∅` by 
        fs[EXTENSION,Phi_bl2nx_0] >> fs[] >> 
       `x' = THE (comp_count (mk_initial_state m 0)) ` by metis_tac[comp_count_terminated]>>
       `Phi m 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))` by 
         (fs[Phi_steps] >> Cases_on`comp_count (mk_initial_state m 0)` >> fs[comp_count_def])>>
       `ℓ m <= 2 * prime_tm M x` by 
         (`ℓ m <= (prime_tm M x)` by fs[ELL_LE] >> `prime_tm M x <= 2 * (prime_tm M x)` by fs[]>>
          fs[]) >> 
       qabbrev_tac`s={LENGTH y |
       Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` >> 
       `MIN_SET s <= ℓ m` suffices_by fs[] >> 
       `s<>{}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0] >> 
       `∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >> `ℓ m∈s` suffices_by fs[] >>
       `(n2bl m) ∈ {y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` by 
         fs[IN_DEF] >>  
       `LENGTH (n2bl m) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl m` >> fs[])    )
  >- (`∀a. a ≤ (x'-1) ⇒ ¬terminated (steps a (mk_initial_state m 0))` by 
        metis_tac[non_terminated_down] >> Cases_on`x'<=t'` >> fs[])
QED


Theorem FINITE_yMt_set:
  FINITE (yMt_set n)
Proof
  cheat (*  fs[newymt_set_def,newymt_def]  *)
QED

Theorem arg_kolmog_size_genlist:
  LENGTH (n2bl (arg_plain_kolmog (bl2n (GENLIST (λn. T) n) ))) < n
Proof
  cheat (*  fs[arg_plain_kolmog] *)
QED




val Z_lam2_def = Define‘
  Z_lam2 M =
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

Theorem Z_lam_size:
  ℓ (Z_lam M n x) = 2 * n
Proof

QED

Theorem Z_lam_machine_size:
  
Proof

QED

Theorem oldpart3plus:
  tmax (ℓ (prime_tm M x) ) <= big_T (ℓ (prime_tm M x))
Proof
  rw[] >> fs[tmax_def,big_T_def] >> irule in_max_set >>
  rw[] 
  >- metis_tac[FINITE_yMt_set,IMAGE_FINITE] >> fs[IN_DEF] >> rw[] >>
  simp[yMt_set_def,yMt_pred_def] >> 
  qexists_tac`(m1,t1)` >> rw[] >- () >> qexists_tac`(y1,m1,t1)` >> rw[] >>qexists_tac`(y1,m1,t1)` >> rw[] >>


  qexists_tac`(arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) ),
               THE (comp_count (mk_initial_state (arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) )) 0)))` >> rw[] >- (rw[]) >> 
  qexists_tac`(bl2n (GENLIST (λn. T) (2*prime_tm M x)),arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) ),
               THE (comp_count (mk_initial_state (arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) )) 0)))` >> rw[] >> qexists_tac`(bl2n (GENLIST (λn. T) (2*prime_tm M x)),arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) ),
               THE (comp_count (mk_initial_state (arg_plain_kolmog (bl2n (GENLIST (λn. T) (2*prime_tm M x)) )) 0)))` >> rw[]
  >- ()
  >- ()
  >- ()
  >- ()
  >- ()


  >- (fs[plain_kolmog_def,kolmog_complexity_def] >>
      `{y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))} <> ∅` by 
        fs[EXTENSION,Phi_bl2nx_0] >> fs[] >> 
       `x' = THE (comp_count (mk_initial_state m 0)) ` by metis_tac[comp_count_terminated]>>
       `Phi m 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))` by 
         (fs[Phi_steps] >> Cases_on`comp_count (mk_initial_state m 0)` >> fs[comp_count_def])>>
       `ℓ m <= 2 * prime_tm M x` by 
         (`ℓ m <= (prime_tm M x)` by fs[ELL_LE] >> `prime_tm M x <= 2 * (prime_tm M x)` by fs[]>>
          fs[]) >> 
       qabbrev_tac`s={LENGTH y |
       Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` >> 
       `MIN_SET s <= ℓ m` suffices_by fs[] >> 
       `s<>{}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0] >> 
       `∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >> `ℓ m∈s` suffices_by fs[] >>
       `(n2bl m) ∈ {y | Phi (bl2n y) 0 = SOME (cs_to_num (steps x' (mk_initial_state m 0)))}` by 
         fs[IN_DEF] >>  
       `LENGTH (n2bl m) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl m` >> fs[])    )
  >- (`∀a. a ≤ (x'-1) ⇒ ¬terminated (steps a (mk_initial_state m 0))` by 
        metis_tac[non_terminated_down] >> Cases_on`x'<=t'` >> fs[])
QED

*)


(* OLD PART 3
Theorem part3:
  computable plain_kolmog ∧ ((Z_lam (prime_tm M x) (ℓ (prime_tm M x)) (0:num)) = SOME y)  ==>
  tmax (ℓ (prime_tm M x) ) < big_T (prime_tm M x)
Proof
  rw[] >> 
  `∃z. Phi z = Z_lam (prime_tm M x) (ℓ (prime_tm M x)) ∧ ℓ z < 2 * (ℓ (prime_tm M x))` by 
    fs[Z_lam_computable_size] >> 
  Cases_on`tmax (ℓ (prime_tm M x)) < big_T (prime_tm M x)` >> fs[] >> 
  `plain_kolmog y = (2*(ℓ (prime_tm M x)))` by metis_tac[Z_lam_output_size] >> 
  fs[plain_kolmog_def,kolmog_complexity_def] >> 
  `{y' | Phi (bl2n y') 0 = SOME y} <> ∅` by fs[EXTENSION,Phi_bl2nx_0] >> 
  fs[] >> 
  `ℓ z < MIN_SET {LENGTH y' | Phi (bl2n y') 0 = SOME y}` by fs[] >>
  qabbrev_tac`s={LENGTH y' | Phi (bl2n y') 0 = SOME y}` >>
  `s<>{}` by fs[Abbr`s`,EXTENSION,Phi_bl2nx_0] >> 
  `MIN_SET s ∈ s ∧ ∀x. x ∈ s ⇒ MIN_SET s ≤ x` by fs[MIN_SET_LEM] >>
  `(n2bl z) ∈ {y' | Phi (bl2n y') 0 = SOME y}` by fs[IN_DEF] >>  
  `LENGTH (n2bl z) ∈ s` by (fs[Abbr`s`,IMAGE_IN] >> qexists_tac`n2bl z` >> fs[])>>
  `MIN_SET s <= ℓ z` by fs[] >> fs[]
QED
*)


(*
Theorem big_T_Tmax_imp:
  (Big_T (LOG 2 (prime_tm M x) ) > tmax (LOG 2 (prime_tm M x) )) ==>
   ( terminated (steps (big_T  (LOG 2 (prime_tm M x))) (mk_initial_state (prime_tm M x) 0 ))  <=> ((M,x)∈HALT ))
Proof
  rw[] >> eq_tac >> rw[]
  >- (fs[HALT_def] >> qexists_tac`big_T (LOG 2 (prime_tm M x))` >>
      `∃m. comp_count  (mk_initial_state (prime_tm M x) 0) = SOME m` by
        (fs[comp_count_def]>>
         `¬((OLEAST n. terminated (steps n (mk_initial_state (prime_tm M x) 0))) = NONE)` by
           (fs[OLEAST_EQ_NONE] >> qexists_tac` (big_T (LOG 2 (prime_tm M x)))` >> fs[]) >>
        qexists_tac`THE (OLEAST n. terminated (steps n (mk_initial_state (prime_tm M x) 0)))`>>
        `IS_SOME  (OLEAST n. terminated (steps n (mk_initial_state (prime_tm M x) 0)))`
          suffices_by fs[quantHeuristicsTheory.SOME_THE_EQ ]  >>
        fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
        qexists_tac`n` >> fs[]) >>
      `terminated (steps m (mk_initial_state (prime_tm M x) 0)) ∧ Phi (prime_tm M x) 0 =
       SOME (cs_to_num (steps m (mk_initial_state (prime_tm M x) 0)))` by
        (fs[correctness_on_termination] >> fs[comp_count_def,OLEAST_EQ_SOME]) >>
      fs[prime_tm_corr] >>
      `tmax (LOG 2 (prime_tm M x)) = m` by (fs[tmax_def] >> fs[comp_count_def])

       `terminated (steps (tmax (LOG (prime_tm M x) 2)) (mk_initial_state M x))` suffices_by
         metis_tac[terminated_ge] >>  )
  >- (fs[HALT_def] >> Cases_on`terminated (steps 0 (mk_initial_state M x))`
      >- (fs[])
      `terminated (steps (tmax (LOG 2 (prime_tm M x)))
       (mk_initial_state (prime_tm M x) 0))` suffices_by metis_tac[terminated_ge] >>
      fs[tmax_def] >> qmatch_abbrev_tac`terminated (steps (MAX_SET ts)
                                        (mk_initial_state (prime_tm M x) 0))` >>
      `FINITE ts` by (cheat) >>
      `ts <> {}` by (cheat) >>
      `MAX_SET ts ∈ ts ∧ ∀y. y ∈ ts ⇒ y ≤ MAX_SET ts` by fs[MAX_SET_DEF] >>  )
  fs[big_T_def] >> fs[tmax_def],yMt_set_def,IMAGE_DEF] >>  >>
  comp_count_def,correctness_on_termination
QED

*)

(*
val find_m_of_size_n_gen_y_def = Define`find_m_of_size_n_gen_y = LAM "n" (LAM "y"
  (dt @@ (ceqnat @@ VAR "y")
      @@ (cmap @@ (C @@ cpair @@ cnil)
               @@ (ctabulate ) )) )`

Theorem kol_dove:
  (∀x. Phi f x = SOME (kolmog x)) ==>
Proof

QED

val _ = Q.store_thm("_",
`∀n. n>const1 ==> ∃Z. tm_size Z <2*n ∧ `,
)

val _ Q.store_thm("_",
`¬∃f. ∀x. kolmog x = recPhi [f;x] ==> ∀y. LENGTH y = l ==> kolmog y`,
)



Theorem ub_tmax: big_T n > tmax n
Proof
  fs[big_T_def,tmax_def]
QED

val ub_implies_halt = Q.store_thm("ub_implies_halt",
`big_T > t_max (tm_size M') ==> (M',[]) ∈ HALT`,
)

val m_prime_implies_halt = Q.store_thm("m_prime_implies_halt",
`(primt_tm M,[]) ∈ HALT ==> (M,x)∈HALT`,
)

(* maybe want arg kolmog *)

val kolmog_non_comp = Q.store_thm("kolmog_non_comp",
`¬∃f. ∀x. kolmog x = recPhi [f;x]`,
strip_tac >> )



(* Not sure if needed  *)

(*

val pr_log2_pr = Q.store_thm("pr_log2_pr",
`primrec (pr_log2) 1`,
simp[pr_log2_def] >> irule primrec_WFM >> irule primrec_pr2 >> simp[restr_def]>>
qexists_tac`` )

val pr_nbar = Q.store_thm("pr_nbar",
`nbar n = n* 2**(pr_log2 [n] +1)+ (3*2**(pr_log2 [n])) - 1 `,
Induct_on`n` >> simp[nbar_def])

val recfn_nbar = Q.store_thm("recfn_nbar",
`recfn (rec1 (SOME o nbar)) 1`,
irule recfn_rec1 >> qexists_tac`SOME o (λl. nbar (HD l))` >> rw[] >> irule primrec_recfn >>
)



val leastR_def = Define`leastR R A = @a. a IN A /\ !b. b IN A ==> ~R b a`

val order_def = tDefine"order"`(order A R 0 = leastR R A) /\
                (order A R (SUC n) = leastR R (A DIFF IMAGE (\i. order A R i) (count (SUC n))))`(WF_REL_TAC`measure (SND o SND)` >> simp[])

val tmorder_def = Define`tmorder x = order {p | universal_tm p = x} `

val listlex_def = Define`(listlex [] x <=> x<>[])/\(listlex (h::t) [] <=> F)/\
                         (listlex (h1::t1) (h2::t2) <=>
                         (LENGTH t1 < LENGTH t2) \/ ((LENGTH t1 = LENGTH t2) /\ ((h1=h2) /\ listlex t1 t2 \/ ~h1 /\ h2 )  ) )`

val listlex_length = Q.store_thm("listlex_length",
`!a b. LENGTH a < LENGTH b ==> listlex a b`,
Cases_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def])

val listlex_length2 = Q.store_thm("listlex_length2",
`!a b. listlex a b ==> (LENGTH a <= LENGTH b)`,
Induct_on `a` >> simp[listlex_def] >> Cases_on `b` >> simp[listlex_def] >> rpt strip_tac >>
simp[])

val listlex_empty = Q.store_thm("listlex_empty[simp]",
`listlex a [] <=> F`,
Cases_on `a` >> simp[listlex_def])

val listlex_same_length = Q.store_thm("listlex_same_length",
`!B l w. (!b. B b ==> (LENGTH b = l)) /\ B w ==> ?v. B v /\ (!b. listlex b v ==> ~B b)`,
Induct_on `l` >> simp[] >- (rw[] >> qexists_tac`[]` >> simp[] >> metis_tac[]) >>
rw[] >> Cases_on`?hf. B' hf /\ (HD hf = F)`
>- (fs[] >>
    `?c. B' c /\ (HD c= F) /\ (!d. listlex d c ==> ~B' d)`
      by (first_x_assum(qspec_then`{t|B' (F::t)}`MP_TAC) >> simp[] >>
          disch_then(qspec_then`TL hf`MP_TAC) >> Cases_on `hf` >> simp[]
          >- (res_tac >> fs[]) >> fs[] >> impl_tac
              >- (rw[] >> res_tac>> fs[]) >>
              rw[] >> qexists_tac`F::v` >> simp[]>> rpt strip_tac >> Cases_on`d` >> fs[]
              >- (res_tac >> fs[])
              >- (fs[listlex_def] >- (res_tac >> fs[]) >> rw[] >> metis_tac[] ))>> metis_tac[])
>- (fs[] >>first_x_assum(qspec_then`{t|B' (T::t)}`MP_TAC) >> simp[] >> Cases_on `w`
    >- (res_tac >> fs[]) >> `h = T` by metis_tac[HD] >> rw[] >>
        pop_assum(qspec_then`t`MP_TAC) >> impl_tac
        >- (rw[] >> res_tac >> fs[]) >> rw[] >> qexists_tac`T::v` >> fs[] >> Cases_on `b`
            >- (rpt strip_tac >> res_tac >> fs[]) >> rw[listlex_def] >> strip_tac
                >- (res_tac >> fs[])
                >- (metis_tac[])
                >- (metis_tac[HD]) ) )

val WF_listlex = Q.store_thm("WF_listlex",`WF listlex`,
simp[relationTheory.WF_DEF] >> rw[] >>
`?v. B' v /\ !v'. B' v' ==> LENGTH v <= LENGTH v'`
  by (`WF (inv_image $< (LENGTH:bool list -> num) )` by (simp[relationTheory.WF_inv_image])>>
  fs[relationTheory.WF_DEF] >> metis_tac[NOT_LESS])>>
  qspecl_then[`{l|B' l /\ (LENGTH l = LENGTH v)}`,`LENGTH v`,`v`] MP_TAC listlex_same_length >>
  rw[] >> qexists_tac`v'` >> rw[] >> strip_tac >> `LENGTH b <> LENGTH v` by metis_tac[] >>
  `LENGTH v' < LENGTH b` by metis_tac[LESS_OR_EQ] >>
  `listlex v' b` by metis_tac[listlex_length] >>
  metis_tac[LESS_EQUAL_ANTISYM,listlex_length2,prim_recTheory.LESS_REFL] )

val num_to_bool_list_def = tDefine"num_to_bool_list"`num_to_bool_list n =
                            if n=0 then []
                            else if EVEN n then
                                T::num_to_bool_list((n-2) DIV 2)
                            else
                                F::num_to_bool_list((n-1) DIV 2)`
(WF_REL_TAC `$<` >> intLib.ARITH_TAC)

val solomonoff_prior_def = Define`
solomonoff_prior x = suminf (\n. let b = num_to_bool_list n in
                                     if universal_tm b = x
                                     then inv(2 pow (LENGTH b))
                                     else 0) `


val existence_of_universal_semimeasure = Q.store_thm("existence_of_universal_semimeasure",
`?M. (semimeasure M) /\ (universal_semimeasure M setX) /\ (continous M) /\ (lower_semicompute M)`,
qexists_tac `solomonoff_prior` >> conj_tac)

val summed_square_error_a_def = Define`summed_square_a_error mu a n =
                                       sum for (x IN Bstar:length x = n-1)
                                       (mu x) *(sqrt (cond_M a x) - sqrt (cond_mu a x))**2`

val summed_square_error_def = Define`summed_square_error mu n =
                                     sum for (a in B) summed_square_a_error mu a n`

val KL_dis_def = Define`KL_dis P Q = sum for (a in B) P(a)*log (P(a)/Q(a))`

val hellinger_dis_def = Define`hellinger_dis P Q = sum for (a in B) (sqrt(P(a)) - sqrt(Q(a)))**2`

val KL_greater_hellinger = Q.store_thm("KL_greater_hellinger",
`hellinger_dis P Q <= KL_dis P Q`,
)

val KL_M_dis_def = Define`KL_M_dis mu x = KL_dis (\y. cond_M y x) (\y. cond_mu y x)`

val sum_KL_M_dis_def = Define`sum_KL_M_dis mu n = sum for (x:length x = n-1)
                                                  (mu x) * (KL_M_dis mu x)`

val solomonoff_thm_claim_1 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==> summed_square_error mu n <= sum_KL_M_dis mu n`,
 )

val solomonoff_thm_claim_11 = Q.store_thm("solomonoff_thm_claim_1",
`(computable_measure mu) ==>
 sum for (n in N) summed_square_error mu n <= sum for (n in N) sum_KL_M_dis mu n`,
rw[sum_of_stuff,solomonoff_thm_claim_1] )

val solomonoff_thm_claim_2 = Q.store_thm("solomonoff_thm_claim_2",
`(computable_measure mu) ==> sum for (n in N) sum_KL_M_dis mu n <= (kolmog_complexity mu)*(log 2)`,
  )

val solomonoff_theorem = Q.store_thm("solomonoff_theorem",
`(computable_measure mu) ==>
 (sum for (n in N) summed_square_error mu n <= (kolmog_complexity mu)*(log 2) )`
rw[LESS_EQ_TRANS,solomonoff_thm_claim_11,solomonoff_thm_claim_2])
 *)



*)
val _ = export_theory()
