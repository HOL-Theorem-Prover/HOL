open HolKernel Parse boolLib bossLib

open arithmeticTheory whileTheory logrootTheory pred_setTheory listTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmog_complexTheory kraft_ineqTheory

val _ = new_theory "kolmog_incomputable"

(*  Proving kolmog is not computable  *)

(* longest it takes machines of size n to terminate *)
val tmax_def = Define`
  tmax n = MAX_SET {t | ∃m. terminated (steps t (mk_initial_state m 0)) ∧
                            ¬terminated (steps (t-1) (mk_initial_state m 0)) ∧
                            ( ℓ  m = n) }
`;

(* the machine of size n, that takes that longest time to terminate,
   the "busy beaver" if you will
*)
val BB_def = Define`
  BB n = @m. terminated (steps (tmax n) (mk_initial_state m 0)) ∧ (LOG 2 m = n)
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
             SOME (LEAST x. ¬MEM x results ∧ LOG 2 x = 2*n)
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

val arg_plain_kolmog_def = new_specification("arg_plain_kolmog_def",
  ["arg_plain_kolmog"], CONV_RULE SKOLEM_CONV arg_plain_pred_exists);

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

Theorem MEM_log2list = ELL_log2list |> SPEC_ALL |> Q.INST [‘i’ |-> ‘ℓ n’]
                                    |> SIMP_RULE (srw_ss()) []

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
  B @@ (
    (* let c = ... in *)
    LAM "c" (
       LAM "machines" (
         LAM "run" (
           cfindleast
             @@ (B @@ (cexists @@ cbnf) @@ VAR "run")
             @@ (LAM "i" (cplus @@ (cpred @@ (cexp @@ church 2 @@ VAR "c"))
                                @@ (cfind_index @@ cbnf
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
       @@ (* machine's value *) (cmap @@ (B @@ cnumdB @@ cpred)
                                      @@ (clog2list @@ VAR "c"))
    )
  )
    @@ (* c's value: *) (B @@ (cbnf_ofk @@ cforce_num)
                           @@ (B @@ (cdAPP @@ (cnumdB @@ church pki))
                                 @@ cchurch))
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

Theorem kolmog_arg_computable:
  computable plain_kolmog ⇒ computable arg_plain_kolmog
Proof
  cheat (*
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
  asm_simp_tac (bsrw_ss()) [clog2list_behaviour, cmap_cvlist] >>
  simp[listTheory.MAP_MAP_o] >>
  qmatch_abbrev_tac ‘∃z. bnf_of (cfindleast @@ P @@ k) = SOME z ∧
                         arg_plain_kolmog y = force_num z’ >>
  ‘∀n. ∃b. P @@ church n == cB b’
     by (simp_tac (bsrw_ss()) [Abbr‘P’, cmap_cvlist] >>
         simp[listTheory.MAP_MAP_o] >> qx_gen_tac ‘n’ >>
         qmatch_abbrev_tac ‘∃b. cexists @@ cbnf @@ cvlist l == cB b’ >>
         ‘∀e. MEM e l ⇒ ∃b. cbnf @@ e == cB b’
            (simp[Abbr‘l’, MEM_MAP, PULL_EXISTS] >>
             simp_tac (bsrw_ss()) [churchDBTheory.csteps_behaviour,
                                   churchDBTheory.cbnf_behaviour]) >>
         asm_simp_tac (bsrw_ss()) [cexists_thm]) >>
  drule (GEN_ALL churchnumTheory.cfindleast_termI) >>
  ‘∃m. P @@ church m == cB T’
    by (simp_tac (bsrw_ss()) [Abbr‘P’, cmap_cvlist] >>
        qho_match_abbrev_tac ‘∃m. cexists @@ cbnf @@ cvlist (Tf m) == cB T’ >>
        ‘∃t e. MEM e (Tf t) ∧ cbnf @@ e == cB T’
           by (simp[Abbr‘Tf’, MEM_MAP, PULL_EXISTS] >>
               simp_tac (bsrw_ss()) [churchDBTheory.csteps_behaviour,
                                     churchDBTheory.cbnf_behaviour] >>
               qspec_then ‘y’ strip_assume_tac plain_kolmog_props >>
               rename [‘Phi M 0 = SOME y’, ‘log2list (plain_kolmog y)’] >>
               simp[]


) >>
        ‘∀m' e. MEM e (Tf m') ⇒ ∃b. cbnf @@ e == cB b’
           by (
        asm_simp_tac(bsrw_ss()) [cexists_thm] *)
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

Theorem part22:
  computable plain_kolmog ==> ∃j. ∀n. ∃l. Phi j n = SOME (nlist_of l) ∧
                       (∀e. MEM e l <=> ∃yi Mi ti. yMt_pred e n yi Mi ti)
Proof
  cheat
QED


val yMt_set_def = Define‘
  yMt_set n = {(yi,Mi,t) | ∃e. yMt_pred n e yi Mi t }
’;

val big_T_def = Define`big_T n = MAX_SET (IMAGE SND (IMAGE SND (yMt_set n)))`

(* unproven *)

Theorem part3:
  computable plain_kolmog ==>
  tmax (ℓ (prime_tm M x) ) < big_T (prime_tm M x)
Proof
  cheat
QED

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

(* still need to prove FINITE s *)


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


Theorem terminated_tmax:
  (∃t. terminated (steps t (mk_initial_state (prime_tm M x) 0))) ==>
  terminated (steps (tmax (ℓ (prime_tm M x))) (mk_initial_state (prime_tm M x) 0))
Proof
  rw[] >> Cases_on`terminated (steps 0 (mk_initial_state (prime_tm M x) 0))`
  >- (Cases_on`0<tmax (ℓ (prime_tm M x))` >>fs[]>> metis_tac[terminated_ge]) >> 
  `∃tl. tl < t ∧ ¬terminated (steps tl (mk_initial_state (prime_tm M x) 0)) ∧
        terminated (steps (tl + 1) (mk_initial_state (prime_tm M x) 0))` by 
    fs[terminated_down] >> 
  rw[tmax_def]>> qabbrev_tac`s = {t | (∃m. terminated (steps t (mk_initial_state m 0)) ∧
             ¬terminated (steps (t − 1) (mk_initial_state m 0)) ∧
             ℓ m = ℓ (prime_tm M x))}` >>
  `s <> {}` by 
    (fs[Abbr`s`,EXTENSION] >> qexists_tac`tl+1` >> qexists_tac`prime_tm M x` >> fs[]) >>
  `(tl+1) ∈ s` by (fs[Abbr`s`,IN_DEF] >> qexists_tac`prime_tm M x` >> fs[])>>
  `FINITE s` by (fs[Abbr`s`] >> 
                 metis_tac[ELL_SURJ_terminate,FINITE_SURJ,ELL_terminated_FINITE]) >> 
  `tl+1<=MAX_SET s` by metis_tac[in_max_set] >>metis_tac[terminated_le]
QED

Theorem part4:
  tmax (ℓ (prime_tm M x) ) < big_T (prime_tm M x) ⇒
  (terminated (steps (big_T  ( (prime_tm M x)))
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
