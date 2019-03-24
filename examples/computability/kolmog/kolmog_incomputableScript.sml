open HolKernel Parse boolLib bossLib

open arithmeticTheory logrootTheory pred_setTheory
open reductionEval;
open churchoptionTheory churchlistTheory recfunsTheory numsAsCompStatesTheory
     kolmog_complexTheory kraft_ineqTheory

val _ = new_theory "kolmog_incomputable"

(*  Proving kolmog is not computable  *)


val tmax_def = Define`
  tmax n = MAX_SET {t | ∃m. terminated (steps t (mk_initial_state m 0)) ∧
                            ¬terminated (steps (t-1) (mk_initial_state m 0)) ∧
                            (LOG 2 m = n) }
`;

val BB_def = Define`
  BB n = @m. terminated (steps (tmax n) (mk_initial_state m 0)) ∧ (LOG 2 m = n)
`;

val HALT_def = Define`
  HALT = {(M,x)| ∃t. terminated (steps t (mk_initial_state M x)) }
`;

val _ = overload_on ("N2T",``λt. toTerm (numdB t)``)

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
  OGENLIST f (SUC n) = OGENLIST f n ++ (case f n of NONE => []| SOME r => [r])
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
             SOME (LEAST x.  ¬MEM x results ∧ LOG 2 x = 2*n)
’;


val cap3_def = Define`cap3 = LAM "f" (
  LAM "p" (
    cpair @@ (cfst @@ VAR "p")
          @@ (cpair @@ (cfst @@ (csnd @@ VAR "p"))
                    @@ (VAR "f" @@ (csnd @@ (csnd @@ VAR "p"))))
  )
)`;

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
 ) ) )`

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


(* still too prove is true *)
(*
Theorem clog2list_behaviour:
  clog2list @@ church n == cvlist (MAP church (log2list n))
Proof
  asm_simp_tac(bsrw_ss())[clog2list_eqn,log2list_def,MAP_GENLIST,
                          ctabulate_cvlist] >>
  HO_MATCH_MP_TAC cvlist_genlist_cong >>
  asm_simp_tac(bsrw_ss())[churchnumTheory.cplus_behaviour,ADD_COMM]
QED
*)


val computable_def = Define`computable (f:num->num) <=> ∃i. ∀n. Phi i n = SOME (f n)`

val narg_kolmog_def = Define`narg_kolmog x = bl2n (arg_kolmog x)`

val plain_kolmog_def = Define`plain_kolmog x = THE (kolmog_complexity x (λy. Phi (bl2n y) 0))`

Theorem plain_kolmog_exists:
  ∀x. ∃y. kolmog_complexity x (λy. Phi (bl2n y) 0) = SOME y
Proof
  rw[kolmog_complexity_def,EXTENSION] >> simp[Phi_def] >>
  qexists_tac`n2bl (dBnum (fromTerm (K @@ church x)))` >> simp[] >> qexists_tac`church x` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED


Theorem Phi_x_0:
  ∀y. ∃x. Phi (x) 0 = SOME y
Proof
  rw[] >> simp[Phi_def] >>
  qexists_tac` (dBnum (fromTerm (K @@ church y)))` >> simp[bool_num_inv] >> qexists_tac`church y` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED

Theorem Phi_bl2nx_0:
  ∀y. ∃x. Phi (bl2n x) 0 = SOME y
Proof
  rw[] >> simp[Phi_def] >>
  qexists_tac`n2bl (dBnum (fromTerm (K @@ church y)))` >> simp[bool_num_inv] >> qexists_tac`church y` >>
  simp[K_lemma,normal_orderTheory.bnf_bnf_of]
QED

Theorem plain_kolmog_thm:
  plain_kolmog x = (MIN_SET {LENGTH p |  Phi (bl2n p) 0 = SOME x})
Proof
  fs[plain_kolmog_def,kolmog_complexity_def] >> Cases_on`{y | Phi (bl2n y) 0 = SOME x} = ∅` >>
  fs[] >> `∃y. Phi (bl2n y) 0 = SOME x` by fs[Phi_bl2nx_0] >>
  `y∈{y | Phi (bl2n y) 0 = SOME x}` by fs[] >> metis_tac[MEMBER_NOT_EMPTY]
QED

val arg_plain_kolmog_def = Define`arg_plain_kolmog x = @q. Phi ( q) 0 = SOME x ∧ LENGTH (n2bl q) = MIN_SET {LENGTH (n2bl p) | Phi ( p) 0 = SOME x}`

val arg_plain_kolmog2_def = Define`arg_plain_kolmog2 x = MIN_SET {p | Phi (p) 0 = SOME x}`

Theorem arg_plain_kolmog_thm:
  arg_plain_kolmog x = @q. Phi ( q) 0 = SOME x ∧ LENGTH (n2bl q) = plain_kolmog x
Proof
  fs[arg_plain_kolmog_def,plain_kolmog_thm] >>
  `{ℓ p | Phi p 0 = SOME x} = {LENGTH p | Phi (bl2n p) 0 = SOME x}` by (fs[EXTENSION] >>
    rw[] >> eq_tac >> rw[] >- (qexists_tac`n2bl p` >> fs[]) >- (qexists_tac`bl2n p` >> fs[]) )>>
  fs[]
QED

Theorem arg_plain_kolmog_exists:
  ∃q. Phi q 0 = SOME x ∧ LENGTH (n2bl q) = plain_kolmog x
Proof
  fs[plain_kolmog_thm] >> `{LENGTH p | Phi (bl2n p) 0 = SOME x} <> {}` by
    fs[EXTENSION,Phi_bl2nx_0] >>
  `MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME x} ∈ {LENGTH p | Phi (bl2n p) 0 = SOME x} ` by
    fs[MIN_SET_LEM] >>
  `IMAGE LENGTH {p | Phi (bl2n p) 0 = SOME x} = {LENGTH p | Phi (bl2n p) 0 = SOME x}` by
    fs[IMAGE_DEF] >>
  `MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME x} ∈ IMAGE LENGTH {p | Phi (bl2n p) 0 = SOME x}` by
    metis_tac[] >>
  `∃q1. MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME x} =  LENGTH q1 ∧ q1 ∈ {p | Phi (bl2n p) 0 = SOME x}` by
    metis_tac[IN_IMAGE] >> qexists_tac`bl2n q1` >> fs[]
QED

Theorem Phi_arg_pl_kolmog:
  Phi (arg_plain_kolmog y) 0 = SOME y
Proof
  fs[arg_plain_kolmog_thm] >>
  `∃q. Phi q 0 = SOME y ∧ LENGTH (n2bl q) = plain_kolmog y` by fs[arg_plain_kolmog_exists] >>
  metis_tac[GSYM SELECT_THM]
QED

Theorem Phi_arg_pl_kolmog2:
  Phi (arg_plain_kolmog2 y) 0 = SOME y
Proof
  fs[arg_plain_kolmog2_def] >> `{p | Phi p 0 = SOME y} <> {}` by (fs[EXTENSION,Phi_x_0]) >>
  `MIN_SET {p | Phi p 0 = SOME y} ∈ {p | Phi p 0 = SOME y}` by metis_tac[MIN_SET_LEM]>>
  fs[]
QED

Theorem MIN_SET_L_PHI_NON_EMPTY:
  {LENGTH p | Phi (bl2n p) 0 = SOME y} <> {}
Proof
  fs[EXTENSION,Phi_bl2nx_0]
QED

(* SELECT stuff
SELECT_AX,SELECT_ELIM_THM,SELECT_REFL,SELECT_REFL_2,SELECT_THM,SELECT_UNIQUE
*)

(* up to here *)

(* To prove maybe
Theorem LEGNTH_n2bl_LOG:
  0<x ==> LENGTH (n2bl x) = LOG 2 (SUC x)
Proof
  rw[] >>
  Induct_on`LOG 2 x` >> rw[] >- (`x=1` by  fs[LOG_EQ_0] >> rw[] >> EVAL_TAC >> fs[LOG_BASE] ) >>

QED

Theorem LENGTH_n2bl_ineq:
  ℓ q < ℓ k ==> q< k
Proof

QED
*)

Theorem arg_pl_kolmog2_min:
  Phi k 0 = SOME y ==>  arg_plain_kolmog2 y ≤ k
Proof
  rw[arg_plain_kolmog2_def] >> fs[EXTENSION,Phi_x_0,MIN_SET_LEM]
QED

(* unproven *)
Theorem arg_pl_kolmog_min:
  Phi k 0 = SOME y ==>  arg_plain_kolmog y ≤ k
Proof
  cheat
  (*
  rw[arg_plain_kolmog_thm] >>
  `(∃q. Phi q 0 = SOME y ∧ ℓ q = plain_kolmog y ∧ (q<=k))` by
  (Cases_on`ℓ k = plain_kolmog y` >- (qexists_tac`k` >> fs[]) >>
  `∃q. Phi q 0 = SOME y ∧ LENGTH (n2bl q) = plain_kolmog y` by fs[arg_plain_kolmog_exists]>>
  `(∀x. (Phi x 0 = SOME y ∧ ℓ x = plain_kolmog y) ⇒ (ℓ x<= ℓ k))` by
    (rw[] >> fs[plain_kolmog_thm] >>
     `{LENGTH p | Phi (bl2n p) 0 = SOME y} <> {}` by fs[MIN_SET_L_PHI_NON_EMPTY] >>
     `∀x. x ∈ {LENGTH p | Phi (bl2n p) 0 = SOME y} ⇒
          MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME y} ≤ x` by fs[MIN_SET_LEM] >>
     `LENGTH (n2bl k) ∈ IMAGE LENGTH { p | Phi (bl2n p) 0 = SOME y}` by fs[] >>
     `ℓ k ∈ {LENGTH p | Phi (bl2n p) 0 = SOME y}` by
       (rfs[IMAGE_DEF] >> qexists_tac`n2bl k` >> fs[]) >>
     ` MIN_SET {LENGTH p | Phi (bl2n p) 0 = SOME y} ≤ ℓ k` by metis_tac[] >> fs[] ) >>
   `ℓ q <= ℓ k` by metis_tac[] >> `ℓ q < ℓ k` by fs[] >> qexists_tac`q` >> rw[] >>
   `q < k` by fs[LENGTH_n2bl_ineq] >> fs[]) >>

  metis_tac[SELECT_ELIM_THM] >>
  fs[GSYM SELECT_THM] *)
QED

(* Part1 uses kolmog, Part11 uses arg_plain_kolmog, Part111 uses arg_plain_kolmog2  *)
(* unproven *)
Theorem part1:
  computable kolmog ==> ∃j. ∀y. ∃i. Phi j y = SOME i ∧ Phi i 0 = SOME y ∧ ∀k. Phi k 0 = SOME y ==> i<= k
Proof
  cheat
  (*
  rw[computable_def] >> qexists_tac`@q.∀y. Phi q y = SOME (MIN_SET {p | Phi p 0 = SOME y })` >>
  rw[] >> qexists_tac`MIN_SET {p | Phi p 0 = SOME y }` >> *)
QED

(* unproven *)
Theorem part11:
  computable arg_plain_kolmog ==> ∃j. ∀y. ∃i. Phi j y = SOME i ∧ Phi i 0 = SOME y ∧ ∀k. Phi k 0 = SOME y ==> i<= k
Proof
  cheat
  (* rw[computable_def] >> qexists_tac`i` >> rw[]
  >- (fs[narg_kolmog_def,arg_kolmog_thm,PUTM_def])
  >- () *)
QED

(* proven *)
Theorem part111:
  computable arg_plain_kolmog2 ==> ∃j. ∀y. ∃i. Phi j y = SOME i ∧ Phi i 0 = SOME y ∧ ∀k. Phi k 0 = SOME y ==> i<= k
Proof
  rw[computable_def] >> qexists_tac`i` >> rw[arg_pl_kolmog2_min,Phi_arg_pl_kolmog2]
QED

val yMt_pred_def = Define`yMt_pred e n yi Mi ti <=> plain_kolmog yi < 2*n ∧
                                                LOG 2 yi = 2* n ∧
                                                LOG 2 Mi = kolmog yi ∧
                                                terminated (steps ti (mk_initial_state Mi 0)) ∧
                                                cs_to_num (steps ti (mk_initial_state Mi 0)) = yi ∧
                                              ∀t'. terminated (steps t' (mk_initial_state Mi 0)) ==>
                                                ti<=t' ∧
                                                e=npair Mi (npair ti yi)`

(* unproven *)
(*
Theorem part2:
  computable kolmog ==> ∃j. ∀n. ∃l. Phi j n = SOME (nlist_of l) ∧
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





val yMt_set_def = Define`
  yMt_set n = {(yi,Mi,t) | Mi = bl2n (arg_kolmog yi) ∧
                           LENGTH (n2bl yi) = 2*n ∧
                           kolmog yi < 2*n ∧
                           terminated (steps t (mk_initial_state Mi 0)) ∧
                           cs_to_num (steps t (mk_initial_state Mi 0)) = yi ∧
                           ∀t'. terminated (steps t' (mk_initial_state Mi 0))
                                  ==> t<=t'
              }
`;

val big_T_def = Define`big_T n = MAX_SET (IMAGE SND (IMAGE SND (yMt_set n)))`

(* unproven *)

Theorem part3:
  computable kolmog ==> (big_T (prime_tm M x) > tmax (LOG 2 (prime_tm M x) ))
Proof
  cheat
QED

open whileTheory;

Theorem terminated_ge:
  (a > b) ==> (terminated (steps b cs) ==> terminated (steps a cs))
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

(*
Theorem big_T_Tmax_imp:
  (big_T (LOG 2 (prime_tm M x) ) > tmax (LOG 2 (prime_tm M x) )) ==>
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
