open HolKernel Parse boolLib bossLib dep_rewrite bitLib reduceLib combinLib computeLib;
open optionTheory pairTheory arithmeticTheory combinTheory listTheory
     rich_listTheory whileTheory bitTheory dividesTheory wordsTheory;

(* The SHA-3 Standard: https://doi.org/10.6028/NIST.FIPS.202 *)

val _ = new_theory "keccak";

Datatype:
  state_array =
  <| w: num
   ; A: num # num # num -> bool
   |>
End

val state_array_component_equality = theorem"state_array_component_equality";

Definition wf_state_array_def:
  wf_state_array a ⇔
  ∀x y z. ¬(x < 5 ∧ y < 5 ∧ z < a.w) ⇒ ¬ a.A (x, y, z)
End

Definition Keccak_widths_def:
  Keccak_widths = {25; 50; 100; 200; 400; 800; 1600}
End

fun pow2 n = if n = 0 then 1 else 2 * pow2 (n - 1)

Theorem Keccak_widths_DIV_25:
  w ∈ Keccak_widths ⇒ ∃n. w = 25 * n
Proof
  rw[Keccak_widths_def]
  THENL (List.tabulate(7,
    fn i => exists_tac(numSyntax.term_of_int(pow2 i)))
  ) \\ simp[]
QED

Definition b2w_def:
  b2w b = b DIV 25
End

Definition w2l_def:
  w2l w = LOG2 w
End

Definition restrict_def:
  restrict (w:num) f (x, y, z) ⇔
  x < 5 ∧ y < 5 ∧ z < w ∧ f (x, y, z)
End

Definition string_to_state_array_def:
  string_to_state_array s =
  let b = LENGTH s in
  let w = b2w b in
    <| w := w
     ; A := restrict w $ λ(x, y, z). EL (w * (5 * y + x) + z) s
     |>
End

Theorem wf_string_to_state_array[simp]:
  wf_state_array (string_to_state_array s)
Proof
  rw[wf_state_array_def, string_to_state_array_def, restrict_def]
  \\ rw[]
QED

Theorem string_to_state_array_w:
  (string_to_state_array s).w = b2w $ LENGTH s
Proof
  rw[string_to_state_array_def]
QED

Definition Lane_def:
  Lane a (i, j) =
    GENLIST (λw. a.A (i, j, w)) a.w
End

Theorem LENGTH_Lane[simp]:
  LENGTH (Lane a x) = a.w
Proof
  Cases_on`x` \\ rw[Lane_def]
QED

Definition Plane_def:
  Plane a j =
    FLAT (GENLIST (λi. Lane a (i, j)) 5)
End

Theorem LENGTH_Plane[simp]:
  LENGTH (Plane a j) = 5 * a.w
Proof
  rw[Plane_def]
QED

Definition state_array_to_string_def:
  state_array_to_string a =
    FLAT (GENLIST (Plane a) 5)
End

Theorem LENGTH_state_array_to_string[simp]:
  LENGTH (state_array_to_string a) = 25 * a.w
Proof
  rw[state_array_to_string_def]
QED

Triviality GENLIST_AND_LENGTH:
  GENLIST (λx. x < n ∧ P x) n = GENLIST P n
Proof
  qid_spec_tac`P` \\
  Induct_on`n` \\ rw[GENLIST_CONS, o_DEF]
QED

Theorem string_to_state_array_to_string:
  LENGTH s = 25 * n ⇒
  state_array_to_string (string_to_state_array s) = s
Proof
  rw[state_array_to_string_def, string_to_state_array_def,
     Plane_def, Lane_def, b2w_def, restrict_def, GENLIST_AND_LENGTH] \\
  let
    val thm = GENLIST_APPEND |> GSYM
    val cnv = numSyntax.term_of_int
    fun tac i =
      thm |> Q.ISPECL_THEN[`λw. EL w s`, `n`, `^(cnv i) * n`]
      mp_tac \\ simp[] \\ disch_then kall_tac
    fun k n = if n = 25 then ALL_TAC else tac n \\ k (n + 1)
  in
    k 1
  end \\
  pop_assum (SUBST1_TAC o SYM) \\
  simp[GENLIST_ID]
QED

Theorem state_array_to_string_to_state_array:
  wf_state_array a ⇒
  string_to_state_array (state_array_to_string a) = a
Proof
  rw[state_array_to_string_def, string_to_state_array_def, b2w_def,
     state_array_component_equality, FUN_EQ_THM, FORALL_PROD,
     wf_state_array_def]
  \\ rw [Plane_def, Lane_def]
  \\ rename1 `a.A (x, y, z)`
  \\ simp[restrict_def]
  \\ reverse (Cases_on`x < 5 ∧ y < 5 ∧ z < a.w`)
  >- metis_tac[]
  \\ fs[NUMERAL_LESS_THM]
  \\ simp[EL_APPEND1,EL_APPEND2]
QED

Definition theta_c_def:
  theta_c A (x, z) =
    (A (x, 0, z) ≠
     (A (x, 1, z) ≠
      (A (x, 2, z) ≠
       (A (x, 3, z) ≠
        (A (x, 4, z))))))
End

Definition theta_d_def:
  theta_d w A (x, z) =
  let c = theta_c A in
    c ((x + 4) MOD 5, z) ≠
    c ((x + 1) MOD 5, (z + PRE w) MOD w)
End

Definition theta_def:
  theta a =
  a with A updated_by (λf. restrict a.w $ λ(x, y, z).
    f (x, y, z) ≠ theta_d a.w a.A (x, z))
End

Theorem wf_theta[simp]:
  wf_state_array a ⇒ wf_state_array (theta a)
Proof
  rw[wf_state_array_def, theta_def, restrict_def] \\ rw[]
QED

Theorem theta_w[simp]:
  (theta a).w = a.w
Proof
  rw[theta_def]
QED

Definition rho_xy_def[simp]:
  rho_xy 0 = (1, 0) ∧
  rho_xy (SUC t) =
  let (x, y) = rho_xy t in
    (y, (2 * x + 3 * y) MOD 5)
End

Theorem rho_xy_exists:
  x < 5 ∧ y < 5 ∧ ¬(x = 0 ∧ y = 0)
  ⇒ ∃t. t ≤ 23 ∧ rho_xy t = (x, y)
Proof
  disch_then(strip_assume_tac o SIMP_RULE(srw_ss())[NUMERAL_LESS_THM])
  \\ simp[LESS_OR_EQ]
  \\ ntac 25 (srw_tac[DNF_ss][Once NUMERAL_LESS_THM] \\ EVAL_TAC)
QED

Definition rho_def:
  rho a =
  a with A updated_by (λf. restrict a.w $ λ(x, y, z).
    if x = 0 ∧ y = 0 then f (x, y, z)
    else
      let t = LEAST t. rho_xy t = (x, y) in
      let tt = ((t + 1) * (t + 2)) DIV 2 in
      let ww = a.w * (SUC tt DIV a.w) in
      f (x, y, (z + ww - tt) MOD a.w))
End

Theorem wf_rho[simp]:
  wf_state_array a ⇒ wf_state_array (rho a)
Proof
  rw[wf_state_array_def, rho_def, restrict_def] \\ rw[]
QED

Theorem rho_w[simp]:
  (rho a).w = a.w
Proof
  rw[rho_def]
QED

Definition pi_def:
  pi a =
  a with A updated_by (λf. restrict a.w $ λ(x, y, z).
    f ((x + 3 * y) MOD 5, x, z))
End

Theorem wf_pi[simp]:
  wf_state_array a ⇒ wf_state_array (pi a)
Proof
  rw[wf_state_array_def, pi_def, restrict_def] \\ rw[]
QED

Theorem pi_w[simp]:
  (pi a).w = a.w
Proof
  rw[pi_def]
QED

Definition chi_def:
  chi a =
  a with A updated_by (λf. restrict a.w $ λ(x, y, z).
    f (x, y, z) ≠
    (¬ f ((x + 1) MOD 5, y, z) ∧
     f ((x + 2) MOD 5, y, z)))
End

Theorem wf_chi[simp]:
  wf_state_array a ⇒ wf_state_array (chi a)
Proof
  rw[wf_state_array_def, chi_def, restrict_def] \\ rw[]
QED

Theorem chi_w[simp]:
  (chi a).w = a.w
Proof
  rw[chi_def]
QED

Definition rc_step_def:
  rc_step r =
  let ra = F :: r in
  let re =
    GENLIST (λi.
      if i ∈ {0; 4; 5; 6} then
        EL i ra ≠ EL 8 ra
      else
        EL i ra)
      9
  in
    TAKE 8 re
End

Definition rc_def:
  rc t =
  if t MOD 255 = 0 then T else
  HD (FUNPOW rc_step (t MOD 255) (T :: REPLICATE 7 F))
End

Definition iota_def[nocompute]:
  iota a i =
  a with A updated_by (λf. restrict a.w $ λ(x, y, z).
    if x = 0 ∧ y = 0 then
      let l = w2l a.w in
      let RCz = case some j. j ≤ l ∧ z = 2 ** j - 1
                of NONE => F
                 | SOME j => rc (j + 7 * i)
      in
        f (x, y, z) ≠ RCz
    else f (x, y, z))
End

Theorem wf_iota[simp]:
  wf_state_array a ⇒ wf_state_array (iota a i)
Proof
  rw[wf_state_array_def, iota_def, restrict_def] \\ rw[]
QED

Theorem iota_w[simp]:
  (iota a i).w = a.w
Proof
  rw[iota_def]
QED

Definition Rnd_def:
  Rnd a = iota (chi (pi (rho (theta a))))
End

Theorem wf_Rnd[simp]:
  wf_state_array a ⇒ wf_state_array (Rnd a i)
Proof
  rw[Rnd_def]
  \\ DEP_REWRITE_TAC[wf_iota]
  \\ rw[]
QED

Theorem Rnd_w[simp]:
  (Rnd a i).w = a.w
Proof
  rw[Rnd_def]
QED

(* N.B. We assume here that the round index is always non-negative, which is not
* assumed in the standard. *)

Definition Keccak_p_def:
  Keccak_p n s =
  let a = string_to_state_array s in
  let l = w2l a.w in
  let i0 = 12 + 2 * l - n in
  let i1 = 12 + 2 * l - 1 in
  let a1 = FST (FUNPOW (λ(a,i). (Rnd a i, SUC i)) (SUC i1 - i0) (a, i0)) in
  state_array_to_string a1
End

(* TODO: move / find in a lib *)
Definition chunks_def:
  chunks n ls =
  if LENGTH ls <= n ∨ n = 0
  then [ls]
  else CONS (TAKE n ls) (chunks n (DROP n ls))
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ rw[LENGTH_DROP]
End

val chunks_ind = theorem"chunks_ind";

Theorem chunks_NIL[simp]:
  chunks n [] = [[]]
Proof
  rw[Once chunks_def]
QED

Theorem FLAT_chunks[simp]:
  FLAT (chunks n ls) = ls
Proof
  completeInduct_on`LENGTH ls` \\ rw[]
  \\ rw[Once chunks_def]
QED

Theorem divides_EVERY_LENGTH_chunks:
  !n ls. ls <> [] /\ divides n (LENGTH ls) ==>
    EVERY ($= n o LENGTH) (chunks n ls)
Proof
  recInduct chunks_ind
  \\ rw[]
  \\ rw[Once chunks_def] \\ fs[]
  \\ gs[divides_def]
  >- ( Cases_on`q = 0` \\ fs[] )
  \\ first_x_assum irule
  \\ qexists_tac`PRE q`
  \\ Cases_on`q` \\ fs[ADD1]
QED

Definition sponge_def:
  sponge f b pad r N d =
  let P = N ++ pad r (LENGTH N) in
  let n = LENGTH P DIV r in
  let c = b - r in
  let Pis = chunks r P in
  let S0 = REPLICATE b F in
  let S = FOLDL (λSi Pi. f (MAP2 $<> Si (Pi ++ REPLICATE c F))) S0 Pis in
  let t = SUC (d DIV r) in
  let Z = FST $ FUNPOW (λ(Z, S). (Z ++ (TAKE r S), f S)) t ([], S) in
  TAKE d Z
End

Definition pad10s1_def:
  pad10s1 x m =
  let j = (x * (2 + m DIV x) - m - 2) MOD x in
    [T] ++ REPLICATE j F ++ [T]
End

Theorem LENGTH_pad10s1:
  0 < x ⇒ ∃d. m + LENGTH (pad10s1 x m) = d * x
Proof
  Cases_on`x = 1` >> fs[]>>
  rw[pad10s1_def, ADD1, LEFT_ADD_DISTRIB]>>
  `2 * x + x * (m DIV x) = (2 + m DIV x) * x` by fs[]>>
  pop_assum SUBST_ALL_TAC>>
  DEP_REWRITE_TAC[MOD_COMPLEMENT]>>
  imp_res_tac DIVISION>>fs[]>>
  CONJ_TAC >- (
    simp[LEFT_ADD_DISTRIB]>>
    last_x_assum (qspec_then`m` assume_tac)>>
    qsuff_tac`2 + m MOD x < 2 * x` >>
    simp[]>>
    `2 <= x` by
      (Cases_on`x`>>fs[])>>
    last_x_assum (qspec_then`m` assume_tac)>>
    DECIDE_TAC)>>
  last_x_assum(qspec_then`m+2` assume_tac)>>
  Cases_on`(m + 2) MOD x = 0`
  >- (
    fs[]>>
    metis_tac[MULT_COMM])>>
  DEP_ONCE_REWRITE_TAC[LESS_MOD]>>
  simp[]>>
  `(m + 2) MOD x + (x − (m + 2) MOD x) = x` by
    (last_x_assum (qspec_then`m+2` assume_tac)>>
     DECIDE_TAC)>>
  `m + (x − (m + 2) MOD x + 2)  =
   ((m + 2) DIV x + 1) * x` by fs[]>>
  metis_tac[]
QED

Definition Keccak_def:
  Keccak c = sponge (Keccak_p 24) 1600 pad10s1 (1600 - c)
End

Definition Keccak_256_def:
  Keccak_256 M = Keccak 512 M 256
End

Definition SHA3_224_def:
  SHA3_224 M = Keccak 448 (M ++ [F; T]) 224
End

Definition SHA3_256_def:
  SHA3_256 M = Keccak 512 (M ++ [F; T]) 256
End

Definition SHA3_384_def:
  SHA3_384 M = Keccak 768 (M ++ [F; T]) 384
End

Definition SHA3_512_def:
  SHA3_512 M = Keccak 1024 (M ++ [F; T]) 512
End

(* compute-friendly versions and tests *)

(* TODO: move *)
Theorem LOG_POW:
  1 < b ==> LOG b (b ** n) = n
Proof
  strip_tac
  \\ irule logrootTheory.LOG_UNIQUE
  \\ rw[EXP]
QED

(* TODO: move *)
Theorem FUNPOW_COMPOSE:
  !n x f g h.
  (!m. m < n ==> h(g(FUNPOW f m x)) = FUNPOW f m x)
  ==>
  FUNPOW (g o f o h) n (g x) =
  g (FUNPOW f n x)
Proof
  Induct \\ rw[]
  \\ rw[FUNPOW_SUC]
QED

(* TODO: move *)
Theorem FUNPOW_CONG:
  !n x f g.
  (!m. m < n ==> f (FUNPOW f m x) = g (FUNPOW f m x))
  ==>
  FUNPOW f n x = FUNPOW g n x
Proof
  Induct \\ rw[FUNPOW_SUC]
  \\ AP_TERM_TAC \\ rw[]
QED

(* TODO: move *)
Theorem FUNPOW_invariant:
  !m x.
  P x /\ (!x. P x ==> P (f x)) ==>
  P (FUNPOW f m x)
Proof
  Induct \\ rw[FUNPOW_SUC]
QED

Triviality iota_some_elim:
  (some j. j ≤ l ∧ z = 2 ** j - 1)
  = if z = 2 ** LOG2 (SUC z) - 1 ∧ LOG2 (SUC z) ≤ l
    then SOME (LOG2 (SUC z))
    else NONE
Proof
  DEEP_INTRO_TAC some_intro \\
  rw[ADD1, SUB_ADD, LOG_POW, LOG2_def]
QED

Triviality iota_case_cond:
  (case (if b then SOME x else NONE) of NONE => y | SOME z => f z) =
  if b then f x else y
Proof
  rw[]
QED

Theorem iota_compute = iota_def |>
  SIMP_RULE (srw_ss()) [iota_some_elim, iota_case_cond];

Definition tabulate_array_def:
  tabulate_array a =
  a with A := restrict a.w (λ(x, y, z).
    EL (y * 5 * a.w + x * a.w + z) (state_array_to_string a))
End

Definition tabulate_string_def:
  tabulate_string w s = <|
    w := w
  ; A := restrict w (λ(x, y, z). EL (y * 5 * w + x * w + z) s)
  |>
End

Theorem wf_tabulate_string[simp]:
  wf_state_array (tabulate_string w s)
Proof
  rw[wf_state_array_def, tabulate_string_def, restrict_def]
  \\ rw[]
QED

Theorem tabulate_string_w[simp]:
  (tabulate_string w s).w = w
Proof
  rw[tabulate_string_def]
QED

Theorem tabulate_id:
  wf_state_array a ⇒
  tabulate_array a = a
Proof
  rw[wf_state_array_def, tabulate_array_def, state_array_component_equality]
  \\ rw[state_array_to_string_def, FUN_EQ_THM, FORALL_PROD, restrict_def]
  \\ rename1`(x,y,z)`
  \\ Cases_on`x < 5` \\ fs[]
  \\ Cases_on`y < 5` \\ fs[]
  \\ Cases_on`z < a.w` \\ fs[]
  \\ fs[NUMERAL_LESS_THM, EL_APPEND_EQN] \\ rw[]
  \\ fs[Plane_def, EL_APPEND_EQN] \\ fs[Lane_def]
QED

Definition Rnd_string_def:
  Rnd_string w s i =
  let θ = state_array_to_string $ theta $ tabulate_string w s in
  let ρ = state_array_to_string $ rho $ tabulate_string w θ in
  let π = state_array_to_string $ pi $ tabulate_string w ρ in
  let χ = state_array_to_string $ chi $ tabulate_string w π in
  let ι = iota $ tabulate_string w χ in
  state_array_to_string $ ι i
End

Theorem LENGTH_Rnd_string[simp]:
  LENGTH (Rnd_string w s i) = 25 * w
Proof
  rw[Rnd_string_def]
QED

Theorem tabulate_state_array_to_string:
  wf_state_array a ∧ w = a.w
  ⇒
  tabulate_string w (state_array_to_string a) = a
Proof
  strip_tac
  \\ first_assum (mp_then Any
       (CONV_TAC o (RHS_CONV o (REWR_CONV o SYM)))
       tabulate_id)
  \\ rw[tabulate_array_def, tabulate_string_def, state_array_component_equality]
QED

Theorem Rnd_string_Rnd:
  w = b2w (LENGTH s) ⇒
  Rnd_string w s i =
  state_array_to_string (Rnd (string_to_state_array s) i)
Proof
  rw[Rnd_string_def, Rnd_def]
  \\ AP_TERM_TAC
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[tabulate_state_array_to_string, wf_chi]
  \\ simp[]
  \\ rpt AP_TERM_TAC
  \\ rw[string_to_state_array_def,
        state_array_component_equality,
        tabulate_string_def]
  \\ rw[restrict_def, FUN_EQ_THM, FORALL_PROD]
  \\ rw[EQ_IMP_THM]
  \\ fs[LEFT_ADD_DISTRIB]
QED

Theorem Rnd_Rnd_string:
  wf_state_array a ∧ w = a.w
  ⇒
  Rnd a i =
  string_to_state_array (Rnd_string w (state_array_to_string a) i)
Proof
  rw[Rnd_def, Rnd_string_def]
  \\ DEP_REWRITE_TAC[state_array_to_string_to_state_array]
  \\ simp[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[tabulate_state_array_to_string]
  \\ simp[]
QED

Definition Keccak_p_tabulate_def:
  Keccak_p_tabulate n s =
  let w = b2w (LENGTH s) in
  let l = w2l w in
  let i0 = 12 + 2 * l - n in
  let i1 = 12 + 2 * l - 1 in
  FST (FUNPOW (λ(s,i). (Rnd_string w s i, SUC i)) (SUC i1 - i0) (s, i0))
End

Theorem Keccak_p_tabulate:
  LENGTH s = 25 * divisor ⇒
  Keccak_p n s = Keccak_p_tabulate n s
Proof
  rw[Keccak_p_def, Keccak_p_tabulate_def, string_to_state_array_w, ADD1]
  \\ qmatch_goalsub_abbrev_tac`2 * l`
  \\ qmatch_goalsub_abbrev_tac`(s, i)`
  \\ qmatch_goalsub_abbrev_tac`FUNPOW k m`
  \\ qmatch_goalsub_abbrev_tac`Rnd_string w`
  \\ qmatch_goalsub_abbrev_tac`FUNPOW f m (s,i)`
  \\ qspecl_then[`m`,`(s,i)`,`f`,
       `string_to_state_array ## I`,
       `state_array_to_string ## I`]mp_tac FUNPOW_COMPOSE
  \\ simp[Abbr`f`, o_DEF, LAMBDA_PROD, PAIR_MAP]
  \\ qmatch_goalsub_abbrev_tac`FST (FUNPOW k m x)`
  \\ qmatch_goalsub_abbrev_tac`FUNPOW d m x`
  \\ `∀x. w = (FST x).w ∧ wf_state_array (FST x) ⇒ d x = k x`
  by (
    simp[Abbr`d`,Abbr`k`, FUN_EQ_THM, FORALL_PROD]
    \\ rw[Rnd_Rnd_string] )
  \\ `FUNPOW k m x = FUNPOW d m x`
  by (
    irule FUNPOW_CONG
    \\ qx_gen_tac`z`
    \\ strip_tac
    \\ irule EQ_SYM
    \\ first_x_assum irule
    \\ conj_tac
    \\ qho_match_abbrev_tac`P (FUNPOW k z x)`
    \\ irule FUNPOW_invariant
    \\ simp[Abbr`P`, Abbr`x`, Abbr`k`, FORALL_PROD]
    \\ simp[string_to_state_array_w] )
  \\ fs[]
  \\ disch_then (fn th => DEP_REWRITE_TAC[th])
  \\ simp[]
  \\ rw[]
  \\ DEP_REWRITE_TAC[GEN_ALL string_to_state_array_to_string]
  \\ simp[]
  \\ qexists_tac`divisor`
  \\ qmatch_goalsub_abbrev_tac`FUNPOW p z q`
  \\ qho_match_abbrev_tac`P (FUNPOW p z q)`
  \\ irule FUNPOW_invariant
  \\ simp[Abbr`P`, Abbr`q`, Abbr`p`, FORALL_PROD, Abbr`w`, b2w_def]
QED

(*
Theorem Keccak_tabulate:
  Keccak c = sponge (Keccak_p_tabulate 24) 1600 pad10s1 (1600 - c)
Proof
  rw[Keccak_def, sponge_def, FUN_EQ_THM]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ qmatch_goalsub_abbrev_tac`FUNPOW f n ([], (FOLDL g e z))`
  \\ qmatch_goalsub_abbrev_tac`_ = FUNPOW h n ([], (FOLDL k e z))`
  \\ `EVERY ($= (1600 - c) o LENGTH) z`
  by (
    rw[Abbr`z`]
    \\ irule divides_EVERY_LENGTH_chunks

  \\ `FOLDL g e z = FOLDL k e z`
  by (
    `EVERY (λls. LENGTH ls = c) z`
    by (
      rw[Abbr`z`, chunks_def]
    irule FOLDL_CONG
    \\ simp[Abbr`g`, Abbr`k`]
    \\ rw[]

    \\ irule Keccak_p_tabulate
    MAP2

  m``FOLDL _ _ _ = FOLDL _ _ _``

val cs = num_compset();
val () = extend_compset [
  Tys [``:state_array``],
  Defs [
    restrict_def,
    b2w_def,
    w2l_def,
    string_to_state_array_def,
    Lane_def,
    Plane_def,
    state_array_to_string_def,
    tabulate_string_def,
    Rnd_string_def,
    theta_c_def,
    theta_d_def,
    theta_def,
    rho_def |> SIMP_RULE std_ss [LEAST_DEF, o_DEF],
    pi_def,
    chi_def,
    rc_step_def,
    rc_def,
    iota_compute,
    Keccak_p_tabulate_def,
    chunks_def,
    pad10s1_def,
    sponge_def,
    Keccak_tabulate,
    Keccak_256_def],
  Extenders [
    listSimps.list_rws,
    rich_listSimps.add_rich_list_compset,
    pairLib.add_pair_compset,
    add_bit_compset,
    pred_setLib.add_pred_set_compset,
    add_combin_compset]
 ] cs

val thm = CBV_CONV cs ``Keccak_256 []``

val ctm = ``512``
val ftm = ``Keccak_p 24``
val btm = ``1600``
val padtm = ``pad10s1``
val rtm = ``1600 - ^ctm``
val Ntm = ``[]: bool list``
val dtm = ``256``
val Ptm = ``^Ntm ++ ^padtm ^rtm (LENGTH ^Ntm)``
val ntm = ``LENGTH ^Ptm DIV ^rtm``
val ctm = ``^btm - ^rtm``
val Pistm =  ``chunks ^rtm ^Ptm``
val S0tm = ``REPLICATE ^btm F``
val Stm = ``FOLDL (λSi Pi. ^ftm (MAP2 (λx y. x ⇎ y) Si (Pi ⧺ REPLICATE ^ctm F))) ^S0tm ^Pistm``

val chunksrw = CBV_CONV cs ``chunks 1088 (pad10s1 1088 0)``
val step1 = (SIMP_CONV (srw_ss()) [REPLICATE_compute, chunksrw]) Stm
val step1args = step1 |> concl |> rhs |> strip_comb |> #2
val n1tm = step1args |> el 1
val s1tm = step1args |> el 2
val atm = ``string_to_state_array ^s1tm``
val ltm = ``w2l ^atm.w``
val i0tm = ``12 + 2 * ^ltm - ^n1tm``
val i1tm = ``12 + 2 * ^ltm - 1``
val step2tm = ``Rnd ^atm ^i0tm``
val step2atm = ``theta ^atm``

*)

val _ = export_theory();
