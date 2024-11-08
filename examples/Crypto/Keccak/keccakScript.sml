open HolKernel Parse boolLib bossLib dep_rewrite
     bitLib reduceLib combinLib optionLib sptreeLib wordsLib computeLib;
open optionTheory pairTheory arithmeticTheory combinTheory listTheory
     rich_listTheory whileTheory bitTheory dividesTheory wordsTheory
     logrootTheory sptreeTheory;

(* The SHA-3 Standard: https://doi.org/10.6028/NIST.FIPS.202 *)

val _ = new_theory "keccak";

val _ = numLib.temp_prefer_num();

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
  w2l w = if 0 < w then LOG2 w else 0
End

Theorem bwl_table:
  MAP b2w [25; 50; 100; 200; 400; 800; 1600] = [1; 2; 4; 8; 16; 32; 64] ∧
  MAP w2l [1; 2; 4; 8; 16; 32; 64] = [0; 1; 2; 3; 4; 5; 6]
Proof
  EVAL_TAC
QED

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

Definition index_to_triple_def:
  index_to_triple w i = ((i DIV w) MOD 5, i DIV w DIV 5, i MOD w)
End

Definition triple_to_index_def:
  triple_to_index w (x, y, z) = x * w + 5 * y * w + z
End

Theorem triple_to_index_examples:
  triple_to_index 64 (4, 1, 2) = 578 ∧
  index_to_triple 64 766 = (1, 2, 62)
Proof
  EVAL_TAC
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

Theorem rho_xy_inj:
  rho_xy t1 = (x,y) ∧
  rho_xy t2 = (x,y) ∧
  t1 < 24 ∧ t2 < 24 ⇒
  t1 = t2
Proof
  disch_then(strip_assume_tac o SIMP_RULE(srw_ss())[NUMERAL_LESS_THM])
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ rpt (pop_assum mp_tac) \\ EVAL_TAC
  \\ rpt strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ rpt (pop_assum mp_tac) \\ EVAL_TAC
QED

Definition rho_def:
  rho a =
  a with A updated_by (λf. restrict a.w $ λ(x, y, z).
    if x = 0 ∧ y = 0 then f (x, y, z)
    else
      let t = LEAST t. rho_xy t = (x, y) in
      let tt = ((t + 1) * (t + 2)) DIV 2 in
      let ww = ((24 * 25) DIV 2) * a.w in
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

Theorem LENGTH_Keccak_p:
  LENGTH (Keccak_p n s) = LENGTH s DIV 25 * 25
Proof
  rw[Keccak_p_def, string_to_state_array_w, ADD1]
  \\ qmatch_goalsub_abbrev_tac`FUNPOW f (i1 - i0) (a, i0)`
  \\ qho_match_abbrev_tac`P (FUNPOW f (i1 - i0) (a, i0))`
  \\ irule FUNPOW_invariant
  \\ simp[Abbr`P`, Abbr`a`, string_to_state_array_w, b2w_def]
  \\ simp[Abbr`f`, FORALL_PROD]
QED

Definition sponge_def:
  sponge f b pad r N d =
  let P = N ++ pad r (LENGTH N) in
  let c = b - r in
  let Pis = chunks r P in
  let S0 = REPLICATE b F in
  let S = FOLDL (λSi Pi. f (MAP2 $<> Si (Pi ++ REPLICATE c F))) S0 Pis in
  let Z = FST $ WHILE
    (λ(Z, S). LENGTH Z < d)
    (λ(Z, S). (Z ++ (TAKE r S), f S))
    ([], S) in
  TAKE d Z
End

Definition pad10s1_def:
  pad10s1 x m =
  let j = (x * (m + 2) - m - 2) MOD x in
    [T] ++ REPLICATE j F ++ [T]
End

Theorem LENGTH_pad10s1:
  0 < x ⇒ ∃d. m + LENGTH (pad10s1 x m) = d * x
Proof
  Cases_on`x = 1` >> fs[]>>
  rw[pad10s1_def, ADD1, LEFT_ADD_DISTRIB]>>
  `2 * x + m * x = (2 + m) * x` by fs[]>>
  pop_assum SUBST_ALL_TAC>>
  DEP_REWRITE_TAC[MOD_COMPLEMENT]>>
  imp_res_tac DIVISION>>fs[]>>
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

Definition Keccak_224_def:
  Keccak_224 M = Keccak 448 M 224
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

Theorem state_array_to_string_compute:
  state_array_to_string a =
  GENLIST (λi.
    a.A ((i DIV a.w) MOD 5, i DIV a.w DIV 5, i MOD a.w))
  (5 * 5 * a.w)
Proof
  rw[state_array_to_string_def, Plane_def, Lane_def]
  \\ rw[LIST_EQ_REWRITE]
  \\ rw[EL_APPEND_EQN]
  \\ gs[LESS_DIV_EQ_ZERO]
  THENL
  let
    fun tac i =
      `x DIV a.w = ^(numSyntax.term_of_int i)` by gs[DIV_EQ_X]
      \\ gs[]
      \\ simp[Ntimes cvTheory.MOD_RECURSIVE i]
    fun loop i = if i = 25 then [] else tac i :: loop (i + 1)
  in
    loop 1
  end
QED

Theorem index_less:
  x < 5 ∧ y < 5 ∧ z < w ⇒ triple_to_index w (x, y, z) < 25 * w
Proof
  rw[triple_to_index_def]
  \\ `z + (w * x + 5 * (w * y)) = (x + 5 * y) * w + z` by simp[]
  \\ pop_assum SUBST_ALL_TAC
  \\ fs[NUMERAL_LESS_THM]
QED

Theorem index_to_triple_to_index[simp]:
  0 < w ==>
  triple_to_index w (index_to_triple w i) = i
Proof
  rw[index_to_triple_def, triple_to_index_def]
  \\ rw[DIV_DIV_DIV_MULT]
  \\ rewrite_tac[MULT_ASSOC]
  \\ `0 < 5 * w` by simp[]
  \\ drule_then(qspec_then`i`strip_assume_tac) DIVISION
  \\ qpat_x_assum`i = _`(fn th => CONV_TAC(RAND_CONV(REWR_CONV th)))
  \\ simp[]
  \\ simp[DIV_MOD_MOD_DIV]
  \\ qspec_then`w`mp_tac DIVISION
  \\ impl_tac >- rw[]
  \\ disch_then(qspec_then`i MOD (5 * w)`strip_assume_tac)
  \\ qpat_x_assum`i MOD _ = _`(fn th => CONV_TAC(RAND_CONV(REWR_CONV th)))
  \\ simp[]
  \\ qspecl_then[`5`,`w`]mp_tac MOD_MULT_MOD
  \\ simp[]
QED

Theorem triple_to_index_to_triple[simp]:
  x < 5 ∧ y < 5 ∧ z < w ⇒
  index_to_triple w (triple_to_index w (x,y,z)) = (x,y,z)
Proof
  rw[index_to_triple_def, triple_to_index_def]
  \\ `w * x + 5 * (w * y) = w * (x + 5 * y)` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ simp[ADD_DIV_RWT, LESS_DIV_EQ_ZERO]
  \\ once_rewrite_tac[MULT_COMM]
  \\ simp[MULT_DIV, LESS_DIV_EQ_ZERO]
QED

Theorem triple_to_index_inj:
  EVERY (λ(x,y,z). x < 5 ∧ y < 5 ∧ z < w) [t1; t2] ∧
  triple_to_index w t1 = triple_to_index w t2
  ⇒ t1 = t2
Proof
  PairCases_on`t1`
  \\ PairCases_on`t2`
  \\ simp[]
  \\ metis_tac[triple_to_index_to_triple, PAIR_EQ]
QED

Definition isFromList_def:
  isFromList t = ∃ls. t = fromList ls
End

Theorem isFromList_insert:
  isFromList t /\ k IN domain t ==>
  isFromList (insert k v t)
Proof
  rw[isFromList_def, PULL_EXISTS]
  \\ gs[domain_fromList]
  \\ gs[insert_fromList_IN_domain]
  \\ PROVE_TAC[]
QED

Definition bool_lookup_def:
  bool_lookup n t =
    case lookup n t of
    | NONE => F
    | SOME b => b
End

(* if y is fixed 0 *)
(* i -> (i DIV w, i MOD w) *)
(* (x, z) -> x * w + z *)

Definition theta_spt_def:
  theta_spt t =
  let w = b2w $ size t in
  let c = fromList (
    GENLIST (λi.
      (bool_lookup i t ≠
        (bool_lookup (i + 5 * w) t ≠
          (bool_lookup (i + 10 * w) t ≠
            (bool_lookup (i + 15 * w) t ≠
              (bool_lookup (i + 20 * w) t))))))
      (5 * w)) in
  let d = fromList (
    GENLIST (λi.
      (bool_lookup (((i DIV w + 4) MOD 5) * w + i MOD w) c ≠
       bool_lookup (((i DIV w + 1) MOD 5) * w + (i MOD w + PRE w) MOD w) c))
      (5 * w)) in
  mapi (λi b. b ≠ bool_lookup (((i DIV w) MOD 5) * w + i MOD w) d) t
End

Definition spt_to_state_array_def:
  spt_to_state_array t =
  let w = b2w $ size t in
  <| w := w
   ; A := restrict w $
          λp. case lookup (triple_to_index w p) t
              of SOME b => b | NONE => F
   |>
End

Definition sptfun_def:
  sptfun w t (x,y,z) ⇔
    x < 5 ∧ y < 5 ∧ z < w ∧
    case lookup (y * 5 * w + x * w + z) t
    of NONE => F | SOME b => b
End

Theorem theta_spt_fromList:
  w = b2w $ LENGTH s
  ⇒
  sptfun w (theta_spt (fromList s)) =
  (theta $ string_to_state_array s).A
Proof
  rw[FUN_EQ_THM, FORALL_PROD, theta_def, sptfun_def, restrict_def] \\
  rw[string_to_state_array_w]
  \\ qmatch_goalsub_rename_tac`(x,y,z)`
  \\ Cases_on`x < 5` \\ simp[]
  \\ Cases_on`y < 5` \\ simp[]
  \\ Cases_on`z < b2w $ LENGTH s` \\ simp[]
  \\ qmatch_assum_abbrev_tac`z < w`
  \\ rewrite_tac[theta_spt_def]
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`bool_lookup _ d`
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac`bool_lookup _ c`
  \\ strip_tac
  \\ rw[lookup_mapi]
  \\ reverse(rw[lookup_fromList])
  >- (
    `F` suffices_by simp[]
    \\ pop_assum mp_tac \\ simp[]
    \\ `triple_to_index w (x,y,z) < 25 * w` by metis_tac[index_less]
    \\ gs[triple_to_index_def]
    \\ `25 * w ≤ LENGTH s` suffices_by simp[]
    \\ simp[Abbr`w`, b2w_def]
    \\ `0 < 25` by simp[]
    \\ `LENGTH s = 25 * (LENGTH s DIV 25) + LENGTH s MOD 25`
        by metis_tac[DIVISION, MULT_COMM]
    \\ metis_tac[LESS_EQ_ADD])
  \\ rw[string_to_state_array_def, restrict_def]
  \\ rw[theta_d_def]
  \\ rw[theta_c_def, restrict_def]
  \\ reverse(rw[Abbr`d`, lookup_fromList, bool_lookup_def])
  >- (
    `F` suffices_by simp[]
    \\ pop_assum mp_tac \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`z + w * b`
    \\ `b < 5` by simp[Abbr`b`]
    \\ pop_assum mp_tac \\ simp[NUMERAL_LESS_THM]
    \\ rw[] \\ decide_tac )
  \\ rw[Abbr`c`]
  \\ reverse(rw[Once lookup_fromList])
  >- (
    `F` suffices_by simp[]
    \\ pop_assum mp_tac \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`z + w * b`
    \\ `b < 5` by simp[Abbr`b`]
    \\ pop_assum mp_tac \\ simp[NUMERAL_LESS_THM]
    \\ rw[] \\ decide_tac )
  \\ `25 * w ≤ LENGTH s`
  by (
    rw[Abbr`w`, b2w_def]
    \\ `0 < 25` by simp[]
    \\ `LENGTH s = 25 * (LENGTH s DIV 25) + LENGTH s MOD 25`
        by metis_tac[DIVISION, MULT_COMM]
    \\ metis_tac[LESS_EQ_ADD])
  \\ rw[bool_lookup_def]
  \\ rw[Once lookup_fromList]
  \\ rw[Once lookup_fromList]
  \\ rw[Once lookup_fromList]
  \\ rw[Once lookup_fromList]
  \\ rw[Once lookup_fromList]
  \\ reverse(rw[Once lookup_fromList])
  >- (
    `F` suffices_by simp[]
    \\ pop_assum mp_tac \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`w * q MOD 5 + r MOD w`
    \\ `q MOD 5 < 5` by simp[]
    \\ pop_assum mp_tac
    \\ `r MOD w < w` by simp[]
    \\ qmatch_goalsub_abbrev_tac`c < 5`
    \\ rw[NUMERAL_LESS_THM]
    \\ decide_tac )
  \\ rw[lookup_fromList]
  \\ qmatch_goalsub_abbrev_tac`(z + w * c) DIV w`
  \\ simp[ADD_DIV_RWT, MULT_DIV]
  \\ qmatch_asmsub_abbrev_tac`c = ((z + d) DIV w) MOD 5`
  \\ `d = w * (x + 5 * y)`
  by simp[Abbr`d`]
  \\ qpat_x_assum`Abbrev(d = _)`kall_tac
  \\ `(z + d) DIV w = (x + 5 * y) + z DIV w`
  by (
    pop_assum SUBST1_TAC
    \\ rewrite_tac[Once ADD_COMM]
    \\ rewrite_tac[Once MULT_COMM]
    \\ DEP_REWRITE_TAC[ADD_DIV_ADD_DIV]
    \\ simp[] )
  \\ pop_assum SUBST_ALL_TAC
  \\ `c = (x + z DIV w) MOD 5` by simp[Abbr`c`]
  \\ qpat_x_assum`Abbrev(c = _)`kall_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ qmatch_goalsub_abbrev_tac`w * c MOD 5`
  \\ rw[]
  \\ `z DIV w = 0` by metis_tac[LESS_DIV_EQ_ZERO]
  \\ fs[Abbr`c`,LEFT_ADD_DISTRIB]
QED

Theorem spt_to_state_array_sptfun:
  (spt_to_state_array t).A = sptfun (b2w $ size t) t
Proof
  rw[spt_to_state_array_def, FUN_EQ_THM, sptfun_def, FORALL_PROD]
  \\ rw[triple_to_index_def, restrict_def]
QED

Theorem spt_to_state_array_w[simp]:
  (spt_to_state_array t).w = b2w $ size t
Proof
  rw[spt_to_state_array_def]
QED

Theorem size_theta_spt[simp]:
  size (theta_spt t) = size t
Proof
  rw[theta_spt_def]
QED

Definition spt_to_string_def:
  spt_to_string t = MAP SND (toSortedAList t)
End

Theorem isFromList_theta_spt[simp]:
  isFromList t ⇒ isFromList (theta_spt t)
Proof
  rw[theta_spt_def]
  \\ rw[isFromList_def]
  \\ rw[fromList_fromAList]
  \\ rw[mapi_Alist]
  \\ qmatch_goalsub_abbrev_tac`MAP f (toAList t)`
  \\ qexists_tac`GENLIST (λi. THE (ALOOKUP (MAP f (toAList t)) i)) (size t)`
  \\ simp[]
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_fromAList]
  \\ simp[lookup_fromAList]
  \\ GEN_TAC \\ AP_THM_TAC
  \\ irule alistTheory.ALOOKUP_ALL_DISTINCT_PERM_same
  \\ simp[MAP_MAP_o]
  \\ `MAP (FST o f) = MAP FST`
  by rw[FUN_EQ_THM, Abbr`f`, LIST_EQ_REWRITE, EL_MAP]
  \\ conj_asm1_tac >- simp[ALL_DISTINCT_MAP_FST_toAList]
  \\ gs[]
  \\ simp[MAP_ZIP, LENGTH_COUNT_LIST]
  \\ reverse conj_asm2_tac
  >- (
    irule sortingTheory.PERM_ALL_DISTINCT
    \\ simp[set_MAP_FST_toAList_domain, all_distinct_count_list, MEM_COUNT_LIST]
    \\ fs[isFromList_def, domain_fromList] )
  \\ rw[pred_setTheory.EXTENSION, FORALL_PROD]
  \\ rw[EQ_IMP_THM]
  >- (
    rw[MEM_ZIP, LENGTH_COUNT_LIST]
    \\ qmatch_asmsub_rename_tac`MEM (k,v) _`
    \\ qexists_tac`k`
    \\ pop_assum mp_tac \\ simp[MEM_MAP, PULL_EXISTS, FORALL_PROD, MEM_toAList]
    \\ qx_genl_tac[`k1`,`v1`]
    \\ strip_tac
    \\ `k = k1` by fs[Abbr`f`]
    \\ gvs[]
    \\ `k ∈ domain t` by metis_tac[domain_lookup]
    \\ gs[isFromList_def, domain_fromList, EL_COUNT_LIST]
    \\ simp[alistTheory.ALOOKUP_MAP_2, Abbr`f`, LAMBDA_PROD]
    \\ qmatch_goalsub_abbrev_tac`OPTION_MAP f`
    \\ fs[]
    \\ simp[ALOOKUP_toAList] )
  \\ pop_assum mp_tac
  \\ simp[MEM_ZIP, LENGTH_COUNT_LIST, PULL_EXISTS, EL_COUNT_LIST]
  \\ qx_gen_tac`n` \\ strip_tac
  \\ gs[EL_COUNT_LIST]
  \\ rw[MEM_MAP, MEM_toAList, EXISTS_PROD]
  \\ simp[alistTheory.ALOOKUP_MAP_2, Abbr`f`, LAMBDA_PROD]
  \\ qmatch_goalsub_abbrev_tac`OPTION_MAP f` \\ fs[]
  \\ simp[ALOOKUP_toAList]
  \\ Cases_on`lookup n t` \\ simp[]
  \\ fs[lookup_NONE_domain]
  \\ gs[isFromList_def, domain_fromList]
QED

Theorem spt_to_state_array_to_string:
  isFromList t ∧ divides 25 (size t) ⇒
  state_array_to_string (spt_to_state_array t) =
  spt_to_string t
Proof
  rw[spt_to_state_array_def, state_array_to_string_compute, spt_to_string_def]
  \\ rw[GSYM GENLIST_EL_MAP]
  \\ simp[LIST_EQ_REWRITE]
  \\ conj_asm1_tac
  >- (
    gs[b2w_def]
    \\ pop_assum mp_tac \\ rw[divides_def]
    \\ simp[] )
  \\ rw[restrict_def]
  \\ qmatch_goalsub_abbrev_tac`triple_to_index w tr`
  \\ `tr = index_to_triple w x` by rw[index_to_triple_def]
  \\ rw[]
  \\ `x DIV w DIV 5 < 5`
  by ( simp[DIV_DIV_DIV_MULT] \\ simp[DIV_LT_X] )
  \\ simp[]
  \\ gs[isFromList_def, toSortedAList_fromList, lookup_fromList,
        EL_ZIP, LENGTH_COUNT_LIST]
QED

Theorem spt_to_state_array_fromList:
  spt_to_state_array (fromList ls) =
  string_to_state_array ls
Proof
  rw[spt_to_state_array_def, string_to_state_array_def, restrict_def,
     FUN_EQ_THM, FORALL_PROD]
  \\ qmatch_goalsub_rename_tac`(x,y,z)`
  \\ simp[triple_to_index_def, LEFT_ADD_DISTRIB]
  \\ simp[lookup_fromList]
  \\ rw[]
  \\ CCONTR_TAC \\ gs[]
  \\ qmatch_asmsub_abbrev_tac`x * w`
  \\ `triple_to_index w (x,y,z) < 25 * w`
  by ( irule index_less \\ rw[] )
  \\ fs[triple_to_index_def]
  \\ gs[Abbr`w`, b2w_def]
  \\ qmatch_asmsub_abbrev_tac`_ < b DIV 25`
  \\ qspec_then`25`mp_tac DIVISION \\ simp[]
  \\ qexists_tac`b`
  \\ strip_tac \\ gs[]
QED

Theorem theta_spt:
  isFromList t ⇒
  spt_to_state_array (theta_spt t) =
  (theta (spt_to_state_array t))
Proof
  rw[state_array_component_equality] \\
  rw[spt_to_state_array_sptfun] \\
  gs[isFromList_def] \\
  simp[theta_spt_fromList] \\
  simp[spt_to_state_array_fromList]
QED

Definition rho_spt_def:
  rho_spt a =
    let w = b2w $ size a in
    let ww = 300 * w in
    let (x,y,t,a') =
    WHILE (λ(x,y,t,a'). t ≤ 23)
      (λ(x,y,t,a'). (y, (2 * x + 3 * y) MOD 5, t + 1,
        let tt = (t + 1) * (t + 2) DIV 2 in
        SND $
        WHILE (λ(z,a'). z < w) (λ(z,a'). (z+1,
          insert (triple_to_index w (x,y,z))
            (bool_lookup (triple_to_index w (x,y,(z + ww - tt) MOD w)) a)
          a'))
          (0, a')))
      (1,0,0,a)
    in a'
End

Theorem rho_spt_invariants:
  isFromList t ⇒
    size (rho_spt t) = size t ∧
    isFromList (rho_spt t)
Proof
  simp[rho_spt_def]
  \\ qmatch_goalsub_abbrev_tac`WHILE P g x`
  \\ strip_tac
  \\ DEP_REWRITE_TAC[WHILE_FUNPOW]
  \\ `∀n. FST(SND(SND(FUNPOW g n x))) = n`
  by (
    Induct
    >- rw[Abbr`x`]
    \\ rw[FUNPOW_SUC]
    \\ qmatch_goalsub_abbrev_tac`g xx`
    \\ PairCases_on`xx`
    \\ simp[Abbr`g`])
  \\ conj_asm1_tac
  >- (
    qexists_tac`24`
    \\ first_x_assum(qspec_then`24`mp_tac)
    \\ qmatch_goalsub_abbrev_tac`P xx`
    \\ PairCases_on`xx`
    \\ rw[Abbr`P`] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- rw[]
  \\ gen_tac \\ strip_tac
  \\ qho_match_abbrev_tac`Q (FUNPOW g n x)`
  \\ `(λ(x,y,m,a). x < 5 ∧ y < 5 ∧ Q (x,y,m,a)) (FUNPOW g n x)`
  suffices_by rw[UNCURRY]
  \\ irule FUNPOW_invariant
  \\ simp[Abbr`Q`]
  \\ conj_tac >- simp[Abbr`x`]
  \\ qx_gen_tac`p`
  \\ PairCases_on`p`
  \\ simp[Abbr`g`]
  \\ strip_tac
  \\ qpat_x_assum`~P _`kall_tac
  \\ qmatch_goalsub_abbrev_tac`WHILE R h u`
  \\ DEP_REWRITE_TAC[WHILE_FUNPOW]
  \\ `∀n. FST (FUNPOW h n u) = n`
  by (
    Induct >- rw[Abbr`u`]
    \\ rw[FUNPOW_SUC]
    \\ rw[Abbr`h`, UNCURRY] )
  \\ conj_asm1_tac
  >- (
    qexists_tac`SUC (b2w (size t))`
    \\ rw[Abbr`R`, UNCURRY] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- rw[]
  \\ qx_gen_tac`m` \\ strip_tac
  \\ fs[]
  \\ `(λz. isFromList (SND z) ∧ size (SND z) = size t)
      (FUNPOW h m u)` suffices_by rw[]
  \\ drule_at (Pos (el 2)) FUNPOW_invariant_index
  \\ disch_then irule
  \\ simp[FORALL_PROD]
  \\ conj_tac >- (
    gs[Abbr`u`]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[Abbr`R`] )
  \\ qx_genl_tac[`q1`,`q2`]
  \\ strip_tac
  \\ simp[Abbr`h`]
  \\ qpat_x_assum`~R _`kall_tac
  \\ DEP_REWRITE_TAC[isFromList_insert]
  \\ simp[size_insert]
  \\ IF_CASES_TAC \\ simp[]
  \\ qpat_x_assum`_ ∉ domain _`mp_tac
  \\ qpat_x_assum`isFromList _`mp_tac
  \\ rw[isFromList_def, PULL_EXISTS, domain_fromList]
  \\ gs[size_fromList,Abbr`R`]
  \\ drule_at Any index_less
  \\ `25 * b2w (size t) ≤ size t` by (
    `0 < 25:num` by fs[]>>
    drule DIVISION>>
    disch_then(qspec_then`size t` assume_tac)>>
    simp[b2w_def])
  \\ metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem rho_spt_size[simp]:
  isFromList t ⇒ size (rho_spt t) = size t
Proof
  rw[rho_spt_invariants]
QED

Theorem rho_xy_cycle:
  ∀t. rho_xy t = rho_xy (t + 24)
Proof
  Induct \\ rw[]
  >- EVAL_TAC
  \\ simp[ADD]
QED

Theorem rho_xy_not_zero:
  ∀t. rho_xy t ≠ (0,0)
Proof
  completeInduct_on`t`
  \\ Cases_on`24 ≤ t`
  >- ( fs[LESS_EQ_EXISTS] \\ simp[GSYM rho_xy_cycle] )
  \\ fs[NOT_LESS_EQUAL]
  \\ pop_assum mp_tac
  \\ simp_tac(std_ss)[NUMERAL_LESS_THM]
  \\ strip_tac \\ rw[]
  \\ EVAL_TAC
QED

Theorem rho_xy_lt_5:
  ∀t x y. rho_xy t = (x,y) ⇒ x < 5 ∧ y < 5
Proof
  completeInduct_on`t`
  \\ Cases_on`24 ≤ t`
  >- (
    fs[PULL_FORALL, LESS_EQ_EXISTS, GSYM rho_xy_cycle]
    \\ rpt gen_tac \\ strip_tac
    \\ first_x_assum irule
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ rw[] )
  \\ fs[NOT_LESS_EQUAL]
  \\ pop_assum mp_tac
  \\ simp_tac(std_ss)[NUMERAL_LESS_THM]
  \\ strip_tac \\ gvs[]
  \\ EVAL_TAC \\ rw[]
QED

Theorem rho_spt:
  isFromList t ⇒
  spt_to_state_array (rho_spt t) =
  (rho (spt_to_state_array t))
Proof
  rw[state_array_component_equality]
  \\ `∃rs. rho_spt t = fromList rs`
  by metis_tac[isFromList_def, rho_spt_invariants]
  \\ simp[spt_to_state_array_fromList]
  \\ `∃ls. t = fromList ls` by metis_tac[isFromList_def]
  \\ simp[spt_to_state_array_fromList]
  \\ simp[rho_def, string_to_state_array_w]
  \\ simp[string_to_state_array_def]
  \\ simp[FUN_EQ_THM, FORALL_PROD]
  \\ simp[Once restrict_def]
  \\ simp[Once restrict_def, SimpRHS]
  \\ qx_genl_tac[`x`,`y`,`z`]
  \\ Cases_on`x < 5 ∧ y < 5` \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`z < w`
  \\ `LENGTH ls = LENGTH rs` by metis_tac[rho_spt_invariants, size_fromList]
  \\ Cases_on`z < w` \\ fs[]
  \\ qpat_x_assum`rho_spt _ = _`mp_tac
  \\ simp[rho_spt_def]
  \\ qmatch_goalsub_abbrev_tac`WHILE P f a`
  \\ simp[restrict_def]
  \\ DEP_REWRITE_TAC[WHILE_FUNPOW]
  \\ `∀n. FST(SND(SND(FUNPOW f n a))) = n`
  by (
    Induct >- rw[Abbr`a`]
    \\ rw[FUNPOW_SUC]
    \\ qmatch_goalsub_abbrev_tac`f xx`
    \\ PairCases_on`xx`
    \\ simp[Abbr`f`])
  \\ conj_asm1_tac
  >- ( qexists_tac`24` \\ simp[Abbr`P`, UNCURRY] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- rw[]
  \\ rpt strip_tac
  \\ `∀m b x y t u.
      FUNPOW f m b = (x,y,t,u) ∧
      rho_xy (FST(SND(SND b))) = (FST b, FST (SND b))
      ⇒ rho_xy t = (x,y)`
  by (
    ntac 2 gen_tac
    \\ qho_match_abbrev_tac`Q (FUNPOW f m b)`
    \\ irule FUNPOW_invariant
    \\ simp[Abbr`Q`]
    \\ conj_tac
    >- ( rw[] \\ gs[] )
    \\ simp[FORALL_PROD]
    \\ simp[Abbr`f`]
    \\ simp[GSYM ADD1] )
  \\ `∀m x y t u.
      FUNPOW f m a = (x,y,t,u) ⇒
      t = m ∧ rho_xy m = (x,y)`
  by (
    rpt gen_tac
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`m`,`a`]mp_tac)
    \\ first_x_assum(qspecl_then[`m`]mp_tac)
    \\ first_x_assum(qspecl_then[`m`]mp_tac)
    \\ simp[Abbr`a`] )
  \\ `∀m x y t u.
        FUNPOW f m a = (x,y,t,u)
        ⇒
        ∀z. z < w ⇒
            lookup (triple_to_index w (0,0,z)) u =
            lookup (triple_to_index w (0,0,z)) (SND(SND(SND a)))`
  by (
    gen_tac
    \\ qho_match_abbrev_tac`Q (FUNPOW f m a)`
    \\ irule FUNPOW_invariant_index
    \\ simp[Abbr`Q`, FORALL_PROD]
    \\ qexists_tac`λ(x,y,t,u). (x, y) ≠ (0,0)`
    \\ reverse(rw[])
    >- (
      qmatch_goalsub_abbrev_tac`_ xx`
      \\ PairCases_on`xx`
      \\ pop_assum mp_tac
      \\ rw[markerTheory.Abbrev_def]
      \\ qpat_x_assum`_ = FUNPOW _ _ _`(assume_tac o SYM)
      \\ first_assum drule
      \\ rpt strip_tac
      \\ metis_tac[rho_xy_not_zero])
    \\ qpat_x_assum`f _ = _`mp_tac
    \\ simp[Abbr`f`] \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`WHILE Q g`
    \\ DEP_REWRITE_TAC[WHILE_FUNPOW]
    \\ `∀n a. FST(FUNPOW g n a) = (FST a + n)`
    by (
      Induct >- rw[]
      \\ rw[FUNPOW_SUC, ADD1]
      \\ qmatch_goalsub_abbrev_tac`g xx`
      \\ `FST (g xx) = FST xx + 1` suffices_by (
        qmatch_asmsub_rename_tac`xx = FUNPOW g _ c`
        \\ first_x_assum(qspec_then`c`mp_tac)
        \\ simp[])
      \\ simp[Abbr`g`, UNCURRY] )
    \\ conj_asm1_tac >- ( qexists_tac`w` \\ simp[Abbr`Q`, UNCURRY])
    \\ numLib.LEAST_ELIM_TAC
    \\ rw[] \\ fs[]
    \\ first_assum $ drule_then(CHANGED_TAC o SUBST1_TAC o SYM)
    \\ qmatch_goalsub_rename_tac`FUNPOW g p (0, j)`
    \\ qmatch_goalsub_abbrev_tac`SND pp`
    \\ qho_match_abbrev_tac`QQ pp`
    \\ qunabbrev_tac`pp`
    \\ irule FUNPOW_invariant
    \\ simp[Abbr`QQ`]
    \\ simp[FORALL_PROD]
    \\ rpt gen_tac \\ disch_then (SUBST1_TAC o SYM)
    \\ simp[Abbr`g`]
    \\ qmatch_goalsub_abbrev_tac`insert kk vv _`
    \\ rw[lookup_insert]
    \\ pop_assum mp_tac
    \\ rw[triple_to_index_def]
    \\ qpat_x_assum`_ < w` mp_tac
    \\ qmatch_goalsub_rename_tac`c1 * w`
    \\ Cases_on`c1 <> 0`
    >- ( Cases_on`c1` \\ fs[MULT_SUC] )
    \\ fs[]
    \\ qmatch_goalsub_rename_tac`c2 * w`
    \\ Cases_on`c2 <> 0`
    >- ( Cases_on`c2` \\ fs[MULT_SUC] )
    \\ fs[])
  \\ Cases_on`x = 0 ∧ y = 0` \\ simp[]
  >- (
    Cases_on`FUNPOW f n a`
    \\ PairCases_on`r` \\ fs[] \\ rw[]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ simp[triple_to_index_def, lookup_fromList, Abbr`a`]
    \\ rw[]
    \\ rfs[Abbr`w`, b2w_def, X_LT_DIV] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[rho_xy_exists]
  \\ rw[]
  \\ Cases_on`FUNPOW f n a`
  \\ PairCases_on`r`
  \\ fs[] \\ rw[]
  \\ qpat_assum`∀m x y t u. _ ⇒ _ ∧ _` drule
  \\ strip_tac \\ rw[]
  \\ qmatch_asmsub_rename_tac`rho_xy i = (x,y)`
  \\ `23 < n` by fs[Abbr`P`]
  \\ qmatch_goalsub_abbrev_tac`EL ti rs`
  \\ `ti = triple_to_index w (x,y,z)`
  by simp[triple_to_index_def, Abbr`ti`]
  \\ pop_assum SUBST1_TAC \\ qunabbrev_tac`ti`
  \\ qmatch_goalsub_abbrev_tac`EL ti ls`
  \\ qabbrev_tac`ii = ((i + 1) * (i + 2) DIV 2)`
  \\ `w * (SUC ii DIV w) = SUC ii - SUC ii MOD w`
  by (
    qspec_then`w`mp_tac DIVISION
    \\ impl_tac >- simp[]
    \\ disch_then(qspec_then`SUC ii`mp_tac)
    \\ qmatch_goalsub_abbrev_tac`sdw * w`
    \\ rw[] )
  \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ + zz MOD w`
  \\ `ti = triple_to_index w (x,y,zz MOD w)`
  by simp[Abbr`ti`, triple_to_index_def]
  \\ pop_assum SUBST1_TAC \\ qunabbrev_tac`ti`
  \\ `i < 24`
  by (
    `¬(x = 0 ∧ y = 0)` by metis_tac[]
    \\ pop_assum (mp_then Any mp_tac rho_xy_exists)
    \\ rw[]
    \\ `¬(t < i)` by metis_tac[]
    \\ decide_tac )
  \\ `i < n` by decide_tac
  \\ `n = 24`
  by (
    `n ≤ 24` suffices_by decide_tac
    \\ CCONTR_TAC
    \\ `24 < n` by decide_tac
    \\ `P (FUNPOW f 24 a)` by metis_tac[]
    \\ `FST (SND (SND (FUNPOW f 24 a))) = 24` by metis_tac[]
    \\ fs[Abbr`P`, UNCURRY] )
  \\ BasicProvers.VAR_EQ_TAC
  \\ qpat_x_assum`rho_xy 24 = _`mp_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ rw[] \\ fs[] \\ rw[]
  \\ `∀j l x y z zz ii.
      rho_xy l = (x,y) ∧ z < w ∧ l < j ∧ j ≤ 24 ∧
      zz = 300 * w + z - ii ∧
      ii = ((l + 1) * (l + 2)) DIV 2
      ⇒
      lookup (triple_to_index w (x,y,z)) (SND(SND(SND(FUNPOW f j a)))) =
      lookup (triple_to_index w (x,y,zz MOD w)) (fromList ls)`
  by (
    Induct_on`j` \\ simp[]
    \\ simp[Abbr`f`, FUNPOW_SUC, UNCURRY]
    \\ qmatch_goalsub_abbrev_tac`FUNPOW f`
    \\ Cases_on`FUNPOW f j a`
    \\ PairCases_on`r` \\ fs[]
    \\ `r1 = j ∧ rho_xy j = (q,r0)` by metis_tac[]
    \\ fs[] \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`WHILE _ g`
    \\ `∀m x. FST (FUNPOW g m x) = m + FST x`
    by (
      Induct \\ rw[FUNPOW_SUC]
      \\ rw[Abbr`g`, UNCURRY] )
    \\ Cases_on`l < j`
    >- (
      first_x_assum(drule_then drule)
      \\ simp[]
      \\ disch_then(SUBST1_TAC o SYM)
      \\ `(q,r0) ≠ rho_xy l`
      by (
        CCONTR_TAC \\ rfs[]
        \\ `j < 24 ∧ l < 24` by decide_tac
        \\ `j = l` by metis_tac[rho_xy_inj]
        \\ decide_tac )
      \\ DEP_REWRITE_TAC[WHILE_FUNPOW]
      \\ conj_asm1_tac >- ( qexists_tac`w` \\ rw[UNCURRY] )
      \\ qmatch_goalsub_abbrev_tac`FUNPOW g m`
      \\ `m ≤ w`
      by (
        simp[Abbr`m`]
        \\ numLib.LEAST_ELIM_TAC
        \\ simp[UNCURRY] \\ rw[]
        \\ CCONTR_TAC
        \\ `w < n` by decide_tac
        \\ `w < w` by metis_tac[]
        \\ fs[] )
      \\ qpat_x_assum`Abbrev (m = _)`kall_tac
      \\ Induct_on`m` \\ simp[]
      \\ rw[FUNPOW_SUC]
      \\ rw[Abbr`g`, UNCURRY]
      \\ qmatch_goalsub_abbrev_tac`FUNPOW g`
      \\ simp[lookup_insert] \\ rw[]
      \\ first_assum(mp_then Any mp_tac triple_to_index_inj)
      \\ simp[] \\ rfs[]
      \\ `rho_xy j = (q,r0)` by metis_tac[]
      \\ imp_res_tac rho_xy_lt_5
      \\ simp[] )
    \\ `j = l` by decide_tac
    \\ fs[] \\ rw[]
    \\ DEP_REWRITE_TAC[WHILE_FUNPOW]
    \\ conj_asm1_tac >- ( qexists_tac`w` \\ rw[UNCURRY] )
    \\ qmatch_goalsub_abbrev_tac`FUNPOW g m`
    \\ `m = w`
    by (
      simp[Abbr`m`]
      \\ numLib.LEAST_ELIM_TAC
      \\ simp[UNCURRY] \\ rw[]
      \\ CCONTR_TAC
      \\ `w < n` by decide_tac
      \\ `w < w` by metis_tac[]
      \\ fs[] )
    \\ rw[]
    \\ qmatch_goalsub_rename_tac`(t,u,v)`
    \\ qho_match_abbrev_tac`_ = lookup (triple_to_index m (t,u,h v j)) _`
    \\ fs[]
    \\ `∀i z. i ≤ m ∧ z < m ⇒
        lookup (triple_to_index m (t,u,z)) (SND (FUNPOW g i (0,r2))) =
        lookup (triple_to_index m (t,u,
          if i ≤ z then z else h z j))
          if i ≤ z then r2 else fromList ls`
    by (
      Induct \\ simp[]
      \\ simp[FUNPOW_SUC]
      \\ qx_gen_tac`p`
      \\ qmatch_goalsub_rename_tac`SUC q ≤ m`
      \\ strip_tac
      \\ simp[Abbr`g`, UNCURRY]
      \\ qmatch_goalsub_abbrev_tac`FUNPOW g`
      \\ imp_res_tac rho_xy_lt_5
      \\ rw[]
      >- (
        Cases_on`q = p` \\ fs[]
        \\ simp[lookup_insert]
        \\ IF_CASES_TAC
        >- (
          first_x_assum (mp_then Any mp_tac triple_to_index_inj)
          \\ simp[])
        \\ rw[] )
      \\ fs[NOT_LESS_EQUAL]
      \\ simp[lookup_insert]
      \\ reverse(Cases_on`p=q` \\ simp[])
      >- (
        rw[bool_lookup_def]
        \\ first_x_assum (mp_then Any mp_tac triple_to_index_inj)
        \\ simp[])
      \\ rw[bool_lookup_def]
      \\ rw[lookup_fromList]
      \\ `h p j < m` by simp[Abbr`h`]
      \\ `triple_to_index m (t, u, h p j) < 25 * m`
      by metis_tac[index_less]
      \\ `25 * m ≤ LENGTH rs` suffices_by decide_tac
      \\ qpat_x_assum`Abbrev(m = $LEAST _)`kall_tac
      \\ qunabbrev_tac`m`
      \\ rewrite_tac[b2w_def]
      \\ qspec_then`25`mp_tac DIVISION
      \\ impl_tac >- rw[]
      \\ disch_then(qspec_then`LENGTH rs`mp_tac)
      \\ simp[])
    \\ first_x_assum(qspecl_then[`m`,`v`]mp_tac)
    \\ simp[])
  \\ first_x_assum(qspec_then`24`mp_tac)
  \\ simp[]
  \\ disch_then(qspec_then`i`mp_tac)
  \\ simp[lookup_fromList]
  \\ disch_then drule
  \\ simp[]
  \\ rw[]
  \\ `triple_to_index w (x,y,z) < 25 * w` by metis_tac[index_less]
  \\ fs[Abbr`w`, b2w_def]
  \\ qmatch_asmsub_abbrev_tac`25 * (l DIV 25)`
  \\ qspec_then`25`mp_tac DIVISION
  \\ simp[]
  \\ disch_then(qspec_then`l`mp_tac)
  \\ simp[]
QED

Definition pi_spt_def:
  pi_spt a =
  let w = b2w (size a) in
  fromList (GENLIST (λi.
    let (x, y, z) = index_to_triple w i in
      bool_lookup (triple_to_index w ((x + 3 * y) MOD 5, x, z)) a
  ) (size a))
End

Theorem size_pi_spt[simp]:
  size (pi_spt a) = size a
Proof
  rw[pi_spt_def]
QED

Theorem pi_spt:
  isFromList t ⇒
  spt_to_state_array (pi_spt t) =
  pi (spt_to_state_array t)
Proof
  rw[state_array_component_equality, isFromList_def]
  \\ rw[pi_spt_def]
  \\ rw[spt_to_state_array_fromList]
  \\ rw[pi_def, string_to_state_array_def]
  \\ simp[restrict_def, FORALL_PROD, FUN_EQ_THM]
  \\ qx_genl_tac[`x`,`y`,`z`]
  \\ qmatch_goalsub_abbrev_tac`z < w`
  \\ Cases_on`x < 5 ∧ y < 5 ∧ z < w` \\ fs[]
  \\ mp_tac index_less
  \\ impl_tac >- simp[]
  \\ simp[Once triple_to_index_def]
  \\ `25 * w ≤ LENGTH ls`
  by (
    simp[Abbr`w`, b2w_def]
    \\ `0 < 25` by simp[]
    \\ drule_then(qspec_then`LENGTH ls`mp_tac) DIVISION
    \\ simp[] )
  \\ simp[lookup_fromList, bool_lookup_def]
  \\ `z + w * (x + 5 * y) = triple_to_index w (x,y,z)` by simp[triple_to_index_def]
  \\ pop_assum SUBST1_TAC
  \\ simp[]
  \\ strip_tac
  \\ rw[]
  >- rw[triple_to_index_def, LEFT_ADD_DISTRIB]
  \\ `triple_to_index w ((x + 3 * y) MOD 5,x,z) < 25 * w`
  by ( irule index_less \\ simp[] )
  \\ fs[]
QED

Definition chi_spt_def:
  chi_spt a =
    let w = b2w (size a) in
    mapi (λk v.
      let (x,y,z) = index_to_triple w k in
      let v1 = bool_lookup (triple_to_index w ((x + 1) MOD 5, y, z)) a in
      let v2 = bool_lookup (triple_to_index w ((x + 2) MOD 5, y, z)) a in
      v ≠ (¬v1 ∧ v2)) a
End

Theorem chi_spt:
  isFromList t ⇒
  spt_to_state_array (chi_spt t) = chi (spt_to_state_array t)
Proof
  rw[isFromList_def, chi_spt_def]
  \\ simp[size_fromList, mapi_fromList]
  \\ qmatch_goalsub_abbrev_tac`triple_to_index w`
  \\ simp[spt_to_state_array_fromList]
  \\ rw[state_array_component_equality, string_to_state_array_w]
  \\ rw[chi_def, string_to_state_array_def]
  \\ `25 * w ≤ LENGTH ls`
  by (
    simp[Abbr`w`, b2w_def]
    \\ `0 < 25` by simp[]
    \\ drule_then(qspec_then`LENGTH ls`mp_tac) DIVISION
    \\ simp[] )
  \\ simp[lookup_fromList, bool_lookup_def]
  \\ simp[FUN_EQ_THM, FORALL_PROD, restrict_def]
  \\ qx_genl_tac[`x`,`y`,`z`]
  \\ Cases_on`x < 5 ∧ y < 5 ∧ z < w` \\ fs[]
  \\ DEP_REWRITE_TAC[indexedListsTheory.EL_MAPi]
  \\ mp_tac index_less
  \\ simp[Once triple_to_index_def]
  \\ simp[index_to_triple_def]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`triple_to_index w (x1,y1,z)`
  \\ qmatch_goalsub_abbrev_tac`¬EL t1 ls ∧ EL t2 ls`
  \\ `x1 < 5 ∧ y1 < 5`
  by simp[Abbr`x1`, Abbr`y1`, DIV_LT_X]
  \\ `triple_to_index w (x1,y1,z) < 25 * w`
  by simp[index_less]
  \\ simp[]
  \\ `triple_to_index w (x1,y1,z) = t1`
  by (
    rw[triple_to_index_def, Abbr`t1`, Abbr`y1`, Abbr`x1`]
    \\ qmatch_goalsub_abbrev_tac`5 * (w * (q DIV 5))`
    \\ `5 * (w * (q DIV 5)) = w * (5 * (q DIV 5))` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ simp[GSYM LEFT_ADD_DISTRIB]
    \\ `q = x + 5 * y`
    by (
      simp[Abbr`q`]
      \\ simp[ADD_DIV_RWT, LESS_DIV_EQ_ZERO]
      \\ once_rewrite_tac[MULT_COMM]
      \\ simp[MULT_DIV] )
    \\ fs[Abbr`q`, LESS_DIV_EQ_ZERO])
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`triple_to_index w (x2,y1,z)`
  \\ `x2 < 5` by simp[Abbr`x2`, DIV_LT_X]
  \\ `triple_to_index w (x2,y1,z) < 25 * w`
  by simp[index_less]
  \\ simp[]
  \\ `triple_to_index w (x2,y1,z) = t2` suffices_by simp[]
  \\ rw[triple_to_index_def, Abbr`t2`, Abbr`y1`, Abbr`x2`]
  \\ qmatch_goalsub_abbrev_tac`5 * (w * (q DIV 5))`
  \\ `5 * (w * (q DIV 5)) = w * (5 * (q DIV 5))` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ simp[GSYM LEFT_ADD_DISTRIB]
  \\ `q = x + 5 * y`
  by (
    simp[Abbr`q`]
    \\ simp[ADD_DIV_RWT, LESS_DIV_EQ_ZERO]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ fs[Abbr`q`, LESS_DIV_EQ_ZERO]
QED

Definition iota_spt_def:
  iota_spt a i =
  let w = b2w (size a) in
  mapi (λk v.
    let (x,y,z) = index_to_triple w k in
    if x = 0 ∧ y = 0 then
      let l = w2l w in
      let RCz = ((z = 2 ** LOG2 (SUC z) - 1 ∧ LOG2 (SUC z) ≤ l) ∧
                 rc (LOG2 (SUC z) + 7 * i)) in
        bool_lookup (triple_to_index w (0,0,z)) a ≠ RCz
    else v) a
End

Theorem iota_spt:
  isFromList t ⇒
  spt_to_state_array (iota_spt t i) =
  iota (spt_to_state_array t) i
Proof
  rw[isFromList_def, iota_spt_def]
  \\ rw[mapi_fromList, spt_to_state_array_fromList]
  \\ rw[state_array_component_equality]
  \\ rw[string_to_state_array_def]
  \\ rw[iota_compute]
  \\ simp[FUN_EQ_THM, FORALL_PROD, restrict_def]
  \\ qx_genl_tac[`x`,`y`,`z`]
  \\ qmatch_goalsub_abbrev_tac`z < w`
  \\ `25 * w ≤ LENGTH ls`
  by (
    simp[Abbr`w`, b2w_def]
    \\ `0 < 25` by simp[]
    \\ drule_then(qspec_then`LENGTH ls`mp_tac) DIVISION
    \\ simp[] )
  \\ Cases_on`x < 5 ∧ y < 5 ∧ z < w` \\ fs[]
  \\ DEP_REWRITE_TAC[indexedListsTheory.EL_MAPi]
  \\ mp_tac index_less
  \\ simp[Once triple_to_index_def]
  \\ simp[index_to_triple_def]
  \\ strip_tac
  \\ simp[Once triple_to_index_def]
  \\ simp[lookup_fromList, bool_lookup_def]
  \\ qmatch_goalsub_abbrev_tac`x1 = 0 ∧ y1 = 0`
  \\ `x1 = x ∧ y1 = y` suffices_by rw[]
  \\ simp[Abbr`x1`, Abbr`y1`]
  \\ simp[ADD_DIV_RWT, LESS_DIV_EQ_ZERO]
  \\ once_rewrite_tac[MULT_COMM]
  \\ simp[MULT_DIV, LESS_DIV_EQ_ZERO]
QED

Definition Rnd_spt_def:
  Rnd_spt t =
  iota_spt (chi_spt (pi_spt (rho_spt (theta_spt t))))
End

Theorem isFromList_chi_spt[simp]:
  isFromList t ⇒ isFromList (chi_spt t)
Proof
  rw[chi_spt_def, isFromList_def]
  \\ rw[mapi_fromList]
  \\ metis_tac[]
QED

Theorem isFromList_pi_spt[simp]:
  isFromList (pi_spt t)
Proof
  rw[pi_spt_def, isFromList_def]
  \\ metis_tac[]
QED

Theorem isFromList_rho_spt[simp]:
  isFromList t ⇒ isFromList (rho_spt t)
Proof
  metis_tac[rho_spt_invariants]
QED

Theorem isFromList_iota_spt[simp]:
  isFromList t ⇒ isFromList (iota_spt t i)
Proof
  rw[iota_spt_def, isFromList_def]
  \\ rw[mapi_fromList]
  \\ metis_tac[]
QED

Theorem Rnd_spt:
  isFromList t ⇒
  spt_to_state_array (Rnd_spt t i) =
  Rnd (spt_to_state_array t) i
Proof
  rw[Rnd_spt_def, Rnd_def]
  \\ rw[iota_spt, chi_spt, pi_spt, rho_spt, theta_spt]
QED

Theorem isFromList_Rnd_spt[simp]:
  isFromList t ⇒ isFromList (Rnd_spt t i)
Proof
  rw[Rnd_spt_def]
QED

Theorem size_iota_spt[simp]:
  size (iota_spt t i) = size t
Proof
  rw[iota_spt_def]
QED

Theorem size_chi_spt[simp]:
  size (chi_spt t) = size t
Proof
  rw[chi_spt_def]
QED

Theorem size_rho_spt[simp]:
  isFromList t ⇒ size (rho_spt t) = size t
Proof
  rw[rho_spt_invariants]
QED


Theorem size_Rnd_spt[simp]:
  isFromList t ⇒
  size (Rnd_spt t i) = size t
Proof
  rw[Rnd_spt_def]
QED

Theorem Keccak_p_spt:
  divides 25 (LENGTH s) ⇒
  Keccak_p n s =
  let w = b2w (LENGTH s) in
  let l = w2l w in
  let i0 = 12 + 2 * l - n in
  let i1 = 12 + 2 * l - 1 in
  let t = FST (FUNPOW (λ(t,i). (Rnd_spt t i, SUC i)) (SUC i1 - i0)
            (fromList s, i0)) in
  spt_to_string t
Proof
  rw[Keccak_p_def, string_to_state_array_w]
  \\ qmatch_goalsub_abbrev_tac`(_, 2 * w2l w + 12 - n)`
  \\ qmatch_goalsub_abbrev_tac`_, i0`
  \\ qmatch_goalsub_abbrev_tac`i1 - i0`
  \\ qmatch_goalsub_abbrev_tac`FUNPOW f1 m (string_to_state_array _,_)`
  \\ qmatch_goalsub_abbrev_tac`FUNPOW f2 m (fromList _,_)`
  \\ DEP_REWRITE_TAC[GSYM spt_to_state_array_to_string]
  \\ `∀x j s.
        FST x = (fromList s) ⇒
        let t = (FST (FUNPOW f2 j x)) in
        isFromList t ∧ size t = LENGTH s`
  by (
    ntac 2 gen_tac
    \\ qho_match_abbrev_tac`Q (FUNPOW f2 j x)`
    \\ irule FUNPOW_invariant
    \\ simp[Abbr`Q`]
    \\ simp[Once isFromList_def]
    \\ conj_tac >- PROVE_TAC[]
    \\ simp[FORALL_PROD, Abbr`f2`]
    \\ rpt gen_tac \\ strip_tac
    \\ gen_tac \\ first_x_assum (disch_then o mp_then Any mp_tac)
    \\ simp[])
  \\ first_assum(qspec_then`(fromList s, i0)`mp_tac)
  \\ simp_tac(srw_ss())[]
  \\ disch_then(qspecl_then[`m`,`s`]mp_tac)
  \\ impl_tac >- simp[]
  \\ simp_tac(srw_ss() ++ boolSimps.LET_ss)[]
  \\ simp[] \\ strip_tac
  \\ `∀x y j s.
        FST y = (fromList s) ∧
        FST x = (string_to_state_array s) ∧
        SND x = SND y
        ⇒
        FST (FUNPOW f1 j x) =
        spt_to_state_array (FST (FUNPOW f2 j y)) ∧
        SND (FUNPOW f1 j x) = SND (FUNPOW f2 j y)`
  by (
    Induct_on`j` \\ simp[]
    >- simp[spt_to_state_array_fromList]
    \\ simp[FUNPOW_SUC]
    \\ rpt gen_tac \\ strip_tac
    \\ first_x_assum (drule_then drule)
    \\ rw[Abbr`f1`, Abbr`f2`, UNCURRY]
    \\ DEP_REWRITE_TAC[Rnd_spt]
    \\ fs[]
    \\ metis_tac[])
  \\ first_x_assum(qspecl_then[
       `(string_to_state_array s, i0)`,
       `(fromList s, i0)`
     ] mp_tac)
  \\ simp[]
QED

Theorem state_array_to_string_remove_restrict:
  state_array_to_string <| w := w0; A := restrict w0 f |> =
  state_array_to_string <| w := w0; A := f |>
Proof
  rw[state_array_to_string_compute, restrict_def, LIST_EQ_REWRITE]
  \\ rw[DIV_LT_X]
QED

Definition Keccak_p_spt_def:
  Keccak_p_spt n s =
  let w = b2w (LENGTH s); l = w2l w; i0 = 12 + 2 * l - n; i1 = 12 + 2 * l - 1 in
  let t = FST (FUNPOW (λ(t, i). (Rnd_spt t i, SUC i)) (SUC i1 - i0)
               (fromList s, i0)) in
    spt_to_string t
End

Theorem Keccak_p_spt_eq:
  divides 25 (LENGTH s) ⇒
  Keccak_p_spt n s = Keccak_p n s
Proof
  rw[Keccak_p_spt_def, Keccak_p_spt]
QED

Theorem Keccak_spt:
  ∀c. c < 1600 ⇒
  Keccak c = sponge (Keccak_p_spt 24) 1600 pad10s1 (1600 - c)
Proof
  gen_tac \\ strip_tac
  \\ simp[Keccak_def, sponge_def, FUN_EQ_THM]
  \\ qx_genl_tac[`m`,`d`]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ qmatch_goalsub_abbrev_tac`WHILE P f1 ([], FOLDL f2 e xs)`
  \\ qmatch_goalsub_abbrev_tac`_ = WHILE P f3 ([], FOLDL f4 e xs)`
  \\ `FOLDL f2 e xs = FOLDL f4 e xs ∧ (λa. LENGTH a = 1600) (FOLDL f4 e xs)`
  by (
    irule FOLDL_CONG_invariant
    \\ simp[Abbr`f2`, Abbr`f4`]
    \\ conj_tac >- simp[Abbr`e`, LENGTH_REPLICATE]
    \\ qx_gen_tac`y`
    \\ qx_gen_tac`a`
    \\ strip_tac
    \\ DEP_REWRITE_TAC[Keccak_p_spt_eq]
    \\ simp[LENGTH_Keccak_p]
    \\ `1600 <= LENGTH y + c` suffices_by (
      simp[MIN_DEF, LESS_OR_EQ]
      \\ strip_tac \\ rw[] \\ EVAL_TAC )
    \\ fs[Abbr`xs`]
    \\ `∃d. LENGTH m + LENGTH (pad10s1 (1600 - c) (LENGTH m)) = d * (1600 - c)`
    by ( irule LENGTH_pad10s1 \\ simp[] )
    \\ qmatch_asmsub_abbrev_tac`chunks (1600 - c) ls`
    \\ `divides (1600 - c) (LENGTH ls)` by simp[Abbr`ls`]
    \\ Cases_on`ls = []`
    >- ( fs[Abbr`ls`] \\ fs[pad10s1_def] )
    \\ drule_then drule divides_EVERY_LENGTH_chunks
    \\ simp[EVERY_MEM]
    \\ disch_then drule
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[])
  \\ simp[]
  \\ DEP_REWRITE_TAC[WHILE_FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`FUNPOW f1 _ ([], ls)`
  \\ `∀n z l.
        LENGTH l = 1600 ⇒
        LENGTH (FST (FUNPOW f1 n (z,l))) = n * (1600 - c) + LENGTH z ∧
        LENGTH (SND (FUNPOW f1 n (z,l))) = 1600`
  by (
    Induct \\ simp[FUNPOW_SUC]
    \\ rw[Abbr`f1`, UNCURRY, LENGTH_TAKE_EQ, MULT]
    \\ simp[LENGTH_Keccak_p])
  \\ `∀n z l.
        LENGTH l = 1600 ⇒
        LENGTH (FST (FUNPOW f3 n (z,l))) = n * (1600 - c) + LENGTH z ∧
        LENGTH (SND (FUNPOW f3 n (z,l))) = 1600`
  by (
    Induct \\ simp[FUNPOW_SUC]
    \\ rw[Abbr`f3`, UNCURRY, LENGTH_TAKE_EQ, MULT]
    \\ DEP_REWRITE_TAC[Keccak_p_spt_eq]
    \\ simp[LENGTH_Keccak_p]
    \\ EVAL_TAC)
  \\ `∀n. P (FUNPOW f3 n ([],ls)) = P (FUNPOW f1 n ([], ls))`
  by ( rw[Abbr`P`, UNCURRY] \\ gs[] )
  \\ simp[]
  \\ conj_asm1_tac
  >- ( qexists_tac`d` \\ rw[Abbr`P`, UNCURRY] \\ gs[] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- simp[]
  \\ gen_tac \\ strip_tac
  \\ `∀n x.
      LENGTH (SND x) = 1600 ⇒
      FUNPOW f1 n x = FUNPOW f3 n x ∧
      LENGTH (SND (FUNPOW f3 n x)) = 1600 `
  by (
    Induct \\ simp[]
    \\ simp[FUNPOW_SUC]
    \\ ntac 2 strip_tac
    \\ simp[Abbr`f1`, Abbr`f3`]
    \\ simp[UNCURRY]
    \\ reverse conj_asm1_tac
    >- (
      pop_assum (SUBST1_TAC o SYM)
      \\ simp[LENGTH_Keccak_p])
    \\ irule (GSYM Keccak_p_spt_eq)
    \\ simp[]
    \\ EVAL_TAC )
  \\ fs[]
QED

Theorem Keccak_512_spt =
  Keccak_spt |> Q.SPEC`512` |> SIMP_RULE std_ss []

Theorem Keccak_448_spt =
  Keccak_spt |> Q.SPEC`448` |> SIMP_RULE std_ss []

Theorem triple_to_index_1600 =
  List.tabulate(5, (fn x =>
    List.tabulate(5, (fn y =>
      List.tabulate(64, (fn z =>
        EVAL``triple_to_index 64 (
                 ^(numLib.term_of_int x),
                 ^(numLib.term_of_int y),
                 ^(numLib.term_of_int z)
              )``))))))
  |> List.concat
  |> List.concat
  |> LIST_CONJ

Theorem index_to_triple_1600 =
  List.tabulate(1600, fn i =>
    EVAL``index_to_triple 64 ^(numLib.term_of_int i)``)
  |> LIST_CONJ

Theorem triple_to_index_25 =
  List.tabulate(5, (fn x =>
    List.tabulate(5, (fn y =>
      List.tabulate(1, (fn z =>
        EVAL``triple_to_index 1 (
                 ^(numLib.term_of_int x),
                 ^(numLib.term_of_int y),
                 ^(numLib.term_of_int z)
              )``))))))
  |> List.concat
  |> List.concat
  |> LIST_CONJ

Theorem index_to_triple_25 =
  List.tabulate(25, fn i =>
    EVAL``index_to_triple 1 ^(numLib.term_of_int i)``)
  |> LIST_CONJ

Theorem triple_to_index_100 =
  List.tabulate(5, (fn x =>
    List.tabulate(5, (fn y =>
      List.tabulate(4, (fn z =>
        EVAL``triple_to_index 4 (
                 ^(numLib.term_of_int x),
                 ^(numLib.term_of_int y),
                 ^(numLib.term_of_int z)
              )``))))))
  |> List.concat
  |> List.concat
  |> LIST_CONJ

Theorem index_to_triple_100 =
  List.tabulate(100, fn i =>
    EVAL``index_to_triple 4 ^(numLib.term_of_int i)``)
  |> LIST_CONJ

Definition bool_to_bit_def:
  bool_to_bit b = if b then 1 else 0
End

Definition bools_to_word_def:
  bools_to_word bs =
  word_from_bin_list (MAP bool_to_bit bs)
End

Definition bools_to_hex_string_def:
  bools_to_hex_string bs =
  FLAT $
    MAP (
      PAD_LEFT #"0" 2 o
      (word_to_hex_string : word8 -> string) o
      bools_to_word
    ) $ chunks 8 bs
End

open cv_transLib cv_stdTheory;

val _ = cv_trans index_to_triple_def;
val _ = cv_trans triple_to_index_def;

val _ = cv_trans bool_lookup_def;

val _ = theta_spt_def |> SRULE [mapi_def] |> cv_auto_trans;

Definition while1_def:
  while1 a tt ww x y w z a' =
    if z < w:num then
      while1 a tt ww x y w (z + 1)
        (insert (triple_to_index w (x,y,z))
          (bool_lookup (triple_to_index w (x,y,(z + ww − tt) MOD w)) a) a')
    else a'
Termination
  WF_REL_TAC ‘measure $ λ(a,tt,ww,x,y,w,z,a'). w - z’
End

Triviality while1_thm:
  ∀a tt ww x y w z a'.
    SND (WHILE (λ(z,a'). z < w)
               (λ(z,a').
                  (z + 1,
                   insert (triple_to_index w (x,y,z))
                          (bool_lookup
                            (triple_to_index w
                              (x,y,(z + ww − tt) MOD w)) a) a')) (z,a')) =
    while1 a tt ww x y w z a'
Proof
  ho_match_mp_tac while1_ind \\ rw []
  \\ simp [Once whileTheory.WHILE]
  \\ simp [Once while1_def]
  \\ IF_CASES_TAC \\ gvs []
QED

Definition while2_def:
  while2 a w ww x y t a' =
    if t ≤ 23 then
      while2 a w ww y ((2 * x + 3 * y) MOD 5) (t + 1:num)
             (let tt = (t + 1) * (t + 2) DIV 2 in
                while1 a tt ww x y w 0 a')
    else a'
Termination
  WF_REL_TAC ‘measure $ λ(a,w,ww,x,y,t,a'). 24 - t’ \\ gvs []
End

Theorem while2_thm:
  ∀a w ww x y t a'.
    (λ(x,y,t,a'). a')
      (WHILE (λ(x,y,t,a'). t ≤ 23)
            (λ(x,y,t,a').
                 (y,(2 * x + 3 * y) MOD 5,t + 1,
                  (let
                     tt = (t + 1) * (t + 2) DIV 2
                   in
                     while1 a tt ww x y w 0 a'))) (x,y,t,a')) =
    while2 a w ww x y t a'
Proof
  ho_match_mp_tac while2_ind \\ rw []
  \\ simp [Once whileTheory.WHILE]
  \\ simp [Once while2_def]
  \\ IF_CASES_TAC \\ gvs []
QED

val _ = cv_trans while1_def;
val _ = cv_trans while2_def;

val rho_spt_eq = rho_spt_def
  |> ISPEC “a :bool num_map”
  |> SRULE [mapi_def,while1_thm]
  |> SRULE [LET_THM,while2_thm]
  |> CONV_RULE (RAND_CONV (UNBETA_CONV “size (a:bool num_map)” THENC
                           RATOR_CONV (ALPHA_CONV “n:num”) THENC
                           REWR_CONV (GSYM LET_THM)));

val _ = cv_trans rho_spt_eq;

val _ = pi_spt_def |> ISPEC “a :bool num_map” |> SRULE [mapi_def]
                                              |> cv_auto_trans;

val _ = chi_spt_def |> SRULE [mapi_def] |> cv_auto_trans;

val _ = cv_trans spt_to_string_def;

val _ = cv_trans b2w_def;

val pre = rc_step_def |> SRULE [LET_THM] |> cv_trans_pre;
Theorem rc_step_pre[cv_pre]:
  ∀r. rc_step_pre r ⇔ 8 ≤ LENGTH r
Proof
  simp [Once pre] \\ rw [] \\ eq_tac \\ gvs [] \\ Cases_on ‘r’ \\ gvs []
QED

Definition rc_steps_def:
  rc_steps n r =
    if n = 0:num then HD r else
      rc_steps (n-1) (rc_step r)
End

val pre = cv_trans_pre rc_steps_def;
Theorem rc_steps_pre[cv_pre]:
  ∀n r. rc_steps_pre n r = if n = 0 then r ≠ [] else 8 ≤ LENGTH r
Proof
  Induct \\ simp [Once pre] \\ gvs [] \\ rw []
  \\ Cases_on ‘r’ \\ gvs [rc_step_def]
QED

Triviality rc_eq:
  rc t = rc_steps (t MOD 255) [T;F;F;F;F;F;F;F]
Proof
  rewrite_tac [rc_def,EVAL “REPLICATE 7 x”]
  \\ IF_CASES_TAC \\ asm_rewrite_tac []
  >- EVAL_TAC
  \\ rename [‘rc_steps n xs’]
  \\ pop_assum kall_tac
  \\ qid_spec_tac ‘xs’
  \\ Induct_on ‘n’
  \\ simp [Once rc_steps_def]
  \\ rewrite_tac [FUNPOW]
  \\ gvs []
QED

val pre = cv_trans_pre rc_eq;
Theorem rc_pre[cv_pre]:
  ∀t. rc_pre t
Proof
  rw [Once pre]
QED

Definition log2_def:
  log2 n acc = if n < 2 then acc else log2 (n DIV 2) (acc + 1:num)
End

val _ = cv_trans log2_def;

Theorem LOG2_eq_log2:
  0 < n ⇒ LOG2 n = log2 n 0
Proof
  qsuff_tac ‘∀n acc. 0 < n ⇒ log2 n acc = LOG2 n + acc’ >- gvs []
  \\ ho_match_mp_tac log2_ind \\ rw []
  \\ Cases_on ‘n = 1’
  >- (gvs [] \\ simp [Once log2_def])
  \\ simp [Once log2_def]
  \\ simp [LOG2_def, SimpRHS]
  \\ once_rewrite_tac [numeral_bitTheory.LOG_compute]
  \\ gvs [] \\ gvs [ADD1,LOG2_def]
  \\ first_x_assum irule
  \\ simp[X_LT_DIV]
QED

val _ = w2l_def |> SRULE [LOG2_eq_log2] |> cv_trans

Definition iota_body_def:
  iota_body w i a l1 k v =
                 (let
                    (x,y,z) = index_to_triple w k
                  in
                    if x = 0 ∧ y = 0 then
                      (let
                         l = l1 ;
                         RCz =
                           ((z = 2 ** log2 (SUC z) 0 − 1 ∧
                             log2 (SUC z) 0 ≤ l) ∧
                            rc (log2 (SUC z) 0 + 7 * i))
                       in
                         bool_lookup (triple_to_index w (0,0,z)) a ⇎ RCz)
                    else v)
End

val _ = iota_spt_def
          |> SRULE [LOG2_eq_log2,mapi_def,GSYM iota_body_def]
          |> cv_auto_trans;

val _ = cv_trans Rnd_spt_def;
val _ = cv_auto_trans Keccak_p_spt_def;
val _ = cv_trans pad10s1_def;

Definition sponge_foldl_def:
  sponge_foldl xs S0 Pis =
    FOLDL (λSi Pi. Keccak_p_spt 24 (MAP2 (λx y. x ⇎ y) Si (Pi ⧺ xs))) S0 Pis
End

val _ = cv_auto_trans sponge_foldl_def;

Definition while3_def:
  while3 cl k x Z S =
    if cl = 0 then Z else
    if LENGTH Z < x then
      while3 (cl-1:num) k x (Z ⧺ TAKE k S) (Keccak_p_spt 24 S)
    else Z
End

val _ = cv_trans while3_def;

Theorem toSortedAList_EQ_NIL:
  ∀t. toSortedAList t = [] ⇔ size t = 0
Proof
  rewrite_tac [GSYM sptreeTheory.LENGTH_toSortedAList] \\ rw []
QED

Triviality GENLIST_EQ_NIL:
  GENLIST f n = [] ⇔ n = 0
Proof
  Cases_on ‘n’ \\ gvs [GENLIST]
QED

Triviality size_while1_neq_0:
  ∀a tt ww x y w z s.
    size s ≠ 0 ⇒
    size (while1 a tt ww x y w z s) ≠ 0
Proof
  ho_match_mp_tac while1_ind
  \\ rpt gen_tac \\ strip_tac \\ strip_tac \\ gvs []
  \\ once_rewrite_tac [while1_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ last_x_assum irule
  \\ gvs [size_insert] \\ rw []
QED

Triviality size_while2_neq_0:
  ∀a w ww x y t s.
    size s ≠ 0 ⇒
    size (while2 a w ww x y t s) ≠ 0
Proof
  ho_match_mp_tac while2_ind
  \\ rpt gen_tac \\ strip_tac \\ strip_tac
  \\ gvs []
  \\ once_rewrite_tac [while2_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ last_x_assum irule
  \\ irule size_while1_neq_0 \\ fs []
QED

Triviality Keccak_p_spt_NOT_NIL:
  xs ≠ [] ⇒ Keccak_p_spt n xs ≠ []
Proof
  gvs [Keccak_p_spt_def,spt_to_string_def]
  \\ qmatch_goalsub_abbrev_tac ‘FUNPOW f k init’ \\ rw []
  \\ fs [toSortedAList_EQ_NIL]
  \\ ‘size (FST init) ≠ 0’ by gvs [Abbr‘init’]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘init’ \\ qid_spec_tac ‘k’
  \\ unabbrev_all_tac
  \\ Induct \\ gvs []
  \\ gen_tac \\ strip_tac
  \\ PairCases_on ‘init’ \\ gvs [FUNPOW]
  \\ first_x_assum irule
  \\ gvs [Rnd_spt_def,iota_spt_def]
  \\ gvs [rho_spt_eq]
  \\ irule size_while2_neq_0
  \\ gvs [theta_spt_def,wf_mapi]
QED

Theorem while3_thm:
  ∀Z S.
    c < 1600 ∧ S ≠ [] ∧ x' ≤ 1600 ⇒
    FST (WHILE (λ(Z,S). LENGTH Z < x')
      (λ(Z,S). (Z ⧺ TAKE (1600 − c) S,Keccak_p_spt 24 S))
      ([],S))
    =
    while3 1600 (1600 − c) x' [] S
Proof
  rw []
  \\ qsuff_tac ‘∀Z0 S0 k. S0 ≠ [] ∧ x' ≤ k + LENGTH Z0 ⇒
    FST (WHILE (λ(Z,S). LENGTH Z < x')
      (λ(Z,S). (Z ⧺ TAKE (1600 − c) S,Keccak_p_spt 24 S)) (Z0,S0)) =
    while3 k (1600 − c) x' Z0 S0’
  >- (rw [] \\ pop_assum irule \\ gvs [])
  \\ gen_tac
  \\ completeInduct_on ‘x' - LENGTH Z0’
  \\ rpt strip_tac \\ gvs [PULL_FORALL]
  \\ once_rewrite_tac [while3_def] \\ gvs []
  \\ once_rewrite_tac [WHILE] \\ simp []
  \\ IF_CASES_TAC \\ gvs []
  \\ last_x_assum irule
  \\ gvs [Keccak_p_spt_NOT_NIL]
  \\ conj_asm1_tac \\ gvs []
  \\ Cases_on ‘S0’ \\ gvs []
QED

Definition Keccak_spt_def:
  Keccak_spt c x x' =
    let
      P = x ⧺ pad10s1 (1600 − c) (LENGTH x);
      c' = 1600 − (1600 − c);
      Pis = chunks (1600 − c) P;
      S0 = REPLICATE 1600 F;
      S = sponge_foldl (REPLICATE c' F) S0 Pis;
      Z = while3 1600 (1600 − c) x' [] S
    in
      TAKE x' Z
End;

Triviality sponge_foldl_NOT_NIL:
  ∀xs S0 Pis.
    S0 ≠ [] ∧ xs ≠ [] ⇒
    sponge_foldl xs S0 Pis ≠ []
Proof
  Induct_on ‘Pis’ \\ gvs [sponge_foldl_def]
  \\ gvs [GSYM sponge_foldl_def] \\ rw []
  \\ last_x_assum irule \\ gvs []
  \\ irule Keccak_p_spt_NOT_NIL \\ gvs []
  \\ Cases_on ‘S0’ \\ gvs []
  \\ Cases_on ‘xs’ \\ gvs []
  \\ Cases_on ‘h’ \\ gvs []
QED

Theorem Keccak_spt_thm:
  ∀c x y. c ≠ 0 ∧ c < 1600 ∧ y ≤ 1600 ⇒ Keccak c x y = Keccak_spt c x y
Proof
  rw []
  \\ DEP_REWRITE_TAC [Keccak_spt] \\ simp [Keccak_spt_def]
  \\ gvs [sponge_def,FUN_EQ_THM,GSYM sponge_foldl_def]
  \\ AP_TERM_TAC
  \\ irule while3_thm \\ fs []
  \\ irule sponge_foldl_NOT_NIL \\ gvs []
QED

Definition chunks_tail_def:
  chunks_tail n ls acc =
    if LENGTH ls ≤ n ∨ n = 0 then REVERSE (ls :: acc) else
      chunks_tail n (DROP n ls) (TAKE n ls :: acc)
Termination
  WF_REL_TAC ‘measure $ λ(n,ls,acc). LENGTH ls’
  \\ gvs [LENGTH_DROP]
End

Theorem chunks_eq_chunks_tail:
  chunks n ls = chunks_tail n ls []
Proof
  qsuff_tac ‘∀n ls acc. chunks_tail n ls acc = REVERSE acc ++ chunks n ls’
  \\ gvs [] \\ ho_match_mp_tac chunks_tail_ind
  \\ rw []
  \\ simp_tac std_ss [Once chunks_tail_def, Once chunks_def]
  \\ IF_CASES_TAC \\ gvs []
QED

val _ = cv_trans chunks_tail_def;
val _ = cv_trans chunks_eq_chunks_tail;
val _ = cv_trans Keccak_spt_def;

val _ = Keccak_224_def |> SRULE [Keccak_spt_thm] |> cv_trans;
val _ = Keccak_256_def |> SRULE [Keccak_spt_thm] |> cv_trans;
val _ = SHA3_224_def |> SRULE [Keccak_spt_thm] |> cv_trans;
val _ = SHA3_256_def |> SRULE [Keccak_spt_thm] |> cv_trans;
val _ = SHA3_384_def |> SRULE [Keccak_spt_thm] |> cv_trans;
val _ = SHA3_512_def |> SRULE [Keccak_spt_thm] |> cv_trans;

Theorem HEX_eq:
  n < 16 ⇒ HEX n = if n < 10 then CHR (ORD #"0" + n) else
                                  CHR (ORD #"A" + n - 10)
Proof
  rpt (Cases_on ‘n’ \\ gvs [ASCIInumbersTheory.HEX_def]
       \\ Cases_on ‘n'’ \\ gvs [ASCIInumbersTheory.HEX_def,ADD1])
QED

val pre = cv_trans_pre HEX_eq
Theorem HEX_pre[cv_pre]:
  ∀n. HEX_pre n ⇔ n < 16
Proof
  gvs [pre]
QED

Definition hex_string_def:
  hex_string n acc =
    if n < 16 then HEX n :: acc else
      hex_string (n DIV 16) (HEX (n MOD 16) :: acc)
End

val pre = cv_trans_pre hex_string_def;
Theorem hex_string_pre[cv_pre]:
  ∀n acc. hex_string_pre n acc
Proof
  ho_match_mp_tac hex_string_ind \\ rw [] \\ simp [Once pre]
QED

Theorem word_to_hex_string_eq_byte:
  word_to_hex_string (w:word8) = hex_string (w2n w) []
Proof
  gvs [word_to_hex_string_def,w2s_def,ASCIInumbersTheory.n2s_def]
  \\ qsuff_tac ‘∀n acc. hex_string n acc = REVERSE (MAP HEX (n2l 16 n)) ++ acc’
  >- gvs []
  \\ ho_match_mp_tac hex_string_ind \\ rw []
  \\ once_rewrite_tac [numposrepTheory.n2l_def]
  \\ simp [Once hex_string_def]
  \\ IF_CASES_TAC \\ gvs []
QED

val _ = cv_trans word_to_hex_string_eq_byte;

Definition bools_to_hex_f_def:
  bools_to_hex_f =
    PAD_LEFT #"0" 2 ∘ word_to_hex_string ∘ (bools_to_word : bool list -> word8)
End

val _ =  bools_to_hex_f_def
  |> SRULE [FUN_EQ_THM,bools_to_word_def,word_from_bin_list_def,l2w_def]
  |> cv_auto_trans;

val _ = bools_to_hex_string_def
  |> SRULE [GSYM bools_to_hex_f_def]
  |> cv_auto_trans;

(* w = 1, so rho does nothing *)
Theorem rho_spt_25_example:
  rho_spt (fromList (GENLIST (λi. i < 10) 25))
  = fromList (GENLIST (λi. i < 10) 25)
Proof
  simp [] \\ CONV_TAC cv_eval
QED

Theorem Keccak_224_NIL:
  bools_to_hex_string (Keccak_224 []) =
  "F71837502BA8E10837BDD8D365ADB85591895602FC552B48B7390ABD"
Proof
  CONV_TAC cv_eval
QED

Theorem Keccak_256_NIL:
  bools_to_hex_string (Keccak_256 []) =
  "C5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470"
Proof
  CONV_TAC cv_eval
QED

(*

val cs = num_compset();
val () = extend_compset [
  Tys [``:state_array``],
  Defs [
    Keccak_224_def,
    Keccak_256_def,
    Keccak_448_spt,
    Keccak_512_spt,
    sponge_def,
    chunks_def,
    pad10s1_def,
    Keccak_p_spt_def,
    b2w_def,
    w2l_def,
    spt_to_string_def,
    Rnd_spt_def,
    iota_spt_def,
    chi_spt_def,
    pi_spt_def,
    rho_spt_def,
    theta_spt_def,
    triple_to_index_25,
    index_to_triple_25,
    triple_to_index_100,
    index_to_triple_100,
    triple_to_index_1600,
    index_to_triple_1600,
    bool_lookup_def,
    rc_step_def,
    rc_def,
    bool_to_bit_def,
    bools_to_word_def,
    bools_to_hex_string_def,
    (* for examples *)
    spt_to_state_array_w,
    spt_to_state_array_sptfun,
    sptfun_def,
    Lane_def,
    (* -- *)
    WHILE, (* TODO: why is this not in a compset? *)
    (* TODO: move to sptree_compset *)
    mapi_def, mapi0_def, apsnd_cons_def, combine_rle_def, spt_center_def,
    spt_left_def, spt_right_def, spt_centers_def, spts_to_alist_def, toSortedAList_def
      ],
  Extenders [
    listSimps.list_rws,
    rich_listSimps.add_rich_list_compset,
    pairLib.add_pair_compset,
    add_bit_compset,
    pred_setLib.add_pred_set_compset,
    add_sptree_compset,
    OPTION_rws,
    add_combin_compset,
    add_words_compset true]
 ] cs

(* w = 1, so rho does nothing *)
Theorem rho_spt_25_example:
  rho_spt (fromList (GENLIST (λi. i < 10) 25))
  = fromList (GENLIST (λi. i < 10) 25)
Proof
  simp [] \\ CONV_TAC cv_eval
QED

(* w = 4,
 * rho shifts (4,0) by 3 (91 MOD 4)
 * rho shifts (1,4) by 2 (66 MOD 4)
 * rho shifts (4,3) by 0 (136 MOD 4)
*)

Theorem rho_spt_100_example:
  let t = fromList $ GENLIST (λi. i MOD 5 = 0) 100 in
  let a0 = spt_to_state_array t in
  let a1 = spt_to_state_array $ rho_spt t in
    Lane a1 (4,0) =
      (let l = Lane a0 (4,0) in
       (DROP 3 l) ++ (TAKE 3 l)) ∧
    Lane a1 (1,4) =
      (let l = Lane a0 (1,4) in
       (DROP 2 l) ++ (TAKE 2 l)) ∧
    Lane a1 (4,3) = Lane a0 (4,3)
Proof
  rw[]
  \\ CONV_TAC cv_eval

  \\ CONV_TAC(CBV_CONV cs)
QED

Theorem Keccak_224_NIL:
  bools_to_hex_string (Keccak_224 []) =
  "F71837502BA8E10837BDD8D365ADB85591895602FC552B48B7390ABD"
Proof
  CONV_TAC(CBV_CONV cs)
QED

Theorem Keccak_256_NIL:
  bools_to_hex_string (Keccak_256 []) =
  "C5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470"
Proof
  CONV_TAC(CBV_CONV cs)
QED

Definition state_array_to_lane_words_def:
  state_array_to_lane_words a =
  MAP bools_to_word
    (FLAT (GENLIST (λx. GENLIST (λy. Lane a (x,y)) 5) 5))
End

val () = computeLib.add_thms
  [state_array_to_lane_words_def,
   string_to_state_array_def, restrict_def] cs

val init_state_thm = CBV_CONV cs ``state_array_to_lane_words
  (string_to_state_array (GENLIST (λi. i MOD 5 = 0) 1600))``

val init_string = init_state_thm |> concl |> lhs |> rand |> rand

val rho_test_thm = CBV_CONV cs ``state_array_to_lane_words (
  spt_to_state_array (rho_spt (fromList ^init_string)))``

val pi_test_thm = CBV_CONV cs ``state_array_to_lane_words (
  spt_to_state_array (pi_spt (fromList ^init_string)))``

val theta_test_thm = CBV_CONV cs ``state_array_to_lane_words (
  spt_to_state_array (theta_spt (fromList ^init_string)))``

val chi_test_thm = CBV_CONV cs ``state_array_to_lane_words (
  spt_to_state_array (chi_spt (fromList ^init_string)))``

val iota_test_thm = CBV_CONV cs ``state_array_to_lane_words (
  spt_to_state_array (iota_spt (fromList ^init_string) 7))``

val Keccak_f_test_thm = CBV_CONV cs ``state_array_to_lane_words (
  string_to_state_array (Keccak_p_spt 24 ^init_string))``

val pad_test_thm = CBV_CONV cs ``
MAP word_from_bin_list
(chunks 8
(MAP (λb. if b then 1 else 0)
  (^init_string ++ pad10s1 (1600 - 512) (LENGTH ^init_string))))
  : word8 list
``

val init_string_bytes = CBV_CONV cs``
  MAP word_from_bin_list (
    chunks 8 (MAP (λb. if b then 1 else 0) ^init_string)
    ) : word8 list
    ``

val absorb_test_thm = CBV_CONV cs
``let f = Keccak_p_spt 24 in
  let b = 1600 in
  let c = 512 in
  let r = 1600 - c in
  let P = ^(pad_test_thm |> concl |> lhs |> funpow 3 rand) in
  let Pis = chunks r P in
  let S0 = REPLICATE b F in
  let S = FOLDL (λSi Pi. f (MAP2 (λx y. x <> y) Si (Pi ++ REPLICATE c F))) S0
  Pis
  in S
``

val squeeze_test_thm = CBV_CONV cs
``
let f = Keccak_p_spt 24 in
let c = 512 in
let r = 1600 - c in
let d = 256 in
let S = ^(rhs(concl absorb_test_thm)) in
let Z = FST (
  WHILE (λ(Z,S). LENGTH Z < d) (λ(Z,S). (Z ++ TAKE r S, f S)) ([], S)
) in TAKE d Z
``

EVAL ``
MAP n2w [1190112520884487201;2380225043985731716;9520900167075897608;2380225112705208452;9520900167075906064;4760450083537948804;1190113655864232002;2380225041768974468;2380227311728464004;9520900167075897608;1190112520884487201;9520900167075897616;1190113655864232002;4760450083537953032;9818428297297019408;2380225041838248068;9530197921145307664;9520900167084556816;595056260442784801;613651768581063713;2380225041704030340;595056260441736225;9520899901065019920;4760450083537948680;9520900167075889680]
= ^(rhs(concl rho_test_thm))``

EVAL `` MAP n2w
[1190112520884487201;9520900167075897608;2380225041768974402;595056260442243600;4760450083537948804;2380225041768974402;595056260442243600;4760450083537948804;1190112520884487201;9520900167075897608;4760450083537948804;1190112520884487201;9520900167075897608;2380225041768974402;595056260442243600;9520900167075897608;2380225041768974402;595056260442243600;4760450083537948804;1190112520884487201;595056260442243600;4760450083537948804;1190112520884487201;9520900167075897608;2380225041768974402]
= ^(rhs(concl pi_test_thm))``

EVAL ``MAP n2w
[6545618864864679605;6545618864864679605;6545618864864679605;6545618864864679605;6545618864864679605;13091237729729359211;13091237729729359211;13091237729729359211;13091237729729359211;13091237729729359211;7735731385749166807;7735731385749166807;7735731385749166807;7735731385749166807;7735731385749166807;15471462771498333612;15471462771498333612;15471462771498333612;15471462771498333612;15471462771498333612;12496181469287115610;12496181469287115610;12496181469287115610;12496181469287115610;12496181469287115610]
= ^(rhs(concl theta_test_thm))``

EVAL ``MAP n2w
[5950562604422436005;5950562604422436005;5950562604422436005;5950562604422436005;5950562604422436005;11901125208844872010;11901125208844872010;11901125208844872010;11901125208844872010;11901125208844872010;5355506343980192404;5355506343980192404;5355506343980192404;5355506343980192404;5355506343980192404;10711012687960384809;10711012687960384809;10711012687960384809;10711012687960384809;10711012687960384809;2975281302211218002;2975281302211218002;2975281302211218002;2975281302211218002;2975281302211218002]
= ^(rhs(concl chi_test_thm))``

EVAL ``MAP n2w
[10413484557739230248;1190112520884487201;1190112520884487201;1190112520884487201;1190112520884487201;2380225041768974402;2380225041768974402;2380225041768974402;2380225041768974402;2380225041768974402;4760450083537948804;4760450083537948804;4760450083537948804;4760450083537948804;4760450083537948804;9520900167075897608;9520900167075897608;9520900167075897608;9520900167075897608;9520900167075897608;595056260442243600;595056260442243600;595056260442243600;595056260442243600;595056260442243600]
= ^(rhs(concl iota_test_thm))``

EVAL ``MAP n2w
[12527428395425175348;15801298012686366507;3188220639418651126;3321697703372914021;392354921814910000;12969346763022901137;16472965139809776265;7551077093031917714;3462283554697442690;11880954693601669160;14043976998532219136;13290350532005714486;8281948419926017253;5563974798024345351;1095251020247860242;11824366241951878661;6839891776852556124;15993682277163781118;18195611134401667551;5043288562153437971;7883103420529788315;8402947264540262517;1941332173674254838;18102320560554041299;2992148669962812600]
= ^(rhs(concl Keccak_f_test_thm))``

EVAL `` MAP n2w
[33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;33;132;16;66;8;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;128]
= ^(rhs(concl pad_test_thm))``

EVAL ``MAP n2w
[12417067843063317025;11559189604044637574;10283124272294950150;14699815144987270495;283173274300431045;3236883229902219665;2896567989647695906;1420376225281158638;17609325282516577257;4943531605352710241;6348566720201527309;13438540713024530881;9813492967349884184;3951509894084461853;13945734360192510516;5945400830828459221;8243876224757392082;2324403489064850701;12570080452898761122;1516007673639937983;15662554419738670582;16342922203974826137;3023483368381129057;3389012354561481769;8948748016597943154]
= state_array_to_lane_words (
    string_to_state_array ^(rhs(concl absorb_test_thm))
  )``

EVAL ``MAP n2w
[33;2;183;49;106;73;82;172;145;169;189;217;37;184;235;44;13;144;122;190;203;163;26;88;213;180;215;56;142;78;130;82]
= MAP bools_to_word (chunks 8 ^(rhs(concl squeeze_test_thm)))
``

val test_Keccak_256_thm = CBV_CONV cs ``Keccak_256 ^init_string``

CBV_CONV cs ``bools_to_hex_string
  ^(rhs (concl test_Keccak_256_thm))``
(* 2102B7316A4952AC91A9BDD925B8EB2C0D907ABECBA31A58D5B4D7388E4E8252 *)
(* 2102b7316a4952ac91a9bdd925b8eb2c0d907abecba31a58d5b4d7388e4e8252 *)

*)

val _ = export_theory();
