open HolKernel Parse boolLib bossLib dep_rewrite bitLib reduceLib combinLib computeLib;
open optionTheory pairTheory arithmeticTheory combinTheory listTheory
     rich_listTheory whileTheory bitTheory dividesTheory wordsTheory
     logrootTheory sptreeTheory;

(* The SHA-3 Standard: https://doi.org/10.6028/NIST.FIPS.202 *)

val _ = new_theory "keccak";

(* TODO: move *)
Theorem FUNPOW_COMPOSE_INV:
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
Theorem WHILE_FUNPOW:
  (?n. ~P (FUNPOW f n s))
  ==> WHILE P f s = FUNPOW f (LEAST n. ~P (FUNPOW f n s)) s
Proof
  strip_tac
  \\ `~!n. P (FUNPOW f n s)` by PROVE_TAC[]
  \\ `?x. OWHILE P f s = SOME x` by PROVE_TAC[OWHILE_EQ_NONE, option_CASES]
  \\ irule OWHILE_WHILE
  \\ rewrite_tac[OWHILE_def]
  \\ IF_CASES_TAC
  \\ fsrw_tac[][]
QED

(* TODO: move *)
Theorem insert_fromList_IN_domain:
  !ls k v.
  k < LENGTH ls ==>
  insert k v (fromList ls) =
  fromList (TAKE k ls ++ [v] ++ DROP (SUC k) ls)
Proof
  simp[fromList_def]
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[FOLDL_SNOC, TAKE_SNOC]
  \\ Cases_on`k = LENGTH ls` \\ gs[]
  >- (
    rw[DROP_LENGTH_NIL_rwt]
    \\ gs[GSYM fromList_def, UNCURRY]
    \\ qmatch_goalsub_abbrev_tac`FST (FOLDL f e ls)`
    \\ `!ls e. FST (FOLDL f e ls) = FST e + LENGTH ls`
    by ( Induct \\ rw[Abbr`f`, UNCURRY] )
    \\ rw[Abbr`e`, insert_shadow]
    \\ simp[fromList_def, FOLDL_APPEND]
    \\ simp[Abbr`f`, UNCURRY] )
  \\ gs[GSYM fromList_def, UNCURRY, DROP_SNOC]
  \\ simp[SNOC_APPEND]
  \\ qmatch_goalsub_abbrev_tac`FST (FOLDL f e ls)`
  \\ `!ls e. FST (FOLDL f e ls) = FST e + LENGTH ls`
  by ( Induct \\ rw[Abbr`f`, UNCURRY] )
  \\ simp[Abbr`e`]
  \\ simp[Once insert_insert]
  \\ simp[fromList_def]
  \\ simp[Once FOLDL_APPEND, SimpRHS]
  \\ simp[Abbr`f`, UNCURRY]
  \\ simp[ADD1]
QED

(*
(* TODO: move *)
Theorem fromList_SNOC:
  !ls x.
  fromList (SNOC x ls) =
  insert (LENGTH ls) x (fromList ls)
Proof
  Induct
  \\ gs[fromList_def]
  \\ gs[FOLDL_SNOC]
  \\ rpt gen_tac
  \\ qmatch_goalsub_abbrev_tac`insert _ _ (SND p)`
  \\ PairCases_on`p` \\ simp[]
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC
  \\ gs[GSYM fromList_def]

  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac`FOLDL f e`
  \\ `FOLDL f e ls = FOLDL f e ls /\
      (\p. FST p = FST e + LENGTH ls) (FOLDL f e ls)`
  by (
    irule FOLDL_CONG_invariant
*)

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

Theorem chunks_0[simp]:
  chunks 0 ls = [ls]
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

Definition index_to_triple_def:
  index_to_triple w i = ((i DIV w) MOD 5, i DIV w DIV 5, i MOD w)
End

Definition triple_to_index_def:
  triple_to_index w (x, y, z) = x * w + 5 * y * w + z
End

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

(* if y is fixed 0 *)
(* i -> (i DIV w, i MOD w) *)
(* (x, z) -> x * w + z *)

Definition theta_spt_def:
  theta_spt t =
  let w = b2w $ size t in
  let c = fromList (
    GENLIST (λi.
      (THE (lookup i t) ≠
        (THE (lookup (i + 5 * w) t) ≠
          (THE (lookup (i + 10 * w) t) ≠
            (THE (lookup (i + 15 * w) t) ≠
              (THE (lookup (i + 20 * w) t)))))))
      (5 * w)) in
  let d = fromList (
    GENLIST (λi.
      (THE (lookup (((i DIV w + 4) MOD 5) * w + i MOD w) c) ≠
       THE (lookup (((i DIV w + 1) MOD 5) * w + (i MOD w + PRE w) MOD w) c)))
      (5 * w)) in
  mapi (λi b. b ≠ THE (lookup (((i DIV w) MOD 5) * w + i MOD w) d)) t
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

Definition sptify_def:
  sptify a =
  a with A := restrict a.w $ λ(x,y,z).
    case lookup (y * 5 * a.w + x * a.w + z)
           $ fromList (state_array_to_string a)
    of NONE => F | SOME b => b
End

Theorem sptify_id:
  wf_state_array a ⇒ sptify a = a
Proof
  rw[sptify_def, state_array_component_equality,
     FUN_EQ_THM, FORALL_PROD, restrict_def]
  \\ reverse (rw[lookup_fromList])
  >- (
    fs[wf_state_array_def]
    \\ first_x_assum irule
    \\ CCONTR_TAC \\ gs[]
    \\ last_x_assum mp_tac \\ simp[]
    \\ fs[NUMERAL_LESS_THM] )
  \\ qmatch_goalsub_rename_tac`a.A (x,y,z)`
  \\ reverse(Cases_on`x < 5 ∧ y < 5 ∧ z < a.w`)
  >- fs[wf_state_array_def] \\ fs[]
  \\ rw[state_array_to_string_compute]
  \\ AP_TERM_TAC \\ simp[]
  \\ `z + (x * a.w + 5 * (y * a.w)) = (x + 5 * y) * a.w + z` by simp[]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[DIV_MULT, LESS_DIV_EQ_ZERO]
QED

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
  \\ qmatch_goalsub_abbrev_tac`THE (lookup _ d)`
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac`THE (lookup _ c)`
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
  \\ reverse(rw[Abbr`d`, lookup_fromList])
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

Theorem theta_spt_isFromList:
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
    let (x,y,t,a') =
    WHILE (λ(x,y,t,a'). t ≤ 23)
      (λ(x,y,t,a'). (y, (2 * x + 3 * y) MOD 5, t + 1,
        let tt = (t + 1) * (t + 2) DIV 2 in
        let ww = w * (tt DIV w) in
        SND $
        WHILE (λ(z,a'). z < w) (λ(z,a'). (z+1,
          insert (triple_to_index w (x,y,z))
            (THE $ lookup (triple_to_index w (x,y,(z + ww - tt) MOD w)) a)
          a'))
          (0, a')))
      (1,0,0,a)
    in a'
End

Theorem FUNPOW_invariant_index:
  ∀m x.
  P x ∧
  (∀n. n < m ⇒ R (FUNPOW f n x)) ∧
  (∀x. P x ∧ R x ⇒ P (f x)) ⇒
  P (FUNPOW f m x)
Proof
  Induct>>rw[FUNPOW_SUC]
QED

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
  \\ metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

(*
Theorem rho_spt:
  spt_to_state_array (rho_spt t) =
  (rho (spt_to_state_array t))
Proof
  rw[state_array_component_equality]
*)

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
       `state_array_to_string ## I`]mp_tac FUNPOW_COMPOSE_INV
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

Theorem Keccak_tabulate:
  ∀c. c < 1600 ⇒
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
    \\ gs[]
    \\ conj_tac >- simp[pad10s1_def]
    \\ `0 < 1600 - c` by simp[]
    \\ drule_then(qspec_then`LENGTH x`strip_assume_tac) LENGTH_pad10s1
    \\ simp[] )
  \\ `FOLDL g e z = FOLDL k e z /\ (divides 25 o LENGTH) (FOLDL k e z)`
  by (
    irule FOLDL_CONG_invariant \\
    conj_tac >- rw[Abbr`e`, divides_def]
    \\ rpt gen_tac \\ strip_tac
    \\ conj_asm1_tac >- (
      rw[Abbr`g`, Abbr`k`]
      \\ irule Keccak_p_tabulate
      \\ rw[]
      \\ fs[EVERY_MEM]
      \\ res_tac \\ pop_assum (SUBST1_TAC o SYM)
      \\ simp[] \\ fs[divides_def]
      \\ rw[MIN_DEF] )
    \\ pop_assum (SUBST1_TAC o SYM)
    \\ rw[Abbr`g`, LENGTH_Keccak_p] )
  \\ gs[]
  \\ irule FUNPOW_CONG
  \\ rw[Abbr`f`, Abbr`h`, UNCURRY]
  \\ irule Keccak_p_tabulate
  \\ qmatch_goalsub_abbrev_tac`FUNPOW f m y`
  \\ qho_match_abbrev_tac`P (FUNPOW f m y)`
  \\ irule FUNPOW_invariant
  \\ rw[Abbr`P`, Abbr`y`, Abbr`f`] \\ rw[UNCURRY, LENGTH_Keccak_p]
  \\ fs[divides_def]
QED

Theorem Keccak_tabulate_512 = Keccak_tabulate |>
  Q.SPEC`512` |> SIMP_RULE std_ss []

Definition Rnd_spt_def:
  Rnd_spt a =
    let θ = theta (sptify a) in
    let ρ = rho (sptify θ) in
    let π = pi (sptify ρ) in
    let χ = chi (sptify π) in
    let ι = iota (sptify χ) in
      ι
End

Theorem Rnd_spt_Rnd:
  wf_state_array a ==> Rnd_spt a = Rnd a
Proof
  strip_tac
  \\ rw[Rnd_spt_def, Rnd_def]
  \\ DEP_REWRITE_TAC[sptify_id]
  \\ rw[]
QED

Theorem state_array_to_string_remove_restrict:
  state_array_to_string <| w := w0; A := restrict w0 f |> =
  state_array_to_string <| w := w0; A := f |>
Proof
  rw[state_array_to_string_compute, restrict_def, LIST_EQ_REWRITE]
  \\ rw[DIV_LT_X]
QED

(*
val cs = num_compset();
val () = extend_compset [
  Tys [``:state_array``],
  Defs [
    restrict_def,
    b2w_def,
    w2l_def,
    string_to_state_array_def,
    state_array_to_string_compute,
    tabulate_string_def,
    sptify_def,
    Rnd_spt_def,
    theta_c_def,
    theta_d_def,
    theta_def,
    rho_def |> SIMP_RULE std_ss [LEAST_DEF, o_DEF],
    pi_def,
    chi_def,
    rc_step_def,
    rc_def,
    iota_compute,
    Keccak_p_def
    Rnd_spt_def
    Keccak_p_tabulate_def,
    chunks_def,
    pad10s1_def,
    sponge_def,
    Keccak_tabulate_512,
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
val ftm = ``Keccak_p_tabulate 24``
val btm = ``1600``
val padtm = ``pad10s1``
val rtm = ``1088``
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
val (step1f, step1args) = step1 |> concl |> rhs |> strip_comb
val n1tm = step1args |> el 1
val s1tm = step1args |> el 2

val wtm = ``b2w (LENGTH ^s1tm)``
val ltm = ``w2l ^wtm``
val i0tm = ``12 + 2 * ^ltm - ^n1tm``
val i1tm = ``12 + 2 * ^ltm - 1``
val step2tm = ``Rnd_string ^wtm ^s1tm ^i0tm``

Triviality EL_n_PLUS:
  n + m < LENGTH ls ==> EL (n + m) ls = EL m (DROP n ls)
Proof
  rw[EL_DROP]
QED

val theta_arg  = ``tabulate_string ^wtm ^s1tm``
val theta_res = ``theta ^theta_arg``
val theta_res_th = CBV_CONV cs theta_res
val theta_str = ``state_array_to_string ^(rhs(concl theta_res_th))``
      |> SIMP_CONV std_ss [state_array_to_string_remove_restrict]
      |> SIMP_RULE std_ss [GSYM ADD_ASSOC, EL_n_PLUS, MOD_LESS]
      |> concl |> rhs
val A_abbrev_def = new_definition("A_abbrev_def",
  ``A_abbrev = ^(theta_str |> funpow 2 rand |> rator |> funpow 2 rand)``)
*)

val _ = export_theory();
