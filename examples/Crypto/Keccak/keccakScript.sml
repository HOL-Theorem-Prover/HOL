open HolKernel Parse boolLib bossLib;
open pairTheory arithmeticTheory combinTheory listTheory rich_listTheory wordsTheory;

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

(*
Theorem state_array_to_string_to_state_array:
  wf_state_array a ⇒
  string_to_state_array (state_array_to_string a) = a
Proof
  rw[state_array_to_string_def, string_to_state_array_def, b2w_def,
     state_array_component_equality, FUN_EQ_THM, FORALL_PROD,
     wf_state_array_def]
  \\ rw [Plane_def, Lane_def]
  \\ rename1 `a.A (x, y, z)`
  \\ Cases_on`x = 0` \\ fs[]
*)

Definition theta_c_def:
  theta_c a (x, z) =
    (a.A (x, 0, z) ≠
     (a.A (x, 1, z) ≠
      (a.A (x, 2, z) ≠
       (a.A (x, 3, z) ≠
        (a.A (x, 4, z))))))
End

Definition theta_d_def:
  theta_d a (x, z) =
  let c = theta_c a in
    c ((x + 4) MOD 5, z) ≠
    c ((x + 1) MOD 5, (z + PRE a.w) MOD a.w)
End

Definition theta_def:
  theta a =
  a with A updated_by (λf (x, y, z).
    f (x, y, z) ≠ theta_d a (x, z))
End

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
  a with A updated_by (λf (x, y, z).
    if x = 0 ∧ y = 0 then f (x, y, z)
    else
      let t = LEAST t. rho_xy t = (x, y) in
      let tt = ((t + 1) * (t + 2)) DIV 2 in
      let ww = a.w * (SUC tt DIV a.w) in
      f (x, y, (z + ww - tt) MOD a.w))
End

Definition pi_def:
  pi a =
  a with A updated_by (λf (x, y, z).
    f ((x + 3 * y) MOD 5, x, z))
End

Definition chi_def:
  chi a =
  a with A updated_by (λf (x, y, z).
    f (x, y, z) ≠
    (¬ f ((x + 1) MOD 5, y, z) ∧
     f ((x + 2) MOD 5, y, z)))
End

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

Definition iota_def:
  iota a i =
  a with A updated_by (λf (x, y, z).
    if x = 0 ∧ y = 0 then
      let l = w2l a.w in
      let RCz = case some j. j ≤ l ∧ z = 2 ** j - 1
                of NONE => F
                 | SOME j => rc (j + 7 * i)
      in
        f (x, y, z) ≠ RCz
    else f (x, y, z))
End

Definition Rnd_def:
  Rnd a = iota (chi (pi (theta a)))
End

(* N.B. We assume here that the round index is always non-negative, which is not
* assumed in the standard. *)

Definition Keccak_p_def:
  Keccak_p s n =
  let a = string_to_state_array s in
  let l = w2l a.w in
  let i0 = 12 + 2 * l - n in
  let i1 = 12 + 2 * l - 1 in
  let a1 = FST (FUNPOW (λ(a,i). (Rnd a i, SUC i)) (SUC i1 - i0) (a, i0)) in
  state_array_to_string a1
End

val _ = export_theory();
