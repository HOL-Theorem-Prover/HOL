(*---------------------------------------------------------------------------
           McCarthy's 91 function.
 ---------------------------------------------------------------------------*)
Theory ninetyOne
Ancestors
  prim_rec arithmetic
Libs
  Defn TotalDefn numLib


(*---------------------------------------------------------------------------
       Define the 91 function. We call it "N". We use Hol_defn to
       make the definition, since we have to tackle the termination
       proof ourselves.
 ---------------------------------------------------------------------------*)

val N_defn =
  Hol_defn "N"
  ‘N(x) = if x>100 then x-10 else N (N (x+11))’;

(*---------------------------------------------------------------------------
   Boilerplate preparation for termination proof.
  ---------------------------------------------------------------------------*)

Theorem lemA[local] =
  DECIDE “~(x > 100) ∧ 101 < y + (101-x) ∧ x < 101 <=> x<y ∧ x < 101”;

val [aux_ind, aux_eqn] =
  Defn.instantiate_aux N_defn
        “measure λx. 101-x”
        (SIMP_RULE arith_ss [lemA] o SRULE[]);

Overload Fn[local] = “N_aux (measure (λx. 101 − x))”

Theorem unexpand_measure:
 (λx' x''. 101 < x' + (101 − x'') ∧ 0 < 101 − x'') = measure (λx. 101 − x)
Proof
  rw[FUN_EQ_THM,measure_def]
QED

(*---------------------------------------------------------------------------
    Induct with the aux induction theorem, then work to unroll the
    aux_eqn at "x+11" and "Fn (x+22)". After that a slightly
    tricky instantiation of the IH finishes things.
  ---------------------------------------------------------------------------*)
val (def,ind) = Defn.tprove
 (N_defn,
  WF_REL_TAC ‘measure λx. 101 - x’ >>
  simp[SUB_LEFT_LESS,unexpand_measure] >>
  ‘∀k x. ¬(x > 100) ∧ k = x + 11 ⇒ x < Fn k’
     suffices_by metis_tac[] >>
  recInduct aux_ind >> rw[] >>
  rename1 ‘x < Fn(x + 11)’ >>
  (* Manually unroll N at "x+11" and "Fn(x+22)" *)
  mp_tac $ Q.INST [‘x’ |-> ‘x + 11’] aux_eqn >> gvs[] >> rw[] >> gvs[] >>
  mp_tac $ Q.INST [‘x’ |-> ‘Fn(x+22)’] aux_eqn >> gvs [] >> rw[] >>
  pop_assum kall_tac >>
  irule LESS_TRANS >>
  qexists_tac ‘Fn(x+22) - 11’ >>
  conj_tac >- decide_tac >>
  ‘¬(Fn(x+22) - 11 > 100)’ by decide_tac >>
  first_x_assum drule >> simp[])

Theorem N_def = def;
Theorem N_ind = ind;

Theorem correctness:
  N n = if n <= 101 then 91 else n - 10
Proof
  qid_spec_tac ‘n’ >>
  recInduct N_ind >> rw[] >>
  once_rewrite_tac [N_def] >>
  simp[]
QED

(*---------------------------------------------------------------------------
      Now try some computations with N.
 ---------------------------------------------------------------------------*)

val results = map (Count.apply EVAL) [
  “N 0”, “N 10”, “N 11”, “N 12”, “N 40”, “N 89”, “N 90” ,
  “N 99”, “N 100”, “N 101”, “N 102”, “N 127”]

(* ----------------------------------------------------------------------
    Alternative approach

    If you do CPS-conversion and then defunctionalisation of the
    continuations, you realise the continuations can just be natural
    numbers, leading to the definition below.

    Proving that *this* terminates requires a tricksy lexicographic
    order, one that embodies the idea that you're approaching the target
    value of 101 (reducing the distance between this and n), but which
    has to cope with parameter combinations that will never occur in
    evaluations that start "normally".

   ---------------------------------------------------------------------- *)

Definition NT_def:
  NT c n = if c = 0 then n
           else if 100 < n then NT (c - 1) (n - 10)
           else NT (c + 1) (n + 11)
Termination
  qexists_tac ‘inv_image ($< LEX $<)
                (λ(c,n). if n < 101 then let m = (101 - n) DIV 11
                                         in
                                           (c + m, 202 - 2 * n)
                         else if c = 0 then (c,n)
                         else if c = 1 /\ 101 < n then (c,n)
                         else if n <= 111 then (c - 1, 223 - 2 * n)
                         else (c,n))’ >>
  rpt strip_tac >> asm_simp_tac (srw_ss()) []
  >- (irule relationTheory.WF_inv_image >> irule pairTheory.WF_LEX >>
      simp[])
  >- (Cases_on ‘n + 11 < 101’ >> ASM_REWRITE_TAC[]
      >- (‘n < 101’ by simp[] >> simp[] >> simp[pairTheory.LEX_DEF] >>
          disj2_tac >>
          ‘101 - n = 11 + (90 - n)’ by simp[] >>
          pop_assum SUBST1_TAC >> simp[ADD_DIV_RWT]) >>
      ‘90 <= n’ by simp[] >>
      simp[pairTheory.LEX_DEF])
  >- (Cases_on ‘c <= 1’ >> asm_simp_tac (srw_ss())[pairTheory.LEX_DEF]
      >- (‘c = 1’ by simp[] >> simp[] >> rw[] >> gs[NOT_LESS, NOT_LESS_EQUAL] >>
          simp[DIV_EQ_X]) >>
      ‘1 < c’ by simp[] >> simp[] >>
      Cases_on ‘n < 111’ >> gs[NOT_LESS_EQUAL, NOT_LESS]
      >- (‘(111 - n) DIV 11 = 0’ by simp[LESS_DIV_EQ_ZERO] >> simp[]) >>
      Cases_on ‘n = 111’ >> simp[] >> rw[])
End

Theorem NT_THM:
  !c n. NT c n = if c = 0 then n
                 else if n <= 10 * c + 91 then 91
                 else n - c * 10
Proof
  recInduct NT_ind >> rpt strip_tac >> Cases_on ‘c=0’
  >- (fs[] >> simp[Once NT_def])
  >- (pop_assum (fn th => RULE_ASSUM_TAC $ SRULE[th] >> assume_tac th) >>
      Cases_on ‘100 < n’ >>
      pop_assum (fn th => RULE_ASSUM_TAC $ SRULE[th] >> assume_tac th) >>
      ONCE_REWRITE_TAC [NT_def] >>
      REWRITE_TAC[ASSUME “c <> 0”]
      >- (asm_simp_tac bool_ss [] >>
          qpat_x_assum ‘NT _ _ = _’ kall_tac >>
          simp[]) >> simp[])
QED

Theorem NT_FUNPOW:
  !c n. NT c n = FUNPOW (NT 1) c n
Proof
  Induct >> simp[NT_THM] >> simp[FUNPOW, NT_THM] >>
  pop_assum (assume_tac o GSYM) >> simp[] >>
  simp[NT_THM]
QED

Overload TrN = “NT 1”

(* looks just like the traditional nested-recursion definition:
     |- TrN n = if 100 < n then n - 10 else TrN (TrN (n + 11))
*)
Theorem TrN_recursive_characterisation =
        NT_def |> Q.SPECL [‘n’, ‘1’]
               |> SRULE[SPEC “2” NT_FUNPOW, SPEC “0” NT_FUNPOW]
               |> REWRITE_RULE[FUNPOW, TWO, ONE]
               |> REWRITE_RULE[GSYM ONE]

(* |- TrN n = if n <= 101 then 91 else n - 10 *)
Theorem TrN_thm = NT_THM |> Q.SPECL [‘1’, ‘n’] |> SRULE[]

