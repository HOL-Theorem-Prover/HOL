open HolKernel Parse boolLib bossLib;

open finite_mapTheory sortingTheory

val _ = new_theory "countchars";

val _ = ParseExtras.tight_equality()

Definition countchars_def[simp]:
  countchars fm [] = fm ∧
  countchars fm (c::cs) =
    let fm' =
      case FLOOKUP fm c of
        NONE => fm |+ (c,1)
      | SOME n => fm |+ (c, n + 1)
    in
      countchars fm' cs
End

Definition countchars_aux_def:
  countchars_aux fm s i =
    if i = 0 then fm
    else
      let c = EL (i - 1) s in
      let fm' =
        case FLOOKUP fm c of
          NONE => fm |+ (c,1)
        | SOME n => fm |+ (c, n + 1)
      in
        countchars_aux fm' s (i - 1)
End

Theorem countchars_PERM:
  ∀s1 s2. PERM s1 s2 ⇒ ∀fm. countchars fm s1 = countchars fm s2
Proof
  Induct_on ‘PERM’ >> simp[countchars_def] >> rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> fs[FLOOKUP_UPDATE] >> rfs[] >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> metis_tac[FUPDATE_COMMUTES]
QED

Theorem aux_correctness:
  ∀i fm s. i ≤ LENGTH s ⇒ countchars_aux fm s i = countchars fm (TAKE i s)
Proof
  Induct_on ‘i’ >> simp[Once countchars_aux_def] >> rw[] >>
  qmatch_abbrev_tac ‘LHS = _’ >>
  ‘LHS = countchars fm (EL i s :: TAKE i s)’ by simp[Abbr‘LHS’] >>
  pop_assum SUBST1_TAC >> irule countchars_PERM >>
  simp[PERM_CONS_EQ_APPEND] >> map_every qexists_tac [‘TAKE i s’, ‘[]’] >>
  simp[GSYM rich_listTheory.SNOC_EL_TAKE]
QED

Theorem countchars_EQN: countchars fm s = countchars_aux fm s (LENGTH s)
Proof simp[aux_correctness]
QED

Theorem correctness:
  ∀fm0 s fm.
     countchars fm0 s =
       FUN_FMAP (λc. LENGTH (FILTER ((=) c) s) +
                     (case FLOOKUP fm0 c of NONE => 0 | SOME i => i))
                (FDOM fm0 ∪ set s)
Proof
  Induct_on ‘s’ >> simp[countchars_def, fmap_EXT, FUN_FMAP_DEF]
  >- simp[FLOOKUP_DEF] >>
  rpt gen_tac >> Cases_on `FLOOKUP fm0 h` >> fs[flookup_thm] >>
  simp[FLOOKUP_DEF] >>
  dsimp[FUN_FMAP_DEF, FAPPLY_FUPDATE_THM] >> rw[] >> fs[] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

val _ = export_theory();
