open HolKernel Parse boolLib bossLib

local open containerTheory in end

val _ = new_theory "tailrecAckermann"

val _ = Hol_datatype `work = DO of num => num | PENDING of num`;

val wsize_def = Define`
  (wsize (DO n m) = (2 * n, m)) ∧
  (wsize (PENDING n) = (2 * n + 1, 0))
`

val A'_defn = Hol_defn "A'" `
  A' results stk =
    case stk of
        [] => HD results
      | DO 0 m :: rest => A' ((m + 1)::results) rest
      | DO (SUC n0) 0 :: rest => A' results (DO n0 1 :: rest)
      | DO (SUC n0) (SUC m0) :: rest =>
          A' results (DO (SUC n0) m0::PENDING n0::rest)
      | PENDING n :: rest => A' (TL results) (DO n (HD results) :: rest)
`
open lcsymtacs
val (A'_def, A'_ind) = Defn.tprove(A'_defn,
  WF_REL_TAC `inv_image (mlt1 ($< LEX $<)) (LIST_TO_BAG o MAP wsize o SND)`
  >- simp[bagTheory.WF_mlt1, pairTheory.WF_LEX, prim_recTheory.WF_LESS] >>
  simp[wsize_def, bagTheory.mlt1_def] >> rpt strip_tac >| [
    map_every qexists_tac [`(2 * SUC n0, SUC m0)`,
                           `{|(2 * n0 + 1, 0); (2 * SUC n0, m0)|}`,
                           `LIST_TO_BAG (MAP wsize rest)`
                          ] >>
    simp[bagTheory.BAG_UNION_INSERT, DISJ_IMP_THM, FORALL_AND_THM] >>
    simp[bagTheory.BAG_INSERT_commutes],
    map_every qexists_tac [`(2 * SUC n0, 0)`,
                           `{| (2 * n0, 1) |}`,
                           `LIST_TO_BAG (MAP wsize rest)`] >>
    simp[bagTheory.BAG_UNION_INSERT, DISJ_IMP_THM, FORALL_AND_THM],
    map_every qexists_tac [`(0,m)`, `{||}`, `LIST_TO_BAG (MAP wsize rest)`] >>
    simp[bagTheory.BAG_UNION_INSERT, DISJ_IMP_THM, FORALL_AND_THM],
    map_every qexists_tac [`(2*n + 1, 0)`, `{| (2 * n, HD results) |}`,
                           `LIST_TO_BAG (MAP wsize rest)`] >>
    simp[bagTheory.BAG_UNION_INSERT, DISJ_IMP_THM, FORALL_AND_THM]
  ])

val _ = save_thm("A'_def", A'_def)
val _ = computeLib.add_persistent_funs ["A'_def"]

(* computing A(3,4) = 125 terminates in reasonable time:

> time EVAL ``A' [] [DO 3 4]``
runtime: 7.044s,    gctime: 5.984s,     systime: 0.09601s.
val it = |- A' [] [DO 3 4] = 125: thm

A(4,0) is also fine.  A(4,1) certainly isn't.

*)

(* I haven't given any thought to proving this formulation equivalent to
   the traditional definition *)

val _ = export_theory()
