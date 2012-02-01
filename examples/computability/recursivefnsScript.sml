open HolKernel Parse boolLib bossLib

open listTheory rich_listTheory
open primrecfnsTheory

val _ = new_theory "recursivefns"

val minimise_def = Define`
  minimise f l =
    if (∃n. (f (n::l) = SOME 0) ∧ ∀i. i < n ⇒ ∃m. 0 < m ∧ (f (i::l) = SOME m))
    then
      SOME (@n. (f (n :: l) = SOME 0) ∧
                ∀i. i < n ⇒ ∃m. 0 < m ∧ (f (i::l) = SOME m))
    else NONE
`;

val recCn_def = Define`
  recCn (f:num list -> num option) gs l =
         let results = MAP (λg : num list -> num option. g l) gs
         in
           if EVERY (λr. r ≠ NONE) results then f (MAP THE results)
           else NONE
`;

val recPr_def = Define`
  recPr zf sf l =
    case l of
      [] => zf []
    | 0::t => zf t
    | SUC n::t => case recPr zf sf (n :: t) of
                    NONE => NONE
                  | SOME r => sf (n::r::t)
`;

val (recfn_rules, recfn_ind, recfn_cases) = Hol_reln`
  recfn (SOME o K 0) 1 ∧
  recfn (SOME o succ) 1 ∧
  (∀i n. i < n ⇒ recfn (SOME o proj i) n) ∧
  (∀f gs m. recfn f (LENGTH gs) ∧ EVERY (λg. recfn g m) gs ⇒
            recfn (recCn f gs) m) ∧
  (∀zf sf n. recfn zf (n - 1) ∧ recfn sf (n + 1) ⇒ recfn (recPr zf sf) n) ∧
  (∀f n. 0 < n ∧ recfn f (n + 1) ⇒ recfn (minimise f) n)
`;

val recfn_rulesl = CONJUNCTS recfn_rules
val recfnCn = save_thm("recfnCn", List.nth(recfn_rulesl, 3))
val recfnPr = save_thm("recfnPr", List.nth(recfn_rulesl, 4))

val primrec_recfn = store_thm(
  "primrec_recfn",
  ``∀f n. primrec f n ⇒ recfn (SOME o f) n``,
  HO_MATCH_MP_TAC strong_primrec_ind THEN SRW_TAC [][recfn_rules] THENL [
    `SOME o Cn f gs = recCn (SOME o f) (MAP (λg. SOME o g) gs)`
       by SRW_TAC [][FUN_EQ_THM, recCn_def, LET_THM, MAP_MAP_o,
                     combinTheory.o_ABS_R, EVERY_MAP, Cn_def] THEN
    SRW_TAC [][] THEN MATCH_MP_TAC recfnCn THEN
    SRW_TAC [][EVERY_MAP] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM],

    `SOME o Pr f f' = recPr (SOME o f) (SOME o f')`
       by (SIMP_TAC (srw_ss()) [FUN_EQ_THM] THEN Q.X_GEN_TAC `list` THEN
           `(list = []) ∨ ∃m ms. list = m :: ms`
              by (Cases_on `list` THEN SRW_TAC [][])
             THEN1 SRW_TAC [][Once recPr_def, Once Pr_def] THEN
           SRW_TAC [][] THEN
           Induct_on `m` THEN SRW_TAC [][Once recPr_def] THEN
           POP_ASSUM (SUBST1_TAC o SYM) THEN SRW_TAC [][]) THEN
    SRW_TAC [][] THEN MATCH_MP_TAC recfnPr THEN SRW_TAC [ARITH_ss][]
  ]);

val totalrec_def = Define`
  totalrec f n = recfn f n ∧ ∀l. (LENGTH l = n) ⇒ ∃m. f l = SOME m
`;








val _ = export_theory()
