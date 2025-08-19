## `RESQ_IMP_RES_TAC`

``` hol4
res_quanTools.RESQ_IMP_RES_TAC : thm_tactic
```

------------------------------------------------------------------------

Repeatedly resolves a restricted universally quantified theorem with the
assumptions of a goal.

The function `RESQ_IMP_RES_TAC` performs repeatedly resolution using a
restricted quantified theorem. It takes a restricted quantified theorem
and transforms it into an implication. This resulting theorem is used in
the resolution.

Given a theorem `th`, the theorem-tactic `RESQ_IMP_RES_TAC` applies
`RESQ_IMP_RES_THEN` repeatedly to resolve the theorem with the
assumptions.

### Failure

Never fails

### See also

[`res_quanTools.RESQ_IMP_RES_THEN`](#res_quanTools.RESQ_IMP_RES_THEN),
[`res_quanTools.RESQ_RES_THEN`](#res_quanTools.RESQ_RES_THEN),
[`res_quanTools.RESQ_RES_TAC`](#res_quanTools.RESQ_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
