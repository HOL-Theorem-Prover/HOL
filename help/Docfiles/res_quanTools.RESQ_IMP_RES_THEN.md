## `RESQ_IMP_RES_THEN`

``` hol4
res_quanTools.RESQ_IMP_RES_THEN : thm_tactical
```

------------------------------------------------------------------------

Resolves a restricted universally quantified theorem with the
assumptions of a goal.

The function `RESQ_IMP_RES_THEN` is the basic building block for
resolution using a restricted quantified theorem. It takes a restricted
quantified theorem and transforms it into an implication. This resulting
theorem is used in the resolution.

Given a theorem-tactic `ttac` and a theorem `th`, the theorem-tactical
`RESQ_IMP_RES_THEN` transforms the theorem into an implication `th'`. It
then passes `th'` together with `ttac` to `IMP_RES_THEN` to carry out
the resolution.

### Failure

Evaluating `RESQ_IMP_RES_THEN ttac th` fails if the supplied theorem
`th` is not restricted universally quantified, or if the call to
`IMP_RES_THEN` fails.

### See also

[`res_quanTools.RESQ_IMP_RES_TAC`](#res_quanTools.RESQ_IMP_RES_TAC),
[`res_quanTools.RESQ_RES_THEN`](#res_quanTools.RESQ_RES_THEN),
[`res_quanTools.RESQ_RES_TAC`](#res_quanTools.RESQ_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
