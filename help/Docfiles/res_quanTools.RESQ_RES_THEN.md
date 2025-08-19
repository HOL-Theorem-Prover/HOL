## `RESQ_RES_THEN`

``` hol4
res_quanTools.RESQ_RES_THEN : thm_tactic -> tactic
```

------------------------------------------------------------------------

Resolves all restricted universally quantified assumptions against other
assumptions of a goal.

Like the function `RESQ_IMP_RES_THEN`, the function `RESQ_RES_THEN`
performs a single step resolution. The difference is that the restricted
universal quantification used in the resolution is taken from the
assumptions.

Given a theorem-tactic `ttac`, applying the tactic `RESQ_RES_THEN ttac`
to a goal `(asml,gl)` has the effect of:

``` hol4
   MAP_EVERY (mapfilter ttac [... ; (ai,aj |- vi) ; ...]) (amsl ?- g)
```

where the theorems `ai,aj |- vi` are all the consequences that can be
drawn by a (single) matching modus-ponens inference from the assumptions
`amsl` and the implications derived from the restricted universal
quantifications in the assumptions.

### Failure

Evaluating `RESQ_RES_TAC ttac th` fails if there are no restricted
universal quantifications in the assumptions, or if the theorem-tactic
`ttac` applied to all the consequences fails.

### See also

[`res_quanTools.RESQ_IMP_RES_TAC`](#res_quanTools.RESQ_IMP_RES_TAC),
[`res_quanTools.RESQ_IMP_RES_THEN`](#res_quanTools.RESQ_IMP_RES_THEN),
[`res_quanTools.RESQ_RES_TAC`](#res_quanTools.RESQ_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
