## `RESQ_RES_TAC`

``` hol4
res_quanTools.RESQ_RES_TAC : tactic
```

------------------------------------------------------------------------

Enriches assumptions by repeatedly resolving restricted universal
quantifications in them against the others.

`RESQ_RES_TAC` uses those assumptions which are restricted universal
quantifications in resolution in a way similar to `RES_TAC`. It calls
`RESQ_RES_THEN` repeatedly until there is no more resolution can be
done. The conclusions of all the new results are returned as additional
assumptions of the subgoal(s). The effect of `RESQ_RES_TAC` on a goal is
to enrich the assumption set with some of its collective consequences.

### Failure

`RESQ_RES_TAC` cannot fail and so should not be unconditionally
`REPEAT`ed.

### See also

[`res_quanTools.RESQ_IMP_RES_TAC`](#res_quanTools.RESQ_IMP_RES_TAC),
[`res_quanTools.RESQ_IMP_RES_THEN`](#res_quanTools.RESQ_IMP_RES_THEN),
[`res_quanTools.RESQ_RES_THEN`](#res_quanTools.RESQ_RES_THEN),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN),
[`Tactic.RES_TAC`](#Tactic.RES_TAC)
