## `GSUBST_TAC`

``` hol4
Tactic.GSUBST_TAC : ((term * term) list -> term -> term) -> thm list -> tactic
```

------------------------------------------------------------------------

Makes term substitutions in a goal using a supplied substitution
function.

`GSUBST_TAC` is the basic substitution tactic by means of which other
tactics such as `SUBST_OCCS_TAC` and `SUBST_TAC` are defined. Given a
list `[(v1,w1),...,(vk,wk)]` of pairs of terms and a term `w`, a
substitution function replaces occurrences of `wj` in `w` with `vj`
according to a specific substitution criterion. Such a criterion may be,
for example, to substitute all the occurrences or only some selected
ones of each `wj` in `w`.

Given a substitution function `sfn`,
`GSUBST_TAC sfn [A1|-t1=u1,...,An|-tn=un] (A,t)` replaces occurrences of
`ti` in `t` with `ui` according to `sfn`.

``` hol4
              A ?- t
   =============================  GSUBST_TAC sfn [A1|-t1=u1,...,An|-tn=un]
    A ?- t[u1,...,un/t1,...,tn]
```

The assumptions of the theorems used to substitute with are not added to
the assumptions `A` of the goal, while they are recorded in the proof.
If any `Ai` is not a subset of `A` (up to alpha-conversion), then
`GSUBST_TAC sfn [A1|-t1=u1,...,An|-tn=un]` results in an invalid tactic.

`GSUBST_TAC` automatically renames bound variables to prevent free
variables in `ui` becoming bound after substitution.

### Failure

`GSUBST_TAC sfn [th1,...,thn] (A,t)` fails if the conclusion of each
theorem in the list is not an equation. No change is made to the goal if
the occurrences to be substituted according to the substitution function
`sfn` do not appear in `t`.

`GSUBST_TAC` is used to define substitution tactics such as
`SUBST_OCCS_TAC` and `SUBST_TAC`. It may also provide the user with a
tool for tailoring substitution tactics.

### See also

[`Tactic.SUBST1_TAC`](#Tactic.SUBST1_TAC),
[`Tactic.SUBST_OCCS_TAC`](#Tactic.SUBST_OCCS_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
