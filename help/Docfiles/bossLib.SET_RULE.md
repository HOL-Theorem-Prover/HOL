## `SET_RULE`

``` hol4
bossLib.SET_RULE : term -> thm
```

------------------------------------------------------------------------

Automatically prove a set-theoretic theorem by reduction to FOL.

An application `DECIDE M`, where `M` is a set-theoretic term, attempts
to automatically prove `M` by reducing basic set-theoretic operators
(`IN`, `SUBSET`, `PSUBSET`, `INTER`, `UNION`, `INSERT`, `DELETE`,
`REST`, `DISJOINT`, `BIGINTER`, `BIGUNION`, `IMAGE`, `SING` and `GSPEC`)
in `M` to their definitions in first-order logic. With `SET_RULE`, many
simple set-theoretic results can be directly proved without finding
needed lemmas in `pred_setTheory`.

### Example

``` hol4
- SET_RULE ``!s t c. DISJOINT s t ==> DISJOINT (s INTER c) (t INTER c)``;
<<HOL message: inventing new type variable names: 'a>>
metis: r[+0+5]+0+0+0+0+1#
> val it = |- !s t c. DISJOINT s t ==> DISJOINT (s INTER c) (t INTER c): thm
```

### Failure

Fails if the underlying resolution machinery used by `METIS_TAC` cannot
prove the goal, e.g. when there are other set operators in the term.

### Comments

`SET_RULE` calls `SET_TAC` without extra lemmas.

### See also

[`bossLib.SET_TAC`](#bossLib.SET_TAC),
[`bossLib.ASM_SET_TAC`](#bossLib.ASM_SET_TAC),
[`bossLib.METIS_TAC`](#bossLib.METIS_TAC)
