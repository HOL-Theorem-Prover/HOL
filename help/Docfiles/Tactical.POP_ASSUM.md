## `POP_ASSUM`

``` hol4
Tactical.POP_ASSUM : thm_tactic -> tactic
```

------------------------------------------------------------------------

Applies tactic generated from the first element of a goal's assumption
list.

When applied to a theorem-tactic and a goal, `POP_ASSUM` applies the
theorem-tactic to the `ASSUME`d first element of the assumption list,
and applies the resulting tactic to the goal without the first
assumption in its assumption list:

``` hol4
   POP_ASSUM f ({A1,...,An} ?- t) = f (A1 |- A1) ({A2,...,An} ?- t)
```

### Failure

Fails if the assumption list of the goal is empty, or the theorem-tactic
fails when applied to the popped assumption, or if the resulting tactic
fails when applied to the goal (with depleted assumption list).

### Comments

It is possible simply to use the theorem `ASSUME A1` as required rather
than use `POP_ASSUM`; this will also maintain `A1` in the assumption
list, which is generally useful. In addition, this approach can equally
well be applied to assumptions other than the first.

There are admittedly times when `POP_ASSUM` is convenient, but it is
most unwise to use it if there is more than one assumption in the
assumption list, since this introduces a dependency on the ordering,
which is vulnerable to changes in the HOL system.

Another point to consider is that if the relevant assumption has been
obtained by `DISCH_TAC`, it is often cleaner to use `DISCH_THEN` with a
theorem-tactic. For example, instead of:

``` hol4
   DISCH_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
```

one might use

``` hol4
   DISCH_THEN (SUBST1_TAC o SYM)
```

The tactical `POP_ASSUM` is also available under the lower-case version
of the name, `pop_assum`.

### Example

The goal:

``` hol4
   {4 = SUC x} ?- x = 3
```

can be solved by:

``` hol4
   POP_ASSUM
    (fn th => REWRITE_TAC[REWRITE_RULE[num_CONV “4”, INV_SUC_EQ] th])
```

Making more delicate use of an assumption than rewriting or resolution
using it.

### See also

[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Tactical.POP_ASSUM_LIST`](#Tactical.POP_ASSUM_LIST),
[`Tactical.POP_LAST_ASSUM`](#Tactical.POP_LAST_ASSUM),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
