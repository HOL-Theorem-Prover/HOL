## `gs`

``` hol4
bossLib.gs : thm list -> tactic
```

------------------------------------------------------------------------

Simplifies assumptions and goal conclusion until a normal form is
reached.

A call to `gs ths` produces a simplification tactic that repeatedly
simplifies with the theorems `ths`, the stateful simpset, the natural
number arithmetic decision procedure and normalizer, and let-elimination
(as done by `simp`) over both a goal's assumptions and the goal's
conclusion.

Assumptions are simplified first, with assumption terms simplified in
turn in a context that includes all of the other assumptions. After
simplification, if an assumption has been reduced to `T` (truth), it is
dropped. Otherwise, it is added back to the assumption list using
`STRIP_ASSUME_TAC`. After this process of assumption simplification
produces no further change (assessed using `CHANGED_TAC`), the goal's
conclusion is also simplified, in a context that assumes all of the (now
simplified) asssumptions.

Theorems with restrictions (`Once`, `Ntimes`) passed to the `gs` tactic
will not have those restrictions refreshed as invocations of the base
simplification procedure are repeated. This means that the restricted
theorems will likely only be applied to the first assumption where the
left-hand-sides match.

### Failure

Never fails, but may loop.

### Example

The theorem `SUB_CANCEL` has two preconditions:

``` hol4
   > arithmeticTheory.SUB_CANCEL;
   val it = ⊢ ∀p n m. n ≤ p ∧ m ≤ p ⇒ (p − n = p − m ⇔ n = m): thm
```

If those preconditions are distributed awkwardly in a goal, neither `fs`
nor `rfs` (which make passes over the assumptions in a particular order)
may be able to apply the rewrite. However, `gs` will make progress:

``` hol4
   x ≤ b, b - x = b - y, y ≤ b   ?- x * y < 10
  ==============================================  gs[SUB_CANCEL]
           y ≤ b, x = y          ?- y ** 2 < 10
```

### Comments

The accompanying functions `gvs`, `gnvs` and `gns` are similar, but
tweak the behaviours slightly. The functions with `v` in their name
eliminate equalities (the `x = y` in the example above, say), and the
functions with `n` in the name do not use `STRIP_ASSUME_TAC` when adding
assumptions back to the goal. The latter can prevent case-splits.

The `rgs` variant attacks the assumptions in the reverse order to `gs`.
The latter simplifies older assumptions using newer assumptions, but
`rgs` uses the opposite order. If, for example, the assumption list
includes both `0 < n` and `n ≠ 0`, then `gs` will preserve one of these
and `rgs` will preserve the other.

### See also

[`Tactical.CHANGED_TAC`](#Tactical.CHANGED_TAC),
[`bossLib.simp`](#bossLib.simp)
