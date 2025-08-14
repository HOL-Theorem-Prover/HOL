## `METIS_TAC`

``` hol4
bossLib.METIS_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Performs first-order resolution to try to prove goal

When `METIS_TAC ths` is applied to a goal `(asl,w)`, it attempts to find
a resolution proof that the provided theorems in `ths` and the
assumptions in `asl` together imply the goal in `w`. `METIS_TAC`
implements ordered resolution and as such its ability to reason about
equality is generally better than `MESON_TAC`'s.

### Failure

Fails if the underlying resolution machinery cannot prove the goal.
`METIS_TAC` may also consume more and more time, and more and more
memory as a search for a proof proceeds without ever explicitly failing.

### Comments

The alternative lower-case spelling `metis_tac` is also available for
this tactic from the `bossLib` structure. There is no "metis" entrypoint
that allows one to ignore the assumptions (with "meson", there is both
`MESON_TAC` and `ASM_MESON_TAC`).

### See also

[`mesonLib.MESON_TAC`](#mesonLib.MESON_TAC)
