## `ASM_MESON_TAC`

``` hol4
mesonLib.ASM_MESON_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Performs first order proof search to prove the goal, using the
assumptions and the theorems given.

`ASM_MESON_TAC` is identical in behaviour to `MESON_TAC` except that it
uses the assumptions of a goal as well as the provided theorems.

### Failure

`ASM_MESON_TAC` fails if it can not find a proof of the goal with depth
less than or equal to the `mesonLib.max_depth` value.

### See also

[`mesonLib.GEN_MESON_TAC`](#mesonLib.GEN_MESON_TAC),
[`mesonLib.MESON_TAC`](#mesonLib.MESON_TAC)
