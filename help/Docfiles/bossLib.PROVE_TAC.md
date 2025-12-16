## `PROVE_TAC`

``` hol4
bossLib.PROVE_TAC : thm list -> tactic
```

------------------------------------------------------------------------

Solve a goal with use of hypotheses and supplied lemmas.

An invocation `PROVE_TAC thl` attempts to solve the goal it is applied
to by executing a proof procedure that is semi-complete for pure first
order logic. The assumptions of the goal and the theorems in `thl` are
used. The procedure makes special provision for handling polymorphic and
higher-order values (lambda terms). It also handles conditional
expressions.

### Failure

`PROVE_TAC` fails if it searches to a depth equal to the contents of the
reference variable `mesonLib.max_depth` (set to 30 by default, but
changeable by the user) without finding a proof.

### Comments

`PROVE_TAC` can only progress the goal to a successful proof of the goal
or not at all. In this respect it differs from tactics such as
simplification and rewriting. Its ability to solve existential goals and
to make effective use of transitivity theorems make it a particularly
powerful tactic.

### See also

[`bossLib.PROVE`](#bossLib.PROVE),
[`mesonLib.MESON_TAC`](#mesonLib.MESON_TAC),
[`mesonLib.ASM_MESON_TAC`](#mesonLib.ASM_MESON_TAC),
[`mesonLib.GEN_MESON_TAC`](#mesonLib.GEN_MESON_TAC)
