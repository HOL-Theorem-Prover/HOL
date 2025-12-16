## `ANTE_RES_THEN`

``` hol4
Thm_cont.ANTE_RES_THEN : thm_tactical
```

------------------------------------------------------------------------

Resolves implicative assumptions with an antecedent.

Given a theorem-tactic `ttac` and a theorem `A |- t`, the function
`ANTE_RES_THEN` produces a tactic that attempts to match `t` to the
antecedent of each implication

``` hol4
   Ai |- !x1...xn. ui ==> vi
```

(where `Ai` is just `!x1...xn. ui ==> vi`) that occurs among the
assumptions of a goal. If the antecedent `ui` of any implication matches
`t`, then an instance of `Ai u A |- vi` is obtained by specialization of
the variables `x1`, ..., `xn` and type instantiation, followed by an
application of modus ponens. Because all implicative assumptions are
tried, this may result in several modus-ponens consequences of the
supplied theorem and the assumptions. Tactics are produced using `ttac`
from all these theorems, and these tactics are applied in sequence to
the goal. That is,

``` hol4
   ANTE_RES_THEN ttac (A |- t) g
```

has the effect of:

``` hol4
   MAP_EVERY ttac [A1 u A |- v1, ..., Am u A |- vm] g
```

where the theorems `Ai u A |- vi` are all the consequences that can be
drawn by a (single) matching modus-ponens inference from the
implications that occur among the assumptions of the goal `g` and the
supplied theorem `A |- t`. Any negation `~v` that appears among the
assumptions of the goal is treated as an implication `v ==> F`. The
sequence in which the theorems `Ai u A |- vi` are generated and the
corresponding tactics applied is unspecified.

### Failure

`ANTE_RES_THEN ttac (A |- t)` fails when applied to a goal `g` if any of
the tactics produced by `ttac (Ai u A |- vi)`, where `Ai u A |- vi` is
the `i`th resolvent obtained from the theorem `A |- t` and the
assumptions of `g`, fails when applied in sequence to `g`.

Painfully detailed proof hacking.

### See also

[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
