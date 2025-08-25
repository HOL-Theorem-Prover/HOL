## `RES_THEN`

``` hol4
Thm_cont.RES_THEN : (thm_tactic -> tactic)
```

------------------------------------------------------------------------

Resolves all implicative assumptions against the rest.

Like the basic resolution function `IMP_RES_THEN`, the resolution tactic
`RES_THEN` performs a single-step resolution of an implication and the
assumptions of a goal. `RES_THEN` differs from `IMP_RES_THEN` only in
that the implications used for resolution are taken from the assumptions
of the goal itself, rather than supplied as an argument.

When applied to a goal `A ?- g`, the tactic `RES_THEN ttac` uses
`RES_CANON` to obtain a set of implicative theorems in canonical form
from the assumptions `A` of the goal. Each of the resulting theorems (if
there are any) will have the form:

``` hol4
   ai |- !x1...xn. ui ==> vi
```

where `ai` is one of the assumptions of the goal. Having obtained these
implications, `RES_THEN` then attempts to match each antecedent `ui` to
each assumption `aj |- aj` in the assumptions `A`. If the antecedent
`ui` of any implication matches the conclusion `aj` of any assumption,
then an instance of the theorem `ai, aj |- vi`, called a 'resolvent', is
obtained by specialization of the variables `x1`, ..., `xn` and type
instantiation, followed by an application of modus ponens. There may be
more than one canonical implication derivable from the assumptions of
the goal and each such implication is tried against every assumption, so
there may be several resolvents (or, indeed, none).

Tactics are produced using the theorem-tactic `ttac` from all these
resolvents (failures of `ttac` at this stage are filtered out) and these
tactics are then applied in an unspecified sequence to the goal. That
is,

``` hol4
   RES_THEN ttac (A ?- g)
```

has the effect of:

``` hol4
   MAP_EVERY (mapfilter ttac [... ; (ai,aj |- vi) ; ...]) (A ?- g)
```

where the theorems `ai,aj |- vi` are all the consequences that can be
drawn by a (single) matching modus-ponens inference from the assumptions
`A` and the implications derived using `RES_CANON` from the assumptions.
The sequence in which the theorems `ai,aj |- vi` are generated and the
corresponding tactics applied is unspecified.

### Failure

Evaluating `RES_THEN ttac th` fails with '`no implication`' if no
implication(s) can be derived from the assumptions of the goal by the
transformation process described under the entry for `RES_CANON`.
Evaluating `RES_THEN ttac (A ?- g)` fails with '`no resolvents`' if no
assumption of the goal `A ?- g` can be resolved with the derived
implication or implications. Evaluation also fails, with '`no tactics`',
if there are resolvents, but for every resolvent `ai,aj |- vi`
evaluating the application `ttac (ai,aj |- vi)` fails---that is, if for
every resolvent `ttac` fails to produce a tactic. Finally, failure is
propagated if any of the tactics that are produced from the resolvents
by `ttac` fails when applied in sequence to the goal.

### See also

[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Tactic.RES_TAC`](#Tactic.RES_TAC)
