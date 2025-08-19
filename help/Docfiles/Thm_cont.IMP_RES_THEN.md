## `IMP_RES_THEN`

``` hol4
Thm_cont.IMP_RES_THEN : thm_tactical
```

------------------------------------------------------------------------

Resolves an implication with the assumptions of a goal.

The function `IMP_RES_THEN` is the basic building block for resolution
in HOL. This is not full higher-order, or even first-order, resolution
with unification, but simply one way simultaneous pattern-matching
(resulting in term and type instantiation) of the antecedent of an
implicative theorem to the conclusion of another theorem (the candidate
antecedent).

Given a theorem-tactic `ttac` and a theorem `th`, the theorem-tactical
`IMP_RES_THEN` uses `RES_CANON` to derive a canonical list of
implications from `th`, each of which has the form:

``` hol4
   Ai |- !x1...xn. ui ==> vi
```

`IMP_RES_THEN` then produces a tactic that, when applied to a goal
`A ?- g` attempts to match each antecedent `ui` to each assumption
`aj |- aj` in the assumptions `A`. If the antecedent `ui` of any
implication matches the conclusion `aj` of any assumption, then an
instance of the theorem `Ai u {aj} |- vi`, called a 'resolvent', is
obtained by specialization of the variables `x1`, ..., `xn` and type
instantiation, followed by an application of modus ponens. There may be
more than one canonical implication and each implication is tried
against every assumption of the goal, so there may be several resolvents
(or, indeed, none).

Tactics are produced using the theorem-tactic `ttac` from all these
resolvents (failures of `ttac` at this stage are filtered out) and these
tactics are then applied in an unspecified sequence to the goal. That
is,

``` hol4
   IMP_RES_THEN ttac th  (A ?- g)
```

has the effect of:

``` hol4
   MAP_EVERY (mapfilter ttac [... , (Ai u {aj} |- vi) , ...]) (A ?- g)
```

where the theorems `Ai u {aj} |- vi` are all the consequences that can
be drawn by a (single) matching modus-ponens inference from the
assumptions of the goal `A ?- g` and the implications derived from the
supplied theorem `th`. The sequence in which the theorems
`Ai u {aj} |- vi` are generated and the corresponding tactics applied is
unspecified.

### Failure

Evaluating `IMP_RES_THEN ttac th` fails if the supplied theorem `th` is
not an implication, or if no implications can be derived from `th` by
the transformation process described under the entry for `RES_CANON`.
Evaluating `IMP_RES_THEN ttac th (A ?- g)` fails if no assumption of the
goal `A ?- g` can be resolved with the implication or implications
derived from `th`. Evaluation also fails if there are resolvents, but
for every resolvent `Ai u {aj} |- vi` evaluating the application
`ttac (Ai u {aj} |- vi)` fails---that is, if for every resolvent `ttac`
fails to produce a tactic. Finally, failure is propagated if any of the
tactics that are produced from the resolvents by `ttac` fails when
applied in sequence to the goal.

### Example

The following example shows a straightforward use of `IMP_RES_THEN` to
infer an equational consequence of the assumptions of a goal, use it
once as a substitution in the conclusion of goal, and then 'throw it
away'. Suppose the goal is:

``` hol4
   a + n = a  ?- !k. k - n = k
```

By the built-in theorem:

``` hol4
   ADD_INV_0 = |- !m n. (m + n = m) ==> (n = 0)
```

the assumption of this goal implies that `n` equals `0`. A single-step
resolution with this theorem followed by substitution:

``` hol4
   IMP_RES_THEN SUBST1_TAC ADD_INV_0
```

can therefore be used to reduce the goal to:

``` hol4
   a + n = a  ?- !k. k - 0 = m
```

Here, a single resolvent `a + n = a |- n = 0` is obtained by matching
the antecedent of `ADD_INV_0` to the assumption of the goal. This is
then used to substitute `0` for `n` in the conclusion of the goal.

### See also

[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
