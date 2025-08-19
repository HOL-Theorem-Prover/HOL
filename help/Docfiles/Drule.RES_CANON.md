## `RES_CANON`

``` hol4
Drule.RES_CANON : (thm -> thm list)
```

------------------------------------------------------------------------

Put an implication into canonical form for resolution.

All the HOL resolution tactics (e.g. `IMP_RES_TAC`) work by using modus
ponens to draw consequences from an implicative theorem and the
assumptions of the goal. Some of these tactics derive this implication
from a theorem supplied explicitly the user (or otherwise from 'outside'
the goal) and some obtain it from the assumptions of the goal itself.
But in either case, the supplied theorem or assumption is first
transformed into a list of implications in 'canonical' form by the
function `RES_CANON`.

The theorem argument to `RES_CANON` should be either be an implication
(which can be universally quantified) or a theorem from which an
implication can be derived using the transformation rules discussed
below. Given such a theorem, `RES_CANON` returns a list of implications
in canonical form. It is the implications in this resulting list that
are used by the various resolution tactics to infer consequences from
the assumptions of a goal.

The transformations done by `RES_CANON th` to the theorem `th` are as
follows. First, if `th` is a negation `A |- ~t`, this is converted to
the implication `A |- t ==> F`. The following inference rules are then
applied repeatedly, until no further rule applies. Conjunctions are
split into their components and equivalence (boolean equality) is split
into implication in both directions:

``` hol4
      A |- t1 /\ t2                         A |- t1 = t2
   --------------------           ----------------------------------
    A |- t1    A |- t2             A |- t1 ==> t2    A |- t2 ==> t1
```

Conjunctive antecedents are transformed by:

``` hol4
                A |- (t1 /\ t2) ==> t
   ---------------------------------------------------
    A |- t1 ==> (t2 ==> t)     A |- t2 ==> (t1 ==> t)
```

and disjunctive antecedents by:

``` hol4
        A |- (t1 \/ t2) ==> t
   --------------------------------
    A |- t1 ==> t    A |- t2 ==> t
```

The scope of universal quantifiers is restricted, if possible:

``` hol4
    A |- !x. t1 ==> t2
   --------------------         [if x is not free in t1]
    A |- t1 ==> !x. t2
```

and existentially-quantified antecedents are eliminated by:

``` hol4
      A |- (?x. t1) ==> t2
   ---------------------------  [x' chosen so as not to be free in t2]
    A |- !x'. t1[x'/x] ==> t2
```

Finally, when no further applications of the above rules are possible,
and the theorem is an implication:

``` hol4
   A |- !x1...xn. t1 ==> t2
```

then the theorem `A u {t1} |- t2` is transformed by a recursive
application of `RES_CANON` to get a list of theorems:

``` hol4
   [A u {t1} |- t21 , ... , A u {t1} |- t2n]
```

and the result of discharging `t1` from these theorems:

``` hol4
   [A |- !x1...xn. t1 ==> t21 , ... , A |- !x1...xn. t1 ==> t2n]
```

is returned. That is, the transformation rules are recursively applied
to the conclusions of all implications.

### Failure

`RES_CANON th` fails if no implication(s) can be derived from `th` using
the transformation rules shown above.

### Example

The uniqueness of the remainder `k MOD n` is expressed in HOL by the
built-in theorem `MOD_UNIQUE`:

``` hol4
   |- !n k r. (?q. (k = (q * n) + r) /\ r < n) ==> (k MOD n = r)
```

For this theorem, the canonical list of implications returned by
`RES_CANON` is as follows:

``` hol4
   - RES_CANON MOD_UNIQUE;
   > val it =
       [|- !r n q k. (k = q * n + r) ==> r < n ==> (k MOD n = r),
        |- !n r. r < n ==> !q k. (k = q * n + r) ==> (k MOD n = r)] : thm list
```

The existentially-quantified, conjunctive, antecedent has given rise to
two implications, and the scope of universal quantifiers has been
restricted to the conclusions of the resulting implications wherever
possible.

The primary use of `RES_CANON` is for the (internal) pre-processing
phase of the built-in resolution tactics `IMP_RES_TAC`, `IMP_RES_THEN`,
`RES_TAC`, and `RES_THEN`. But the function `RES_CANON` is also made
available at top-level so that users can call it to see the actual form
of the implications used for resolution in any particular case.

### See also

[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
