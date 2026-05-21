## `SELECT_CONV`

``` hol4
Conv.SELECT_CONV : conv
```

------------------------------------------------------------------------

Eliminates an epsilon term by introducing an existential quantifier.

The conversion `SELECT_CONV` expects a boolean term of the form
`P[@x.P[x]/x]`, which asserts that the epsilon term `@x.P[x]` denotes a
value, `x` say, for which `P[x]` holds. This assertion is equivalent to
saying that there exists such a value, and `SELECT_CONV` applied to a
term of this form returns the theorem `|- P[@x.P[x]/x] = ?x. P[x]`.

### Failure

Fails if applied to a term that is not of the form `P[@x.P[x]/x]`.

### Example

``` hol4
SELECT_CONV (Term `(@n. n < m) < m`);
val it = |- (@n. n < m) < m = (?n. n < m) : thm
```

Particularly useful in conjunction with `CONV_TAC` for proving
properties of values denoted by epsilon terms. For example, suppose that
one wishes to prove the goal

``` hol4
   ([0 < m], (@n. n < m) < SUC m)
```

Using the built-in arithmetic theorem

``` hol4
   LESS_SUC  |- !m n. m < n ==> m < (SUC n)
```

this goal may be reduced by the tactic `MATCH_MP_TAC LESS_SUC` to the
subgoal

``` hol4
   ([0 < m], (@n. n < m) < m)
```

This is now in the correct form for using `CONV_TAC SELECT_CONV` to
eliminate the epsilon term, resulting in the existentially quantified
goal

``` hol4
   ([0 < m], ?n. n < m)
```

which is then straightforward to prove.

### See also

[`Drule.SELECT_ELIM`](#Drule.SELECT_ELIM),
[`Drule.SELECT_INTRO`](#Drule.SELECT_INTRO),
[`Drule.SELECT_RULE`](#Drule.SELECT_RULE)
