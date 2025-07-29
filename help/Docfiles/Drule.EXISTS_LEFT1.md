## `EXISTS_LEFT1`

``` hol4
Drule.EXISTS_LEFT1 : term -> thm -> thm
```

------------------------------------------------------------------------

Existentially quantifes hypotheses of a theorem.

In this example, assume that `h1` and `h3` (only) involve the free
variable `x`.

``` hol4
      h1, h2, h3 |- t
   --------------------- EXISTS_LEFT1 ``x``
   ?x. h1 /\ h3, h2 |- t
```

### Failure

`EXISTS_LEFT1` will fail unless the term supplied is a free variable
which appears in one or more hypotheses but not the conclusion of the
given theorem

### Example

Where `th` is `[p, q, g x, h y, f x y] |- r`, and `fvx` and `fvy` are
``` ``x`` ``` and ``` ``y`` ```,

`EXISTS_LEFT1 fvx th` is `[p, q, h y, ?x. g x /\ f x y] |- r`

`EXISTS_LEFT1 fvy th` is `[p, q, g x, ?y. h y /\ f x y] |- r`

### Comments

`EXISTS_LEFT1 fv` is just like `EXISTS_LEFT [fv]` except that
`EXISTS_LEFT1 fv` fails where `EXISTS_LEFT [fv]` returns the theorem
unchanged

See `EXISTS_LEFT` for further discussion

### See also

[`Drule.EXISTS_LEFT`](#Drule.EXISTS_LEFT), [`Thm.CHOOSE`](#Thm.CHOOSE),
[`Thm.EXISTS`](#Thm.EXISTS), [`Tactic.CHOOSE_TAC`](#Tactic.CHOOSE_TAC),
[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
