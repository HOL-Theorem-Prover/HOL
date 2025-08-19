## `SELECT_EQ`

``` hol4
Drule.SELECT_EQ : (term -> thm -> thm)
```

------------------------------------------------------------------------

Applies epsilon abstraction to both terms of an equation.

Effects the extensionality of the epsilon operator `@`.

``` hol4
       A |- t1 = t2
   ------------------------  SELECT_EQ "x"      [where x is not free in A]
    A |- (@x.t1) = (@x.t2)
```

### Failure

Fails if the conclusion of the theorem is not an equation, or if the
variable `x` is free in `A`.

### Example

Given a theorem which shows the equivalence of two distinct forms of
defining the property of being an even number:

``` hol4
   th = |- (x MOD 2 = 0) = (?y. x = 2 * y)
```

A theorem giving the equivalence of the epsilon abstraction of each form
is obtained:

``` hol4
   - SELECT_EQ (Term `x:num`) th;
   > val it = |- (@x. x MOD 2 = 0) = (@x. ?y. x = 2 * y) : thm
```

### See also

[`Thm.ABS`](#Thm.ABS), [`Thm.AP_TERM`](#Thm.AP_TERM),
[`Drule.EXISTS_EQ`](#Drule.EXISTS_EQ),
[`Drule.FORALL_EQ`](#Drule.FORALL_EQ),
[`Conv.SELECT_CONV`](#Conv.SELECT_CONV),
[`Drule.SELECT_ELIM`](#Drule.SELECT_ELIM),
[`Drule.SELECT_INTRO`](#Drule.SELECT_INTRO)
