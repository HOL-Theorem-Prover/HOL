## `UNDISCH_TM`

``` hol4
Drule.UNDISCH_TM : thm -> term * thm
```

------------------------------------------------------------------------

Undischarges the antecedent of an implicative theorem, also returning
that antecedent.

``` hol4
    A |- t1 ==> t2
   ----------------  UNDISCH_TM
     A, t1 |- t2
```

Note that `UNDISCH_TM` treats `"~u"` as `"u ==> F"`.

### Failure

`UNDISCH_TM` will fail on theorems which are not implications or
negations.

### Comments

If the antecedent already appears in (or is alpha-equivalent to one of)
the hypotheses, it will not be duplicated.

`UNDISCH_TM` is similar to `UNDISCH` except that it also returns the
antecedent concerned, which may be useful, for example, when the new
assumption is subsequently to be discharged

### See also

[`Drule.UNDISCH`](#Drule.UNDISCH), [`Thm.DISCH`](#Thm.DISCH)
