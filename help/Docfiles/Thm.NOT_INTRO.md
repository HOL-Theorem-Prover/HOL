## `NOT_INTRO`

``` hol4
Thm.NOT_INTRO : (thm -> thm)
```

------------------------------------------------------------------------

Transforms `|- t ==> F` into `|- ~t`.

When applied to a theorem `A |- t ==> F`, the inference rule `NOT_INTRO`
returns the theorem `A |- ~t`.

``` hol4
    A |- t ==> F
   --------------  NOT_INTRO
      A |- ~t
```

### Failure

Fails unless the theorem has an implicative conclusion with `F` as the
consequent.

### See also

[`Drule.IMP_ELIM`](#Drule.IMP_ELIM), [`Thm.NOT_ELIM`](#Thm.NOT_ELIM)
