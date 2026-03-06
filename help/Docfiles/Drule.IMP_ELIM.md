## `IMP_ELIM`

``` hol4
Drule.IMP_ELIM : (thm -> thm)
```

------------------------------------------------------------------------

Transforms `|- s ==> t` into `|- ~s \/ t`.

When applied to a theorem `A |- s ==> t`, the inference rule `IMP_ELIM`
returns the theorem `A |- ~s \/ t`.

``` hol4
    A |- s ==> t
   --------------  IMP_ELIM
    A |- ~s \/ t
```

### Failure

Fails unless the theorem is implicative.

### See also

[`Thm.NOT_INTRO`](#Thm.NOT_INTRO), [`Thm.NOT_ELIM`](#Thm.NOT_ELIM)
