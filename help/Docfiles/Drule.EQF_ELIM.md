## `EQF_ELIM`

``` hol4
Drule.EQF_ELIM : (thm -> thm)
```

------------------------------------------------------------------------

Replaces equality with `F` by negation.

``` hol4
    A |- tm = F
   -------------  EQF_ELIM
     A |- ~tm
```

### Failure

Fails if the argument theorem is not of the form `A |- tm = F`.

### See also

[`Drule.EQF_INTRO`](#Drule.EQF_INTRO),
[`Drule.EQT_ELIM`](#Drule.EQT_ELIM),
[`Drule.EQT_INTRO`](#Drule.EQT_INTRO)
