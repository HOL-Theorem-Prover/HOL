## `EQT_INTRO`

``` hol4
Drule.EQT_INTRO : thm -> thm
```

------------------------------------------------------------------------

Introduces equality with `T`.

``` hol4
      A |- tm
   -------------  EQT_INTRO
    A |- tm = T
```

### Failure

Never fails.

### See also

[`Drule.EQT_ELIM`](#Drule.EQT_ELIM),
[`Drule.EQF_ELIM`](#Drule.EQF_ELIM),
[`Drule.EQF_INTRO`](#Drule.EQF_INTRO)
