## `NEG_DISCH`

``` hol4
Drule.NEG_DISCH : term -> thm -> thm
```

------------------------------------------------------------------------

Discharges an assumption, transforming `|- s ==> F` into `|- ~s`.

When applied to a term `s` and a theorem `A |- t`, the inference rule
`NEG_DISCH` returns the theorem `A - {s} |- s ==> t`, or if `t` is just
`F`, returns the theorem `A - {s} |- ~s`.

``` hol4
          A |- F
   --------------------  NEG_DISCH    [special case]
      A - {s} |- ~s

          A |- t
   --------------------  NEG_DISCH    [general case]
    A - {s} |- s ==> t
```

### Failure

Fails unless the supplied term has type `bool`.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Thm.NOT_ELIM`](#Thm.NOT_ELIM),
[`Thm.NOT_INTRO`](#Thm.NOT_INTRO)
