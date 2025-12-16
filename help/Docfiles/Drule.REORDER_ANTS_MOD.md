## `REORDER_ANTS_MOD`

``` hol4
Drule.REORDER_ANTS_MOD : (term list -> term list) -> (thm -> thm) -> thm -> thm
```

------------------------------------------------------------------------

Strips universal quantifiers and antecedents of implications, modifies
the conclusion, and reorders the antecedents

`REORDER_ANTS_MOD f g` combines the effects of `REORDER_ANTS_MOD f` and
applies the function `g` to the ultimate consequent of the theorem, as
does `underAIs`.

### Failure

Fails if `g` fails when applied to the consequent

### See also

[`Drule.DISCH`](#Drule.DISCH), [`Drule.GEN_ALL`](#Drule.GEN_ALL),
[`Drule.REORDER_ANTS`](#Drule.REORDER_ANTS),
[`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Drule.underAIs`](#Drule.underAIs), [`Thm.UNDISCH`](#Thm.UNDISCH)
