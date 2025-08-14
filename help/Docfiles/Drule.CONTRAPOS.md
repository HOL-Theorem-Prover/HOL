## `CONTRAPOS`

``` hol4
Drule.CONTRAPOS : (thm -> thm)
```

------------------------------------------------------------------------

Deduces the contrapositive of an implication.

When applied to a theorem `A |- s ==> t`, the inference rule `CONTRAPOS`
returns its contrapositive, `A |- ~t ==> ~s`.

``` hol4
     A |- s ==> t
   ----------------  CONTRAPOS
    A |- ~t ==> ~s
```

### Failure

Fails unless the theorem is an implication.

### See also

[`Thm.CCONTR`](#Thm.CCONTR), [`Drule.CONTR`](#Drule.CONTR),
[`Conv.CONTRAPOS_CONV`](#Conv.CONTRAPOS_CONV),
[`Thm.NOT_ELIM`](#Thm.NOT_ELIM)
