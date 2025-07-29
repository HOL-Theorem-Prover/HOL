## `selectDB`

``` hol4
DB.selectDB : DB.selector list -> DB.public_data list
```

------------------------------------------------------------------------

Searches the theorem database with multiple conjoined selectors

A call to `DB.selectDB [sel1, sel2, ..., seln]` returns a list of
theorems from the theorem database that match all of the criteria
embodied by `sel1`, `sel2`, etc. The selectors are of three different
forms:

``` hol4
   SelTM term | SelNM string | SelTHY string
```

The selector `SelTM t` matches any theorem that has a sub-term matching
the term `t`. The selector `SelNM s` matches any theorem whose name
matches the string `s`, using the regular-expression-like matching
syntax described in the documentation for `DB.find`. Finally,
`SelThy thy` matches a theorem if that theorem comes from theory `thy`.

### Failure

Never fails.

### Example

``` hol4
> DB.selectDB [SelTM “_ /\ _”, SelTHY "bool", SelNM "ASSOC"];
val it =
   [(("bool", "CONJ_ASSOC"),
     (⊢ ∀t1 t2 t3. t1 ∧ t2 ∧ t3 ⇔ (t1 ∧ t2) ∧ t3, Thm))]: 
   public_data list
```

### Comments

Allows for more powerful searches than other entrypoints in `DB`.

### See also

[`DB.find`](#DB.find), [`DB.match`](#DB.match)
