## `REORDER_ANTS`

``` hol4
Drule.REORDER_ANTS : (term list -> term list) -> thm -> thm
```

------------------------------------------------------------------------

Strips universal quantifiers and antecedents of implications and
reorders the antecedents

``` hol4
   |- !x. a1 ==> !y. a2 ==> !z. a3 ==> !u. t
   ----------------------------------------- REORDER_ANTS rev
       |- a3 ==> a2 ==> a1 ==> t
```

### Failure

No failure. Can leave the supplied theorem unchanged.

But a choice of `f` other than reordering a list of terms will give a
result with assumptions remaining or superfluous antecedents

### Comments

For simplicity, doesn't try to reinsert quantifiers in appropriate
places. If required, apply GEN_ALL to the resulting theorem.

### See also

[`Drule.REORDER_ANTS_MOD`](#Drule.REORDER_ANTS_MOD),
[`Drule.SPEC_ALL`](#Drule.SPEC_ALL), [`Drule.GEN_ALL`](#Drule.GEN_ALL),
[`Thm.UNDISCH`](#Thm.UNDISCH), [`Drule.DISCH`](#Drule.DISCH)
