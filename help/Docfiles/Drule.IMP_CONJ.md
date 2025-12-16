## `IMP_CONJ`

``` hol4
Drule.IMP_CONJ : (thm -> thm -> thm)
```

------------------------------------------------------------------------

Conjoins antecedents and consequents of two implications.

When applied to theorems `A1 |- p ==> r` and `A2 |- q ==> s`, the
`IMP_CONJ` inference rule returns the theorem
`A1 u A2 |- p /\ q ==> r /\ s`.

``` hol4
    A1 |- p ==> r    A2 |- q ==> s
   --------------------------------  IMP_CONJ
     A1 u A2 |- p /\ q ==> r /\ s
```

### Failure

Fails unless the conclusions of both theorems are implicative.

### See also

[`Thm.CONJ`](#Thm.CONJ)
