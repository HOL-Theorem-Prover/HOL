## `PSPEC_ALL`

``` hol4
PairRules.PSPEC_ALL : (thm -> thm)
```

------------------------------------------------------------------------

Specializes the conclusion of a theorem with its own quantified pairs.

When applied to a theorem `A |- !p1...pn. t`, the inference rule
`PSPEC_ALL` returns the theorem `A |- t[p1'/p1]...[pn'/pn]` where the
`pi'` are distinct variants of the corresponding `pi`, chosen to avoid
clashes with any variables free in the assumption list and with the
names of constants. Normally `pi'` is just `pi`, in which case
`PSPEC_ALL` simply removes all universal quantifiers.

``` hol4
       A |- !p1...pn. t
   ---------------------------  PSPEC_ALL
    A |- t[p1'/x1]...[pn'/xn]
```

### Failure

Never fails.

### See also

[`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC)
