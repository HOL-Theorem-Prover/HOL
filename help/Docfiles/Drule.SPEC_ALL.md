## `SPEC_ALL`

``` hol4
Drule.SPEC_ALL : thm -> thm
```

------------------------------------------------------------------------

Specializes the conclusion of a theorem with its own quantified
variables.

When applied to a theorem `A |- !x1...xn. t`, the inference rule
`SPEC_ALL` returns the theorem `A |- t[x1'/x1]...[xn'/xn]` where the
`xi'` are distinct variants of the corresponding `xi`, chosen to avoid
clashes with any variables free in the assumption list and with the
names of constants. Normally `xi'` is just `xi`, in which case
`SPEC_ALL` simply removes all universal quantifiers.

``` hol4
       A |- !x1...xn. t
   ---------------------------  SPEC_ALL
    A |- t[x1'/x1]...[xn'/xn]
```

### Failure

Never fails.

### Example

``` hol4
- SPEC_ALL CONJ_ASSOC;
> val it = |- t1 /\ t2 /\ t3 = (t1 /\ t2) /\ t3 : thm
```

### See also

[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL),
[`Drule.GEN_ALL`](#Drule.GEN_ALL), [`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`Thm.SPEC`](#Thm.SPEC), [`Drule.SPECL`](#Drule.SPECL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC)
