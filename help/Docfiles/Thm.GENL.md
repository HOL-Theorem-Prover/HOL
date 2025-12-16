## `GENL`

``` hol4
Thm.GENL : term list -> thm -> thm
```

------------------------------------------------------------------------

Generalizes zero or more variables in the conclusion of a theorem.

When applied to a term list `[x1,...,xn]` and a theorem `A |- t`, the
inference rule `GENL` returns the theorem `A |- !x1...xn. t`, provided
none of the variables `xi` are free in any of the assumptions. It is not
necessary that any or all of the `xi` should be free in `t`.

``` hol4
         A |- t
   ------------------  GENL [x1,...,xn]       [where no xi is free in A]
    A |- !x1...xn. t
```

### Failure

Fails unless all the terms in the list are variables, none of which are
free in the assumption list.

### See also

[`Thm.GEN`](#Thm.GEN), [`Drule.GEN_ALL`](#Drule.GEN_ALL),
[`Tactic.GEN_TAC`](#Tactic.GEN_TAC), [`Thm.SPEC`](#Thm.SPEC),
[`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC)
