## `PEXT`

``` hol4
PairRules.PEXT : (thm -> thm)
```

------------------------------------------------------------------------

Derives equality of functions from extensional equivalence.

When applied to a theorem `A |- !p. t1 p = t2 p`, the inference rule
`PEXT` returns the theorem `A |- t1 = t2`.

``` hol4
    A |- !p. t1 p = t2 p
   ----------------------  PEXT          [where p is not free in t1 or t2]
        A |- t1 = t2
```

### Failure

Fails if the theorem does not have the form indicated above, or if any
of the component variables in the paired variable structure `p` is free
either of the functions `t1` or `t2`.

### Example

``` hol4
- PEXT (ASSUME (Term `!(x,y). ((f:('a#'a)->'a) (x,y)) = (g (x,y))`));
> val it =  [.] |- f = g : thm
```

### See also

[`Drule.EXT`](#Drule.EXT), [`Thm.AP_THM`](#Thm.AP_THM),
[`PairRules.PETA_CONV`](#PairRules.PETA_CONV),
[`Conv.FUN_EQ_CONV`](#Conv.FUN_EQ_CONV),
[`PairRules.P_FUN_EQ_CONV`](#PairRules.P_FUN_EQ_CONV)
