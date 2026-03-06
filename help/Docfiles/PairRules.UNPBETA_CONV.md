## `UNPBETA_CONV`

``` hol4
PairRules.UNPBETA_CONV : (term -> conv)
```

------------------------------------------------------------------------

Creates an application of a paired abstraction from a term.

The user nominates some pair structure of variables `p` and a term `t`,
and `UNPBETA_CONV` turns `t` into an abstraction on `p` applied to `p`.

``` hol4
   ------------------  UNPBETA_CONV "p" "t"
    |- t = (\p. t) p
```

### Failure

Fails if `p` is not a paired structure of variables.

### See also

[`PairRules.PBETA_CONV`](#PairRules.PBETA_CONV),
[`PairedLambda.PAIRED_BETA_CONV`](#PairedLambda.PAIRED_BETA_CONV)
