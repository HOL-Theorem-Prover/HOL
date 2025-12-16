## `PSPEC`

``` hol4
PairRules.PSPEC : (term -> thm -> thm)
```

------------------------------------------------------------------------

Specializes the conclusion of a theorem.

When applied to a term `q` and a theorem `A |- !p. t`, then `PSPEC`
returns the theorem `A |- t[q/p]`. If necessary, variables will be
renamed prior to the specialization to ensure that `q` is free for `p`
in `t`, that is, no variables free in `q` become bound after
substitution.

``` hol4
     A |- !p. t
   --------------  PSPEC "q"
    A |- t[q/p]
```

### Failure

Fails if the theorem's conclusion is not a paired universal
quantification, or if `p` and `q` have different types.

### Example

`PSPEC` specialised paired quantifications.

``` hol4
   - PSPEC (Term `(1,2)`) (ASSUME (Term`!(x,y). (x + y) = (y + x)`));
   > val it =  [.] |- 1 + 2 = 2 + 1 : thm
```

`PSPEC` treats paired structures of variables as variables and preserves
structure accordingly.

``` hol4
   - PSPEC (Term `x:'a#'a`) (ASSUME (Term `!(x:'a,y:'a). (x,y) = (x,y)`));
   > val it =  [.] |- x = x : thm
```

### See also

[`Thm.SPEC`](#Thm.SPEC), [`PairRules.IPSPEC`](#PairRules.IPSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL)
