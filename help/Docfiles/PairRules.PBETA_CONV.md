## `PBETA_CONV`

``` hol4
PairRules.PBETA_CONV : conv
```

------------------------------------------------------------------------

Performs a general beta-conversion.

The conversion `PBETA_CONV` maps a paired beta-redex `"(\p.t)q"` to the
theorem

``` hol4
   |- (\p.t)q = t[q/p]
```

where `u[q/p]` denotes the result of substituting `q` for all free
occurrences of `p` in `t`, after renaming sufficient bound variables to
avoid variable capture. Unlike `PAIRED_BETA_CONV`, `PBETA_CONV` does not
require that the structure of the argument match the structure of the
pair bound by the abstraction. However, if the structure of the argument
does match the structure of the pair bound by the abstraction, then
`PAIRED_BETA_CONV` will do the job much faster.

### Failure

`PBETA_CONV tm` fails if `tm` is not a paired beta-redex.

### Example

`PBETA_CONV` will reduce applications with arbitrary structure.

``` hol4
   - PBETA_CONV
        (Term `((\((a:'a,b:'a),(c:'a,d:'a)). f a b c d) ((w,x),(y,z))):'a`);
   > val it = |- (\((a,b),c,d). f a b c d) ((w,x),y,z) = f w x y z : thm
```

`PBETA_CONV` does not require the structure of the argument and the
bound pair to match.

``` hol4
   - PBETA_CONV
       (Term `((\((a:'a,b:'a),(c:'a,d:'a)). f a b c d) ((w,x),yz)):'a`);
   > val it = |- (\((a,b),c,d). f a b c d) ((w,x),yz) =
                 f w x (FST yz) (SND yz) : thm
```

`PBETA_CONV` regards component pairs of the bound pair as variables in
their own right and preserves structure accordingly:

``` hol4
   - PBETA_CONV
       (Term `((\((a:'a,b:'a),(c:'a,d:'a)). f (a,b) (c,d)) (wx,(y,z))):'a`);
   > val it = |- (\((a,b),c,d). f (a,b) (c,d)) (wx,y,z) = f wx (y,z) : thm
```

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV),
[`PairedLambda.PAIRED_BETA_CONV`](#PairedLambda.PAIRED_BETA_CONV),
[`PairRules.PBETA_RULE`](#PairRules.PBETA_RULE),
[`PairRules.PBETA_TAC`](#PairRules.PBETA_TAC),
[`PairRules.LIST_PBETA_CONV`](#PairRules.LIST_PBETA_CONV),
[`PairRules.RIGHT_PBETA`](#PairRules.RIGHT_PBETA),
[`PairRules.RIGHT_LIST_PBETA`](#PairRules.RIGHT_LIST_PBETA),
[`PairRules.LEFT_PBETA`](#PairRules.LEFT_PBETA),
[`PairRules.LEFT_LIST_PBETA`](#PairRules.LEFT_LIST_PBETA)
