## `PALPHA_CONV`

``` hol4
PairRules.PALPHA_CONV : term -> conv
```

------------------------------------------------------------------------

Renames the bound variables of a paired lambda-abstraction.

If `q` is a variable of type `ty` and `\p.t` is a paired abstraction in
which the bound pair `p` also has type `ty`, then `ALPHA_CONV q "\p.t"`
returns the theorem:

``` hol4
   |- (\p.t) = (\q'. t[q'/p])
```

where the pair `q':ty` is a primed variant of `q` chosen so that none of
its components are free in `\p.t`. The pairs `p` and `q` need not have
the same structure, but they must be of the same type.

### Example

`PALPHA_CONV` renames the variables in a bound pair:

``` hol4
   - PALPHA_CONV
       (Term `((w:'a,x:'a),(y:'a,z:'a))`)
       (Term `\((a:'a,b:'a),(c:'a,d:'a)). (f a b c d):'a`);
   > val it = |- (\((a,b),c,d). f a b c d) = (\((w,x),y,z). f w x y z) : thm
```

The new bound pair and the old bound pair need not have the same
structure.

``` hol4
   - PALPHA_CONV
       (Term `((wx:'a#'a),(y:'a,z:'a))`)
       (Term `\((a:'a,b:'a),(c:'a,d:'a)). (f a b c d):'a`);
   > val it = |- (\((a,b),c,d). f a b c d) =
                 (\(wx,y,z). f (FST wx) (SND wx) y z) : thm
```

`PALPHA_CONV` recognises subpairs of a pair as variables and preserves
structure accordingly.

``` hol4
   - PALPHA_CONV
      (Term `((wx:'a#'a),(y:'a,z:'a))`)
      (Term `\((a:'a,b:'a),(c:'a,d:'a)). (f (a,b) c d):'a`);
   > val it = |- (\((a,b),c,d). f (a,b) c d) = (\(wx,y,z). f wx y z) : thm
```

### Comments

`PALPHA_CONV` will only ever add the terms `FST` and `SND`, i.e., it
will never remove them. This means that while `\(x,y). x + y` can be
converted to `\xy. (FST xy) + (SND xy)`, it can not be converted back
again.

### Failure

`PALPHA_CONV q tm` fails if `q` is not a variable, if `tm` is not an
abstraction, or if `q` is a variable and `tm` is the lambda abstraction
`\p.t` but the types of `p` and `q` differ.

### See also

[`Drule.ALPHA_CONV`](#Drule.ALPHA_CONV),
[`PairRules.PALPHA`](#PairRules.PALPHA),
[`PairRules.GEN_PALPHA_CONV`](#PairRules.GEN_PALPHA_CONV)
