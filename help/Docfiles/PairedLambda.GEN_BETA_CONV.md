## `GEN_BETA_CONV`

``` hol4
PairedLambda.GEN_BETA_CONV : conv
```

------------------------------------------------------------------------

Beta-reduces single or paired beta-redexes, creating a paired argument
if needed.

The conversion `GEN_BETA_CONV` will perform beta-reduction of simple
beta-redexes in the manner of `BETA_CONV`, or of tupled beta-redexes in
the manner of `PAIRED_BETA_CONV`. Unlike the latter, it will force
through a beta-reduction by introducing arbitrarily nested pair
destructors if necessary. The following shows the action for one level
of pairing; others are similar.

``` hol4
   GEN_BETA_CONV "(\(x,y). t) p" = t[(FST p)/x, (SND p)/y]
```

### Failure

`GEN_BETA_CONV tm` fails if `tm` is neither a simple nor a tupled
beta-redex.

### Example

The following examples show the action of `GEN_BETA_CONV` on tupled
redexes. In the following, it acts in the same way as
`PAIRED_BETA_CONV`:

``` hol4
   - pairLib.GEN_BETA_CONV (Term `(\(x,y). x + y) (1,2)`);
   val it = |- (\(x,y). x + y)(1,2) = 1 + 2 : thm
```

whereas in the following, the operand of the beta-redex is not a pair,
so `FST` and `SND` are introduced:

``` hol4
   - pairLib.GEN_BETA_CONV (Term `(\(x,y). x + y) numpair`);
   > val it = |- (\(x,y). x + y) numpair = FST numpair + SND numpair : thm
```

The introduction of `FST` and `SND` will be done more than once as
necessary:

``` hol4
   - pairLib.GEN_BETA_CONV (Term `(\(w,x,y,z). w + x + y + z) (1,triple)`);
   > val it =
       |- (\(w,x,y,z). w + x + y + z) (1,triple) =
          1 + FST triple + FST (SND triple) + SND (SND triple) : thm
```

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV),
[`PairedLambda.PAIRED_BETA_CONV`](#PairedLambda.PAIRED_BETA_CONV)
