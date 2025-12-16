## `PABS_CONV`

``` hol4
PairRules.PABS_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the body of a paired abstraction.

If `c` is a conversion that maps a term `t` to the theorem `|- t = t'`,
then the conversion `PABS_CONV c` maps abstractions of the form `\p.t`
to theorems of the form:

``` hol4
   |- (\p.t) = (\p.t')
```

That is, `ABS_CONV c "\p.t"` applies `p` to the body of the paired
abstraction `"\p.t"`.

### Failure

`PABS_CONV c tm` fails if `tm` is not a paired abstraction or if `tm`
has the form `"\p.t"` but the conversion `c` fails when applied to the
term `t`. The function returned by `ABS_CONV p` may also fail if the ML
function `c:term->thm` is not, in fact, a conversion (i.e. a function
that maps a term `t` to a theorem `|- t = t'`).

### Example

``` hol4
- PABS_CONV SYM_CONV (Term `\(x,y). (1,2) = (x,y)`);
> val it = |- (\(x,y). (1,2) = (x,y)) = (\(x,y). (x,y) = (1,2)) : thm
```

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV),
[`PairRules.PSUB_CONV`](#PairRules.PSUB_CONV)
