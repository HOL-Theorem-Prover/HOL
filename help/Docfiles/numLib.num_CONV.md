## `num_CONV`

``` hol4
numLib.num_CONV : conv
```

------------------------------------------------------------------------

Equates a non-zero numeral with the form `SUC x` for some `x`.

### Example

``` hol4
- num_CONV ``1203``;
> val it = |- 1203 = SUC 1202 : thm
```

### Failure

Fails if the argument term is not a numeral of type ``` ``:num`` ```, or
if the argument is ``` ``0`` ```.

### See also

[`numLib.SUC_TO_NUMERAL_DEFN_CONV`](#numLib.SUC_TO_NUMERAL_DEFN_CONV)
