## `PTREE_ADD_CONV`

``` hol4
patriciaLib.PTREE_ADD_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$ADD` and
`patricia$ADD_LIST`.

The conversion `PTREE_ADD_CONV` evaluates terms of the form `t |+ (m,n)`
or `t |++ l` where `t` is a well-formed Patricia tree (correctly
constructed using `patricia$Empty`, `patricia$Leaf` and
`patricia$Branch`) and `m` is a natural number literal.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$ADD` or `patricia$ADD_LIST`.

### Example

``` hol4
- patriciaLib.PTREE_ADD_CONV ``Empty |+ (3, x:num)``;
> val it = |- <{}> |+ (3,x) = Leaf 3 x: thm

- DEPTH_CONV patriciaLib.PTREE_ADD_CONV ``Empty |+ (3, 2) |+ (2,1)``;
> val it = |- <{}> |+ (3,2) |+ (2,1) = Branch 0 0 (Leaf 3 2) (Leaf 2 1): thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
