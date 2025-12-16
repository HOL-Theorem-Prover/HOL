## `PTREE_IS_PTREE_CONV`

``` hol4
patriciaLib.PTREE_IS_PTREE_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$IS_PTREE`.

The conversion `PTREE_IS_PTREE_CONV` evaluates terms of the form
`IS_PTREE t` where `t` is any tree constructed by `patricia$Empty`,
`patricia$Leaf` and `patricia$Branch`. Well-formed trees correspond with
those that can be constructed by `patricia$ADD`.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$IS_PTREE`.

### Example

``` hol4
- patriciaLib.PTREE_IS_PTREE_CONV ``IS_PTREE Empty``;
> val it = |- IS_PTREE $= <{}> <=> T: thm

- patriciaLib.PTREE_IS_PTREE_CONV ``IS_PTREE (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it = |- IS_PTREE (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) <=> T: thm

- patriciaLib.PTREE_IS_PTREE_CONV ``IS_PTREE (Branch 0 0 (Leaf 3 2) (Leaf 1 1))``;
> val it = |- IS_PTREE (Branch 0 0 (Leaf 3 2) (Leaf 1 1)) <=> F: thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
