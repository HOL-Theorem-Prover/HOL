## `PTREE_DEPTH_CONV`

``` hol4
patriciaLib.PTREE_DEPTH_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$DEPTH`.

The conversion `PTREE_DEPTH_CONV` evaluates terms of the form `DEPTH t`
where `t` is a well-formed Patricia tree (constructed by
`patricia$Empty`, `patricia$Leaf` and `patricia$Branch`).

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$DEPTH`.

### Example

``` hol4
- patriciaLib.PTREE_DEPTH_CONV ``DEPTH Empty``;
> val it = |- DEPTH <{}> = 0: thm

- patriciaLib.PTREE_DEPTH_CONV ``DEPTH (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it = |- DEPTH (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) = 2: thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
