## `PTREE_TRANSFORM_CONV`

``` hol4
patriciaLib.PTREE_TRANSFORM_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$TRANSFORM`.

The conversion `PTREE_TRANSFORM_CONV` evaluates terms of the form
`TRANSFORM f t` where `t` is a well-formed Patricia tree (constructed by
`patricia$Empty`, `patricia$Leaf` and `patricia$Branch`) and `f` is map.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$TRANSFORM`.

### Example

``` hol4
- patriciaLib.PTREE_TRANSFORM_CONV ``TRANSFORM ODD Empty``;
> val it = |- TRANSFORM ODD <{}> = <{}>: thm

- patriciaLib.PTREE_TRANSFORM_CONV ``TRANSFORM ODD (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it =
   |- TRANSFORM ODD (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) =
      Branch 0 0 (Leaf 3 F) (Leaf 2 T):
   thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
