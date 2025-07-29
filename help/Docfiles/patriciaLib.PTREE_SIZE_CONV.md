## `PTREE_SIZE_CONV`

``` hol4
patriciaLib.PTREE_SIZE_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$SIZE`.

The conversion `PTREE_SIZE_CONV` evaluates terms of the form `SIZE t`
where `t` is a well-formed Patricia tree (constructed by
`patricia$Empty`, `patricia$Leaf` and `patricia$Branch`).

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$SIZE`.

### Example

``` hol4
- patriciaLib.PTREE_SIZE_CONV ``SIZE Empty``;
> val it = |- SIZE <{}> = 0: thm

- patriciaLib.PTREE_SIZE_CONV ``SIZE (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it = |- SIZE (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) = 2: thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
