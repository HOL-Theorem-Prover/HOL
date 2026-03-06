## `PTREE_REMOVE_CONV`

``` hol4
patriciaLib.PTREE_REMOVE_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$REMOVE`.

The conversion `PTREE_REMOVE_CONV` evaluates terms of the form `t \\ m`
where `t` is a well-formed Patricia tree (constructed by
`patricia$Empty`, `patricia$Leaf` and `patricia$Branch`) and `m` is a
natural number literal.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$REMOVE`.

### Example

``` hol4
- patriciaLib.PTREE_REMOVE_CONV ``Empty \\ 3``;
> val it = |- <{}> \\ 3 = <{}>: thm

- patriciaLib.PTREE_REMOVE_CONV ``Branch 0 0 (Leaf 3 2) (Leaf 2 1) \\ 3``;
> val it = |- Branch 0 0 (Leaf 3 2) (Leaf 2 1) \\ 3 = Leaf 2 1: thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
