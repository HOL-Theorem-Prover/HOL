## `PTREE_PEEK_CONV`

``` hol4
patriciaLib.PTREE_PEEK_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$PEEK`.

The conversion `PTREE_PEEK_CONV` evaluates terms of the form `t ' m`
where `t` is a well-formed Patricia tree (constructed by
`patricia$Empty`, `patricia$Leaf` and `patricia$Branch`) and `m` is a
natural number literal.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$PEEK`.

### Example

``` hol4
- patriciaLib.PTREE_PEEK_CONV ``Empty ' 3``;
> val it = |- <{}> ' 3 = NONE: thm

- patriciaLib.PTREE_PEEK_CONV ``Branch 0 0 (Leaf 3 2) (Leaf 2 1) ' 3``;
> val it = |- Branch 0 0 (Leaf 3 2) (Leaf 2 1) ' 3 = SOME 2: thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
