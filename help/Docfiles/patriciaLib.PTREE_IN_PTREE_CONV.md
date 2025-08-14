## `PTREE_IN_PTREE_CONV`

``` hol4
patriciaLib.PTREE_IN_PTREE_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$IN_PTREE`.

The conversion `PTREE_IN_PTREE_CONV` evaluates terms of the form
`n IN_PTREE t` where `t` is a well-formed unit Patricia tree
(constructed by `patricia$Empty`, `patricia$Leaf` and `patricia$Branch`)
and `n` is a natural number literal.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$IN_PTREE`.

### Example

``` hol4
- patriciaLib.PTREE_IN_PTREE_CONV ``1 IN_PTREE Empty``;
> val it = |- 1 IN_PTREE <{}> <=> F: thm

- patriciaLib.PTREE_IN_PTREE_CONV ``3 IN_PTREE (Branch 0 0 (Leaf 3 ()) (Leaf 2 ()))``;
> val it = |- 3 IN_PTREE Branch 0 0 (Leaf 3 ()) (Leaf 2 ()) <=> T: thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
