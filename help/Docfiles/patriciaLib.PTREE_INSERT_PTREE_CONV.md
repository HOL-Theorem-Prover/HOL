## `PTREE_INSERT_PTREE_CONV`

``` hol4
patriciaLib.PTREE_INSERT_PTREE_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$INSERT_PTREE`.

The conversion `PTREE_INSERT_PTREE_CONV` evaluates terms of the form
`m INSERT_PTREE_PTREE t` where `t` is a well-formed unit Patricia tree
(correctly constructed using `patricia$Empty`, `patricia$Leaf` and
`patricia$Branch`) and `m` is a natural number literal.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$INSERT_PTREE`.

### Example

``` hol4
- patriciaLib.PTREE_INSERT_PTREE_CONV ``2 INSERT_PTREE Empty``;
> val it = |- <{2}> = Leaf 2 (): thm

- DEPTH_CONV patriciaLib.PTREE_INSERT_PTREE_CONV ``3 INSERT_PTREE 2 INSERT_PTREE Empty``;
> val it = |- <{3; 2}> = Branch 0 0 (Leaf 3 ()) (Leaf 2 ()): thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
