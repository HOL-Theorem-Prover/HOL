## `PTREE_EXISTS_LEAF_CONV`

``` hol4
patriciaLib.PTREE_EXISTS_LEAF_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$EXISTS_LEAF`.

The conversion `PTREE_EXISTS_LEAF_CONV` evaluates terms of the form
`EXISTS_LEAF P t` where `t` is a well-formed Patricia tree (constructed
by `patricia$Empty`, `patricia$Leaf` and `patricia$Branch`) and `P` is
predicate.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$EXISTS_LEAF`.

### Example

``` hol4
- patriciaLib.PTREE_EXISTS_LEAF_CONV ``EXISTS_LEAF (=) Empty``;
> val it = |- EXISTS_LEAF $= <{}> <=> F: thm

- patriciaLib.PTREE_EXISTS_LEAF_CONV ``EXISTS_LEAF (\x y. y = 2) (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it =
   |- EXISTS_LEAF (\x y. y = 2) (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) <=> T:
   thm

- patriciaLib.PTREE_EXISTS_LEAF_CONV ``EXISTS_LEAF (\x y. y = 3) (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it =
   |- EXISTS_LEAF (\x y. y = 3) (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) <=> F:
   thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
