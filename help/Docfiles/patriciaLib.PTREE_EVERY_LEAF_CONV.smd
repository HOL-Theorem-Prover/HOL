## `PTREE_EVERY_LEAF_CONV`

``` hol4
patriciaLib.PTREE_EVERY_LEAF_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `patricia$EVERY_LEAF`.

The conversion `PTREE_EVERY_LEAF_CONV` evaluates terms of the form
`EVERY_LEAF P t` where `t` is a well-formed Patricia tree (constructed
by `patricia$Empty`, `patricia$Leaf` and `patricia$Branch`) and `P` is
predicate.

### Failure

The conversion will fail if the supplied term is not a suitable
application of `patricia$EVERY_LEAF`.

### Example

``` hol4
- patriciaLib.PTREE_EVERY_LEAF_CONV ``EVERY_LEAF (=) Empty``;
> val it = |- EVERY_LEAF $= <{}> <=> T: thm

- patriciaLib.PTREE_EVERY_LEAF_CONV ``EVERY_LEAF (\x y. (x < 3) ==> (y = 1)) (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it =
   |- EVERY_LEAF (\x y. x < 3 ==> (y = 1))
        (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) <=> T:
   thm

- patriciaLib.PTREE_EVERY_LEAF_CONV ``EVERY_LEAF (\x y. x < 2) (Branch 0 0 (Leaf 3 2) (Leaf 2 1))``;
> val it =
   |- EVERY_LEAF (\x y. x < 2) (Branch 0 0 (Leaf 3 2) (Leaf 2 1)) <=> F:
   thm
```

### See also

[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
