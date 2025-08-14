## `is_ptree`

``` hol4
patriciaLib.is_ptree : term -> bool
```

------------------------------------------------------------------------

Term recogniser for Patricia trees.

The destructor `is_ptree` will return true if, and only if, the supplied
term is a well-constructed, ground Patricia tree.

### Example

``` hol4
- is_ptree ``t:unit ptree``;
val it = false: bool

- is_ptree ``Branch 1 2 (Leaf 2 2) (Leaf 3 3)``;
val it = false: bool

- is_ptree ``Branch 0 0 (Leaf 1 1) (Leaf 2 2)``;
val it = true: bool
```

### See also

[`patriciaLib.mk_ptree`](#patriciaLib.mk_ptree),
[`patriciaLib.dest_ptree`](#patriciaLib.dest_ptree)
