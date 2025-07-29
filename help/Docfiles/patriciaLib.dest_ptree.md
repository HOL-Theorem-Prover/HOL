## `dest_ptree`

``` hol4
patriciaLib.dest_ptree : term -> term_ptree
```

------------------------------------------------------------------------

Term destructor for Patricia trees.

The destructor `dest_ptree` will return a Patricia tree in ML that
corresponds with the supplied HOL term. The ML abstract data type
`term_ptree` is defined in `patriciaLib`.

### Failure

The conversion will fail if the supplied term is not well constructed
Patricia tree.

### Example

``` hol4
- dest_ptree ``(Branch 1 2 (Leaf 2 2) (Leaf 3 3))``;
Exception-
   HOL_ERR
  {message = "not a valid Patricia tree", origin_function = "dest_ptree",
  origin_structure = "patricia"} raised

- dest_ptree ``(Branch 0 0 (Leaf 3 3) (Leaf 2 2))``;
val it = <ptree>: term_ptree
```

### Comments

By default PolyML prints abstract data types in full. This can be turned
off with:

``` hol4
let
  fun pp _ _ (_: term_ptree) = PolyML.PrettyString "<ptree>"
in
  PolyML.addPrettyPrinter pp
end;
```

### See also

[`patriciaLib.mk_ptree`](#patriciaLib.mk_ptree),
[`patriciaLib.is_ptree`](#patriciaLib.is_ptree)
