## `mk_ptree`

``` hol4
patriciaLib.mk_ptree : term_ptree -> term
```

------------------------------------------------------------------------

Term constructor for Patricia trees.

The constructor `mk_ptree` will return a HOL term that corresponds with
the supplied ML Patricia tree. The ML abstract data type `term_ptree` is
defined in `patriciaLib`.

### Failure

The conversion will fail if the terms stored in the supplied Patricia
tree do not all have the same type.

### Example

``` hol4
- mk_ptree (int_ptree_of_list [(1,``T``), (2, ``2``)]);
Exception-
   HOL_ERR
  {message = "", origin_function = "mk_branch", origin_structure =
  "HolKernel"} raised

- mk_ptree (int_ptree_of_list [(1,``1``), (2, ``2``)]);
val it = ``Branch 0 0 (Leaf 1 1) (Leaf 2 2)``: term
```

### Comments

When working with large trees it is a good idea constrain term printing
by setting Globals.max_print_depth.

### See also

[`patriciaLib.dest_ptree`](#patriciaLib.dest_ptree),
[`patriciaLib.is_ptree`](#patriciaLib.is_ptree)
