## `PTREE_CONV`

``` hol4
patriciaLib.PTREE_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating Patricia tree operations.

The conversion `PTREE_CONV` evaluates Patricia tree operations such as
`ADD`, `ADD_LIST`, `REMOVE`, `SIZE`, `PEEK` and `FIND`. These
evaluations work for constants that are defined using `Define_mk_ptree`.
When adding to, or removing from, a Patricia tree a new contant will be
defined after `patriciaLib.ptree_new_defn_depth` operations. By default
`ptree_new_defn_depth` is `~1`, which means that new constants are never
defined.

### Example

Consider the following Patricia tree:

``` hol4
val ptree = Define_mk_ptree "ptree" (int_ptree_of_list [(1,``1``), (2, ``2``)]);
<<HOL message: Saved IS_PTREE theorem for new constant "ptree">>
val ptree = |- ptree = Branch 0 0 (Leaf 1 1) (Leaf 2 2): thm
```

Adding a list of updates expands into applications of `ADD`:

``` hol4
> real_time PTREE_CONV ``ptree |++ [(3,3); (4,4); (5,5); (6,6); (7,7)]``;
realtime: 0.000s
val it =
   |- ptree |++ [(3,3); (4,4); (5,5); (6,6); (7,7)] =
   ptree |+ (3,3) |+ (4,4) |+ (5,5) |+ (6,6) |+ (7,7):
   thm
```

However, setting `ptree_new_defn_depth` will cause new definitions to be
made:

``` hol4
> ptree_new_defn_depth := 2;
val it = (): unit
> real_time PTREE_CONV ``ptree |++ [(3,3); (4,4); (5,5); (6,6); (7,7)]``;
<<HOL message: Defined new ptree: ptree1>>
<<HOL message: Defined new ptree: ptree2>>
realtime: 0.006s
val it = |- ptree |++ [(3,3); (4,4); (5,5); (6,6); (7,7)] = ptree2 |+ (7,7):
   thm
```

New definitions will also be made when removing elements:

``` hol4
> real_time PTREE_CONV ``ptree2 \\ 6 \\ 5``;
<<HOL message: Defined new ptree: ptree3>>
realtime: 0.001s
val it = |- ptree2 \\ 6 \\ 5 = ptree3: thm
```

Here, the conversion is not smart enough to work out that `ptree3` is
the same as `ptree1`.

``` hol4
> (DEPTH_CONV PTREE_DEFN_CONV THENC EVAL) ``ptree1 = ptree3``;
val it = |- (ptree1 = ptree3) <=> T: thm
```

Look-up behaves as expected:

``` hol4
> real_time PTREE_CONV ``ptree1 ' 2``;
realtime: 0.001s
val it = |- ptree1 ' 2 = SOME 2: thm
> real_time PTREE_CONV ``ptree1 ' 5``;
realtime: 0.001s
val it = |- ptree1 ' 5 = NONE: thm
```

### Comments

The conversion `PTREE_CONV` is automatically added to the standard
`compset`. Thus, `EVAL` will have the same behaviour when `patriciaLib`
is loaded.

Run-times should be respectable when working with large Patricia trees.
However, this is predicated on the assumption that relatively small
numbers of updates are made following an initial application of
`Define_mk_ptree`. In this sense, the Patricia tree development is best
suited to situations where users require fast "read-only" look-up; where
the work of building the look-up tree can be performed outside of the
logic (i.e. in ML).

### See also

[`patriciaLib.Define_mk_ptree`](#patriciaLib.Define_mk_ptree),
[`patriciaLib.PTREE_DEFN_CONV`](#patriciaLib.PTREE_DEFN_CONV)
