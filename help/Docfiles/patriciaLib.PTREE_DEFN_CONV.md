## `PTREE_DEFN_CONV`

``` hol4
patriciaLib.PTREE_DEFN_CONV : conv
```

------------------------------------------------------------------------

Conversion for evaluating applications of `ADD` and `REMOVE` to Patricia
tree constants.

Given a constant `c` defined using `Define_mk_ptree`, the conversion
`PTREE_DEFN_CONV` will evaluate term of the form `c |+ (k,x)`, `c \\ k`
and `c` where `k` is a natural number literal.

### Example

``` hol4
- val ptree = Define_mk_ptree "ptree" (int_ptree_of_list [(1,``1``), (2, ``2``)]);
<<HOL message: Saved IS_PTREE theorem for new constant "ptree">>
val ptree = |- ptree = Branch 0 0 (Leaf 1 1) (Leaf 2 2): thm

- PTREE_DEFN_CONV ``ptree \\ 1``;
val it = |- ptree \\ 1 = Leaf 2 2: thm

- PTREE_DEFN_CONV ``ptree |+ (3,3)``;
val it =
   |- ptree |+ (3,3) =
   Branch 0 0 (Branch 1 1 (Leaf 3 3) (Leaf 1 1)) (Leaf 2 2):
   thm
```

### Comments

The conversion `PTREE_DEFN_CONV` has limited uses and is mostly used
internally by the conversion `PTREE_CONV`.

### See also

[`patriciaLib.Define_mk_ptree`](#patriciaLib.Define_mk_ptree),
[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV)
