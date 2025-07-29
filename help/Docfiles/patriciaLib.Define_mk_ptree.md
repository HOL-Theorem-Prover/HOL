## `Define_mk_ptree`

``` hol4
patriciaLib.Define_mk_ptree : string -> term_ptree -> thm
```

------------------------------------------------------------------------

Define a new Patricia tree constant.

A call to `Define_mk_ptree c t` builds a HOL Patricia tree from the ML
tree `t` and uses this to define a new constant `c`. This provides and
efficient mechanism to define large patricia trees in HOL: the trees can
be quickly built in ML and then imported into HOL via
`patriciaLib.mk_ptree`. Provided the tree is not too large, a
side-effect of `Define_mk_ptree` is to prove the theorem
`|- IS_PTREE c`. This is controlled by the reference
`is_ptree_term_size_limit`.

To avoid producing large terms, a call to `EVAL` will not expand out the
definition of the new constant `c`. However, it will efficiently
evaluate operations performed on `c`, e.g. `PEEK c n` for ground `n`.

### Failure

`Define_mk_ptree` will fail when `patriciaLib.mk_ptree` fails.

### Example

The following session shows the construction of Patricia trees in ML,
which are then imported into HOL.

``` hol4
open patriciaLib;
...
> val ptree = Define_mk_ptree "ptree" (int_ptree_of_list [(1,``1``), (2, ``2``)]);
<<HOL message: Saved IS_PTREE theorem for new constant "ptree">>
val ptree = |- ptree = Branch 0 0 (Leaf 1 1) (Leaf 2 2): thm
> DB.theorem "ptree_is_ptree_thm";
val it = |- IS_PTREE ptree: thm

> val _ = Globals.max_print_depth := 7;
> let
    fun pp _ _ (_: term_ptree) = PolyML.PrettyString "<ptree>"
  in
    PolyML.addPrettyPrinter pp
  end;
val it = (): unit

> val random_ptree =
  real_time patriciaLib.ptree_of_ints
    (Random.rangelist (0,100000) (10000,Random.newgenseed 1.0));
realtime: 0.091s
val random_ptree = <ptree>: term_ptree

> val random = real_time (patriciaLib.Define_mk_ptree "random") random_ptree;
<<HOL warning: patriciaLib.Define_ptree: Failed to prove IS_PTREE (is_ptree_term_size_limit might be too small).>>
realtime: 0.196s
val random =
   |- random =
   Branch 0 0
     (... ... 1 (... ... (... ... ))
        (... ... (... ... ) (... ... (... ... ))))
     (Branch 0 1 (... ... (... ... ) (... ... (... ... )))
        (... ... 2 (... ... (... ... ))
           (... ... (... ... ) (... ... (... ... ))))):
   thm

> patriciaLib.size random_ptree;
val it = 9517: int
> real_time EVAL ``SIZE random``;
realtime: 3.531s
val it = |- SIZE random = 9517: thm

> int_peek random_ptree 3;
val it = SOME ``()``: term option
> real_time EVAL ``random ' 3``;
realtime: 0.004s
val it = |- random ' 3 = SOME (): thm

> int_peek random_ptree 100;
val it = NONE: term option
> real_time EVAL ``random ' 100``;
realtime: 0.004s
val it = |- random ' 100 = NONE: thm
```

### See also

[`patriciaLib.mk_ptree`](#patriciaLib.mk_ptree),
[`patriciaLib.PTREE_CONV`](#patriciaLib.PTREE_CONV),
[`patriciaLib.PTREE_DEFN_CONV`](#patriciaLib.PTREE_DEFN_CONV)
