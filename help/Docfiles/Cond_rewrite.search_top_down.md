## `search_top_down`

``` hol4
Cond_rewrite.search_top_down
 : (term -> term -> ((term # term) list # (type # type) list) list)
```

------------------------------------------------------------------------

Search a term in a top-down fashion to find matches to another term.

`search_top_down tm1 tm2` returns a list of instantiations which make
the whole or part of `tm2` match `tm1`. The first term should not have a
quantifier at the outer most level. `search_top_down` first attempts to
match the whole second term to `tm1`. If this fails, it recursively
descend into the subterms of `tm2` to find all matches.

The length of the returned list indicates the number of matches found.
An empty list means no match can be found between `tm1` and `tm2` or any
subterms of `tm2`. The instantiations returned in the list are in the
same format as for the function `match`. Each instantiation is a pair of
lists: the first is a list of term pairs and the second is a list of
type pairs. Either of these lists may be empty. The situation in which
both lists are empty indicates that there is an exact match between the
two terms, i.e., no instantiation is required to make the entire `tm2`
or a part of `tm2` the same as `tm1`.

### Failure

Never fails.

### Example

``` hol4
   #search_top_down "x = y:*" "3 = 5";;
   [([("5", "y"); ("3", "x")], [(":num", ":*")])]
   : ((term # term) list # (type # type) list) list

   #search_top_down "x = y:*" "x =y:*";;
   [([], [])] : ((term # term) list # (type # type) list) list

   #search_top_down "x = y:*" "0 < p ==> (x <= p = y <= p)";;
   [([("y <= p", "y"); ("x <= p", "x")], [(":bool", ":*")])]
   : ((term # term) list # (type # type) list) list
```

The first example above shows the entire `tm2` matching `tm1`. The
second example shows the two terms match exactly. No instantiation is
required. The last example shows that a subterm of `tm2` can be
instantiated to match `tm1`.

### See also

[`Db.match`](#Db.match)
