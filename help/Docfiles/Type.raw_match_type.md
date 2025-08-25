## `raw_match_type`

``` hol4
Type.raw_match_type
  : hol_type -> hol_type ->
    (hol_type,hol_type) subst * hol_type list ->
    (hol_type,hol_type) subst * hol_type list
```

------------------------------------------------------------------------

Primitive type matching algorithm.

An invocation `raw_match_type pat ty (S,Id)` performs matching, just as
`match_type`, except that it takes an extra accumulating parameter
`(S,Id)`, which represents a 'raw' substitution that the match
`(theta,id)` of `pat` and `ty` must be compatible with. If matching is
successful, `(theta,id)` is merged with `(S,Id)` to yield the result.

### Failure

A call to `raw_match_type pat ty (S,Id)` will fail when
`match_type pat ty` would. It will also fail when a `{redex,residue}`
calculated in the course of matching `pat` and `ty` is such that there
is a `{redex_i,residue_i}` in `S` and `redex` equals `redex_i` but
`residue` does not equal `residue_i`.

### Example

``` hol4
> val res1 = raw_match_type alpha “:'a -> bool” ([],[]);
val res1 = ([{redex = “:α”, residue = “:α -> bool”}], []) : ...

> raw_match_type “:'a -> 'b -> 'c”
                 “:('a -> bool) -> 'b -> ind” res1;
val it = ([{redex = “:γ”, residue = “:ind”},
           {redex = “:α”, residue = “:α -> bool”}], [“:β”]) : ....
```

### Comments

Probably exposes too much internal state of the matching algorithm.

### See also

[`Type.match_type`](#Type.match_type)
