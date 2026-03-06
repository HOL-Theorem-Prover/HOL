## `delta_pair`

``` hol4
Lib.delta_pair : ('a -> 'a delta) ->
             ('b -> 'b delta) ->
             'a * 'b -> ('a * 'b) delta
```

------------------------------------------------------------------------

Apply two functions to the projections of a pair, sharing as much
structure as possible.

An application `delta_pair f g (x,y)` applies `f` to `x` and `g` to `y`.
If `f x` equals `g y` equals `SAME`, then `SAME` is returned. Otherwise
`DIFF (p1,p2)` is returned, where `p1` is `x` if `f x` equals `SAME`;
otherwise `p1` is `f x`. Similarly, `p2` is `y` if `g y` equals `SAME`;
otherwise `p2` is `g y`.

### Failure

If `f x` raises `e`, then `delta_pair f g (x,y)` raises `e`.

If `g y` raises `e`, then `delta_pair f g (x,y)` raises `e`.

### Example

See the example in the documentation for `delta_apply`.

### See also

[`Lib.delta`](#Lib.delta), [`Lib.delta_apply`](#Lib.delta_apply),
[`Lib.delta_pair`](#Lib.delta_pair)
