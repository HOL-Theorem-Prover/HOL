## `delta_map`

``` hol4
Lib.delta_map : ('a -> 'a delta) -> 'a list -> 'a list delta
```

------------------------------------------------------------------------

Apply a function to a list, sharing as much structure as possible.

An application `delta_map f list` applies `f` to each member
`[x1,...,xn]` of `list`. If all applications of `f` return `SAME`, then
`delta_map f list` returns `SAME`. Otherwise, `DIFF [y1,...,yn]` is
returned. If `f xi` yielded `SAME`, then `yi` is `xi`. Otherwise, `f xi`
equals `DIFF yi`.

### Failure

If some application of `f xi` raises `e`, then `delta_map f list` raises
`e`.

### Example

See the example in the documentation for `delta_apply`.

### See also

[`Lib.delta`](#Lib.delta), [`Lib.delta_apply`](#Lib.delta_apply),
[`Lib.delta_pair`](#Lib.delta_pair)
