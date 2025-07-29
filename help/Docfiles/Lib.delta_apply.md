## `delta_apply`

``` hol4
Lib.delta_apply : ('a -> 'a delta) -> 'a -> 'a
```

------------------------------------------------------------------------

Apply a function to an argument, re-using the argument if possible.

An application `delta_apply f x` applies `f` to `x` and, if the result
is `SAME`, returns `x`. If the result is `DIFF y`, then `y` is returned.

### Failure

If `f x` raises exception `e`, then `delta_apply f x` raises `e`.

### Example

Suppose we want to write a function that replaces every even integer in
a list of pairs of integers with an odd one. The most basic replacement
function is therefore

``` hol4
   - fun ireplace i = if i mod 2 = 0 then DIFF (i+1) else SAME
```

Applying `ireplace` to an arbitrary integer would yield an element of
the `int delta` type. It's not seemingly useful, but it becomes useful
when used with similar functions for type operators. Then a delta
function for pairs of integers is built by
`delta_pair ireplace ireplace`, and a delta function for a list of pairs
of integers is built by applying `delta_map`.

``` hol4
   - delta_map (delta_pair ireplace ireplace)
               [(1,2), (3,5), (5,7), (4,8)];
   > val it = DIFF [(1,3), (3,5), (5,7), (5,9)] : (int * int) list delta

   - delta_map (delta_pair ireplace ireplace)
               [(1,3), (3,5), (5,7), (7,9)];
   > val it = SAME : (int * int) list delta
```

Finally, we can move the result from the `delta` type to the actual type
we are interested in.

``` hol4
   - delta_apply (delta_map (delta_pair ireplace ireplace))
               [(1,2), (3,5), (5,7), (4,8)];
   > val it = [(1,3), (3,5), (5,7), (5,9)] : (int * int) list
```

### Comments

Used to change a function from one that returns an `'a delta` element to
one that returns an `'a` element.

### See also

[`Lib.delta`](#Lib.delta), [`Lib.delta_map`](#Lib.delta_map),
[`Lib.delta_pair`](#Lib.delta_pair)
