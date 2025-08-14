## `delta`

``` hol4
Lib.type 'a delta
```

------------------------------------------------------------------------

A type used for telling when a function has changed its argument.

The `delta` type is declared as follows:

``` hol4
   datatype 'a delta = SAME | DIFF of 'a
```

The `delta` type may be used in applications where it is important to
tell if a function has changed its argument or not. As an example of
this, consider mapping a function over a large collection of elements.
If only a few elements are changed, it makes sense to re-use all those
that were not changed. This can of course be handled on an ad hoc basis;
the `delta` type provides a mechanism for doing this systematically.

### Comments

The `delta` type is an example of polytypism.

### See also

[`Lib.delta_apply`](#Lib.delta_apply),
[`Lib.delta_map`](#Lib.delta_map), [`Lib.delta_pair`](#Lib.delta_pair)
