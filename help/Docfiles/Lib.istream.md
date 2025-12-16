## `istream`

``` hol4
Lib.type ('a,'b) istream
```

------------------------------------------------------------------------

Type of imperative streams.

The type `('a,'b) istream` is an abstract type of imperative streams.
These may be created with `mk_istream`, advanced by `next`, accessed by
`state`, and reset with `reset`.

### Comments

Purely functional streams are well-known in functional programming, and
more elegant. However, this type proved useful in implementing some
imperative 'gensym'-like algorithms used in HOL.

### See also

[`Lib.mk_istream`](#Lib.mk_istream), [`Lib.next`](#Lib.next),
[`Lib.state`](#Lib.state), [`Lib.reset`](#Lib.reset)
