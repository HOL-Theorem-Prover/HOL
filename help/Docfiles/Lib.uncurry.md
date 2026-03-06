## `uncurry`

``` hol4
Lib.uncurry : ('a -> 'b -> 'c) -> ('a * 'b) -> 'c
```

------------------------------------------------------------------------

Converts a function taking two arguments into a function taking a single
paired argument.

The application `uncurry f` returns `fn (x,y) => f x y`, so that

``` hol4
   uncurry f (x,y) = f x y
```

### Failure

Never fails.

### Example

``` hol4
- fun add x y = x + y
> val add = fn : int -> int -> int

- uncurry add (3,4);
> val it = 7 : int
```

### See also

[`Lib`](#Lib), [`Lib.curry`](#Lib.curry)
