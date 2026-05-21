## `curry`

``` hol4
Lib.curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
```

------------------------------------------------------------------------

Converts a function on a pair to a corresponding curried function.

The application `curry f` returns `fn x => fn y => f(x,y)`, so that

``` hol4
   curry f x y = f(x,y)
```

### Failure

A call `curry f` never fails; however, `curry f x y` fails if `f (x,y)`
fails.

### Example

``` hol4
- val increment = curry op+ 1;
> val it = increment = fn : int -> int

- increment 6;
> val it = 7 : int
```

### See also

[`Lib`](#Lib), [`Lib.uncurry`](#Lib.uncurry)
