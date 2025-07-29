## `funpow`

``` hol4
Lib.funpow : int -> ('a -> 'a) -> 'a -> 'a
```

------------------------------------------------------------------------

Iterates a function a fixed number of times.

`funpow n f x` applies `f` to `x`, `n` times, giving the result
`f (f ... (f x)...)` where the number of `f`'s is `n`. If `n` is not
positive, the result is `x`.

### Failure

`funpow n f x` fails if any of the `n` applications of `f` fail.

### Example

Apply `tl` three times to a list:

``` hol4
   - funpow 3 tl [1,2,3,4,5];
   > [4, 5] : int list
```

Apply `tl` zero times:

``` hol4
   - funpow 0 tl [1,2,3,4,5];
   > [1; 2; 3; 4; 5] : int list
```

Apply `tl` six times to a list of only five elements:

``` hol4
   - funpow 6 tl [1,2,3,4,5];
   ! Uncaught exception:
   ! List.Empty
```

### See also

[`Lib.repeat`](#Lib.repeat)
