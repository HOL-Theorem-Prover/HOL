## `repeat`

``` hol4
Lib.repeat : ('a -> 'a) -> 'a -> 'a
```

------------------------------------------------------------------------

Iteratively apply a function until it fails.

An invocation `repeat f x` expands to `repeat f (f x)`. Thus it unrolls
to `f(...(f x)...)`, returning the most recent argument to `f` before
application fails.

### Failure

The evaluation of `repeat f x` fails only if interrupted, or machine
resources are exhausted.

### Example

The following gives a simple-minded way of calculating the largest
integer on the machine.

``` hol4
- fun incr x = x+1;
> val incr = fn : int -> int

val maxint = repeat incr 0;   (* takes some time *)
> val maxint = 1073741823 : int
```

(Caution: in some ML implementations, the type `int` is not implemented
by machine words, but by 'bignum' techniques that allow numbers of
arbitrary size, in which case the example above will not return for a
very long time.)

### See also

[`Lib.funpow`](#Lib.funpow)
