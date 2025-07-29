## `hash`

``` hol4
Lib.hash : int -> string -> int * int -> int
```

------------------------------------------------------------------------

Hash function for strings.

An invocation `hash i s (j,k)` takes an integer `i` and uses that to
construct a function that, given a string `s`, will produce values
approximately equally distributed among the numbers less than `i`. The
argument `j` gives an index in the string to start from. The `k`
argument is an accumulator, which is useful when hashing a collection of
strings.

### Failure

Never fails.

### Example

``` hol4
- hash 13 "ishkabibble" (0,0);
> val it = 5 : int
```

### Comments

For better results, the `i` parameter should be a prime.

This is probably not an industrial strength hash function.
