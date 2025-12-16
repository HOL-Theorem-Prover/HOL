## `PATH_CONV`

``` hol4
Conv.PATH_CONV : string -> conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the subterm indicated by a path string.

A call to `PATH_CONV p c` returns a new conversion that applies `c` to
the subterm of a term identified by the path string `p`. This path
string is interpreted as a sequence of direction indications: `"a"`:
take the body of an abstraction; `"b"`: take the body of an abstraction
or binder (such as universal or existential quantification); `"l"`: take
the left (rator) path in an application; `"r"`: take the right (rand)
path in an application.

### Failure

The call to the path string and conversion fails if the provided string
includes characters other than `a`, `b`, `l` or `r`. When applied to a
term the resulting conversion will fail if the path is not meaningful or
if the conversion itself fails on the indicated subterm.

### Example

``` hol4
> PATH_CONV "lrr" numLib.REDUCE_CONV ``(1 + 2) + (3 + 4) + (5 + 6)``;
val it = |- 1 + 2 + (3 + 4) + (5 + 6) = 1 + 2 + 7 + (5 + 6) : thm

> PATH_CONV "br" numLib.REDUCE_CONV ``!x. x > 10 + 3``;
val it = |- (!x. x > 10 + 3) <=> !x. x > 13 : thm
```

### Comments

This function provides a more concise indication of sub-conversion
application than by composing `RATOR_CONV`, `RAND_CONV` and `ABS_CONV`.

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV),
[`Conv.BINDER_CONV`](#Conv.BINDER_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV)
