## `sort_vars`

``` hol4
HolKernel.sort_vars : string list -> term list -> term list
```

------------------------------------------------------------------------

Sorts a list of variables according to first argument.

A call to `sort_vars [s1,s2,..sn] vs` will return a permutation of `vs`
such that variables with the name `s1` will appears first, followed by
those with the name `s2` etc.

### Failure

Never fails.

### Example

``` hol4
> sort_vars ["a", "b", "d"] [``b:bool``, ``c:num``, ``d:bool``, ``a:'a``];
val it = [``a``, ``b``, ``d``, ``c``] : term list
```

### See also

[`Conv.RESORT_EXISTS_CONV`](#Conv.RESORT_EXISTS_CONV),
[`Conv.RESORT_FORALL_CONV`](#Conv.RESORT_FORALL_CONV)
