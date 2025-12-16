## `zDefine`

``` hol4
bossLib.zDefine : term quotation -> thm
```

------------------------------------------------------------------------

General-purpose function definition facility.

`zDefine` behaves exactly like `Define`, except that it does not add the
definition to `computeLib.the_compset`. Consequently the definition is
not used by `bossLib.EVAL` when evaluating expressions.

### Failure

`zDefine` and `Define` succeed and fail in the same way.

### Example

``` hol4
- zDefine `foo = 10 ** 10 ** 10`
- EVAL ``foo``;
> val it = |- foo = foo: thm
```

### Comments

`zDefine` is helpful when users wish to derive and use their own
efficient evaluation theorems, which can be added using
`computeLib.add_funs` or `computeLib.add_persistent_funs`.

### See also

[`bossLib.Define`](#bossLib.Define)
