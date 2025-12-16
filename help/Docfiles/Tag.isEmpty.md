## `isEmpty`

``` hol4
Tag.isEmpty : tag -> bool
```

------------------------------------------------------------------------

Tells if a tag is empty.

An invocation `isEmpty t` returns `true` just in case `t` is the empty
tag. Only theorems built solely by HOL proof have an empty tag.

### Failure

Never fails.

### Example

``` hol4
- Tag.isEmpty (Thm.tag NOT_FORALL_THM);
> val it = true : bool
```

### See also

[`Thm.tag`](#Thm.tag), [`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm)
