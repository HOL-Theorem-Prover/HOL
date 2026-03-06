## `merge`

``` hol4
Tag.merge : tag -> tag -> tag
```

------------------------------------------------------------------------

Combine two tags into one.

When two theorems interact via inference, their tags are merged. This
propagates to the new theorem the fact that either or both were
constructed via shortcut.

### Failure

Never fails.

### Example

``` hol4
- Tag.merge (Tag.read "foo") (Tag.read "bar");
> val it = Kerneltypes.TAG(["bar", "foo"], []) : tag

- Tag.merge it (Tag.read "foo");
> val it = Kerneltypes.TAG(["bar", "foo"], []) : tag
```

### Comments

Although it is not harmful to use this entrypoint, there is little
reason to, since the merge operation is only used inside the HOL kernel.

### See also

[`Tag.read`](#Tag.read), [`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm),
[`Thm.tag`](#Thm.tag)
