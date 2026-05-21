## `tag`

``` hol4
Thm.tag : thm -> tag
```

------------------------------------------------------------------------

Extract the tag from a theorem.

An invocation `tag th`, where `th` has type `thm`, returns the tag of
the theorem. If derivation of the theorem has appealed at some point to
an oracle, the tag of that oracle will be embedded in the result.
Otherwise, an empty tag is returned.

### Failure

Never fails.

### Example

``` hol4
- Thm.tag (mk_thm([],F));
> val it = Kerneltypes.TAG(["MK_THM"], []) : tag

- Thm.tag NOT_FORALL_THM;
> val it = Kerneltypes.TAG([], []) : tag
```

### See also

[`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm), [`Tag.read`](#Tag.read),
[`Tag.merge`](#Tag.merge), [`Tag.pp_tag`](#Tag.pp_tag)
