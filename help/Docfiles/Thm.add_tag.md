## `add_tag`

``` hol4
Thm.add_tag : tag * thm -> thm
```

------------------------------------------------------------------------

Adds oracle tags to a theorem.

A call to `add_tag(tg,th)` returns a `th'` such that calling
`Thm.tag(th')` returns the tag that is the merge of the tag associated
with `th` (if any) and `tg`.

### Failure

Never fails.

### Comments

If an oracle implementation wishes to record additional information
about the oracle mechanisms that have contributed to the 'proof' of a
theorem (perhaps the use of existing HOL theorems that will have their
own tags), then this function can be used to add that record.

### See also

[`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm)
