## `tag`

``` hol4
Tag.type tag
```

------------------------------------------------------------------------

Abstract type of oracle tags.

The type `tag` is used to track the use of oracles in HOL. An 'oracle'
is a source of theorems that are not proved, but just asserted. In HOL,
such unproven 'theorems' are used to incorporate the results of external
proof tools. Each theorem coming from an oracle has a tag attached to
it. This tag gets copied to any theorems hereditarily generated from an
oracular theorem by inference.

### See also

[`Tag.read`](#Tag.read), [`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm)
