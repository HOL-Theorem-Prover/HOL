## `augment_srw_ss`

``` hol4
bossLib.augment_srw_ss : simpLib.ssfrag list -> unit
```

------------------------------------------------------------------------

Augments the "stateful rewriter" with a list of `simpset` fragments.

A call to `augment_srw_ss sslist` causes each element of `sslist` to be
merged into the `simpset` value that the system maintains "behind"
`srw_ss()`.

### Failure

Never fails.

### Comments

The change to the `srw_ss()` `simpset` brought about with
`augment_srw_ss` is not exported with a theory, so it is not
"permanent". But see `export_rewrites` for a simple way to achieve a
sort of permanence.

### See also

[`BasicProvers.export_rewrites`](#BasicProvers.export_rewrites),
[`bossLib.srw_ss`](#bossLib.srw_ss),
[`bossLib.SRW_TAC`](#bossLib.SRW_TAC)
