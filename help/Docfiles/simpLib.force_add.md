## `force_add`

``` hol4
simpLib.force_add : simpset -> ssfrag -> simpset
```

------------------------------------------------------------------------

Adds a simpset fragment, overriding any active exclusion of its name.

A call to `force_add simpset frag` returns a simpset that is `simpset`
augmented with `frag` (as if by `++`).  In addition, if `frag` has a name
that is currently in the simpset's *excluded* set (because of an earlier
`exclude_ssfrags` call), that name is removed from the excluded set so
that subsequent `++` of a fragment with the same name will also succeed.

This function is the override mechanism for `exclude_ssfrags`: while
`++` is silent when the incoming fragment is currently excluded,
`force_add` lifts the exclusion for that name and performs the addition.

`force_add` is what underlies the behaviour of the `SF` marker in
thm-list arguments to simplification tactics: writing `simp[SF FRAG_ss]`
inside a `Proof[exclude_frags = FRAG]` body re-enables `FRAG_ss` for
that simp call.

### Failure

Never fails.

### See also

[`simpLib.exclude_ssfrags`](#simpLib.exclude_ssfrags),
[`simpLib.++`](#simpLib..KAL),
[`bossLib.SF`](#bossLib.SF)
