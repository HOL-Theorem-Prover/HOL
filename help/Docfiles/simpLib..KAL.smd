---
title: simpLib.++
---

## `++`

``` hol4
op simpLib.++ : simpset * ssfrag -> simpset
```

------------------------------------------------------------------------

Infix operator for adding an `ssfrag` item into a simpset.

`bossLib.++` is identical to `simpLib.++`.

If the incoming fragment has a name and that name is currently in the
simpset's *excluded* set (set up by an earlier `exclude_ssfrags` call —
e.g. via the `Proof[exclude_frags = ...]` attribute), the addition is a
silent no-op and `ss ++ frag` returns `ss` unchanged.  Use `force_add`
(or, in the rewrite-list of a simplification tactic, the `SF` marker) to
override that prohibition.

### See also

[`bossLib.++`](#bossLib..KAL),
[`simpLib.exclude_ssfrags`](#simpLib.exclude_ssfrags),
[`simpLib.force_add`](#simpLib.force_add)
