## `remove_ssfrags`

``` hol4
simpLib.remove_ssfrags : string list -> simpset -> simpset
```

------------------------------------------------------------------------

Removes named simpset fragments from a simpset.

A call to `remove_ssfrags fragnames simpset` returns a simpset that is
the same as `simpset` except that the simpset fragments with names in
the list `fragnames` are no longer included. As a special case, the
empty name `""` matches all unnamed fragments within `simpset` and
causes them to be removed.

### Failure

If no member of `fragnames` names a fragment in `simpset`, the
`Conv.UNCHANGED` exception is raised.

### Example

``` hol4
> SIMP_CONV (srw_ss()) [] “MAP ($+ 1) [3;4;5]”;
<<HOL message: Initialising SRW simpset ... done>>
val it = ⊢ MAP ($+ 1) [3; 4; 5] = [4; 5; 6] : thm


> val myss = simpLib.remove_ssfrags ["REDUCE"] (srw_ss());
val myss = ... : simpset


> SIMP_CONV myss [] “MAP ($+ 1) [3;4;5]”;
val it = ⊢ MAP ($+ 1) [3; 4; 5] = [1 + 3; 1 + 4; 1 + 5] : thm
```

### Comparison with `exclude_ssfrags`

`remove_ssfrags` only strips matching fragments from the simpset's
history; a subsequent `ss ++ FRAG_ss` would re-add them.  By contrast,
`exclude_ssfrags` also records the exclusion in the simpset itself, so
that subsequent `++` of a fragment with one of the named names is a
silent no-op (until cleared via `force_add` / `SF`).  `exclude_ssfrags`
also never raises `Conv.UNCHANGED`.  The `Proof[exclude_frags = ...]`
attribute uses `exclude_ssfrags`.

### See also

[`simpLib.exclude_ssfrags`](#simpLib.exclude_ssfrags),
[`simpLib.force_add`](#simpLib.force_add),
[`BasicProvers.diminish_srw_ss`](#BasicProvers.diminish_srw_ss)
