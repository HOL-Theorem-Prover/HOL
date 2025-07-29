## `remove_ssfrags`

``` hol4
simpLib.remove_ssfrags : simpset -> string list -> simpset
```

------------------------------------------------------------------------

Removes named simpset fragments from a simpset.

A call to `remove_ssfrags simpset fragnames` returns a simpset that is
the same as `simpset` except that the simpset fragments with names in
the list `fragnames` are no longer included. As a special case, the
empty name `""` matches all unnamed fragments within `simpset` and
causes them to be removed.

### Failure

If no member of `fragnames` names a fragments in `simpset`, the
`Conv.UNCHANGED` exception is raised.

### Example

``` hol4
- SIMP_CONV (srw_ss()) [] ``MAP ($+ 1) [3;4;5]``;
<<HOL message: Initialising SRW simpset ... done>>
> val it = |- MAP ($+ 1) [3; 4; 5] = [4; 5; 6] : thm

- val myss = simpLib.remove_ssfrags (srw_ss()) ["REDUCE"]
> val myss = ...output elided...

- SIMP_CONV myss [] ``MAP ($+ 1) [3;4;5]``
> val it = |- MAP ($+ 1) [3; 4; 5] = [1 + 3; 1 + 4; 1 + 5] : thm
```

### See also

[`BasicProvers.diminish_srw_ss`](#BasicProvers.diminish_srw_ss)
