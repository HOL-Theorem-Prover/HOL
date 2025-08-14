## `diminish_srw_ss`

``` hol4
BasicProvers.diminish_srw_ss : string list -> ssfrag list
```

------------------------------------------------------------------------

Removes named simpset fragments from the stateful simpset.

A call to `diminish_srw_ss fragnames` removes the simpset fragments with
names given in `fragnames` from the stateful simpset which is returned
by `srw_ss()`, and which is used by `SRW_TAC`. This removal is done as a
side effect.

The function also returns the simpset fragments that have been removed.
This allows them to be put back into the simpset with a call to
`augment_srw_ss`.

The effect of this call is not exported to descendent theories.

### Failure

Fails with the `Conv.UNCHANGED` exception if the call would make no
change to the underlying simpset (i.e., if no name in `fragnames`
corresponds to a fragment in the stateful simpset. Apart from this, a
name can be provided for a fragment that does not appear in the stateful
simpset. In this case, the name is just ignored, and there will be no
corresponding fragment in the list that the function returns.

### Example

``` hol4
- SIMP_CONV (srw_ss()) [] ``MAP ($+ 1) [3;4;5]``;
> val it = |- MAP ($+ 1) [3; 4; 5] = [4; 5; 6] : thm

- val frags = diminish_srw_ss ["REDUCE"]
> val frags =
   [Simplification set: REDUCE
    Conversions:
      REDUCE_CONV (arithmetic reduction), keyed on pattern  ``EVEN x``
      REDUCE_CONV (arithmetic reduction), keyed on pattern  ``ODD x``
      REDUCE_CONV (arithmetic reduction), keyed on pattern  ``PRE x``
      REDUCE_CONV (arithmetic reduction), keyed on pattern  ``SUC x``
    ...] : ssfrag list

- SIMP_CONV (srw_ss()) [] ``MAP ($+ 1) [3;4;5]``;
> val it = |- MAP ($+ 1) [3; 4; 5] = [1 + 3; 1 + 4; 1 + 5] : thm

- augment_srw_ss frags;
> val it = () : unit

- SIMP_CONV (srw_ss()) [] ``MAP ($+ 1) [3;4;5]``;
> val it = |- MAP ($+ 1) [3; 4; 5] = [4; 5; 6] : thm
```

### See also

[`BasicProvers.augment_srw_ss`](#BasicProvers.augment_srw_ss),
[`simpLib.remove_ssfrags`](#simpLib.remove_ssfrags)
