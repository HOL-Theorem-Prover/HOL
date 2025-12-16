## `UNFOLD_CONV`

``` hol4
unwindLib.UNFOLD_CONV : (thm list -> conv)
```

------------------------------------------------------------------------

Expands sub-components of a hardware description using their
definitions.

`UNFOLD_CONV thl "t1 /\ ... /\ tn"` returns a theorem of the form:

``` hol4
   B |- t1 /\ ... /\ tn = t1' /\ ... /\ tn'
```

where each `ti'` is the result of rewriting `ti` with the theorems in
`thl`. The set of assumptions `B` is the union of the instantiated
assumptions of the theorems used for rewriting. If none of the rewrites
are applicable to a `ti`, it is unchanged.

### Failure

Never fails.

### Example

``` hol4
#UNFOLD_CONV [ASSUME "!in out. INV (in,out) = !(t:num). out t = ~(in t)"]
# "INV (l1,l2) /\ INV (l2,l3) /\ (!(t:num). l1 t = l2 (t-1) \/ l3 (t-1))";;
. |- INV(l1,l2) /\ INV(l2,l3) /\ (!t. l1 t = l2(t - 1) \/ l3(t - 1)) =
     (!t. l2 t = ~l1 t) /\
     (!t. l3 t = ~l2 t) /\
     (!t. l1 t = l2(t - 1) \/ l3(t - 1))
```

### See also

[`unwindLib.UNFOLD_RIGHT_RULE`](#unwindLib.UNFOLD_RIGHT_RULE)
