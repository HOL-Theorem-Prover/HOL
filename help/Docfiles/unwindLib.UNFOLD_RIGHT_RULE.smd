## `UNFOLD_RIGHT_RULE`

``` hol4
unwindLib.UNFOLD_RIGHT_RULE : (thm list -> thm -> thm)
```

------------------------------------------------------------------------

Expands sub-components of a hardware description using their
definitions.

`UNFOLD_RIGHT_RULE thl` behaves as follows:

``` hol4
       A |- !z1 ... zr. t = ?y1 ... yp. t1 /\ ... /\ tn
   --------------------------------------------------------
    B u A |- !z1 ... zr. t = ?y1 ... yp. t1' /\ ... /\ tn'
```

where each `ti'` is the result of rewriting `ti` with the theorems in
`thl`. The set of assumptions `B` is the union of the instantiated
assumptions of the theorems used for rewriting. If none of the rewrites
are applicable to a `ti`, it is unchanged.

### Failure

Fails if the second argument is not of the required form, though either
or both of `r` and `p` may be zero.

### Example

``` hol4
#UNFOLD_RIGHT_RULE [ASSUME "!in out. INV(in,out) = !(t:num). out t = ~(in t)"]
# (ASSUME "!(in:num->bool) out. BUF(in,out) = ?l. INV(in,l) /\ INV(l,out)");;
.. |- !in out.
       BUF(in,out) = (?l. (!t. l t = ~in t) /\ (!t. out t = ~l t))
```

### See also

[`unwindLib.UNFOLD_CONV`](#unwindLib.UNFOLD_CONV)
