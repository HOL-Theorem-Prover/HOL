## `CONJ_FORALL_RIGHT_RULE`

``` hol4
unwindLib.CONJ_FORALL_RIGHT_RULE : (thm -> thm)
```

------------------------------------------------------------------------

Moves universal quantifiers up through a tree of conjunctions.

``` hol4
    A |- !z1 ... zr.
          t = ?y1 ... yp. (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)
   -------------------------------------------------------------------
      A |- !z1 ... zr. t = ?y1 ... yp. !x1 ... xm. t1 /\ ... /\ tn
```

### Failure

Fails if the argument theorem is not of the required form, though either
or both of `r` and `p` may be zero.

### See also

[`unwindLib.FORALL_CONJ_RIGHT_RULE`](#unwindLib.FORALL_CONJ_RIGHT_RULE),
[`unwindLib.CONJ_FORALL_CONV`](#unwindLib.CONJ_FORALL_CONV),
[`unwindLib.FORALL_CONJ_CONV`](#unwindLib.FORALL_CONJ_CONV),
[`unwindLib.CONJ_FORALL_ONCE_CONV`](#unwindLib.CONJ_FORALL_ONCE_CONV),
[`unwindLib.FORALL_CONJ_ONCE_CONV`](#unwindLib.FORALL_CONJ_ONCE_CONV)
