## `SPLICE_CONJ_CONV`

``` hol4
Conv.SPLICE_CONJ_CONV : conv
```

------------------------------------------------------------------------

Partially normalize a conjunction.

Normalize to right associativity a conjunction without recursing in the
right conjunct.

### Failure

Fails if the user-provided term is not a conjunction.

### Example

``` hol4
> SPLICE_CONJ_CONV ``(a1 /\ a2 /\ a3) /\ b /\ c``;
val it = |- (a1 /\ a2 /\ a3) /\ b /\ c <=> a1 /\ a2 /\ a3 /\ b /\ c: thm

> SPLICE_CONJ_CONV ``(a1 /\ a2) /\ (b1 /\ b2) /\ c``;
val it = |- (a1 /\ a2) /\ (b1 /\ b2) /\ c <=> a1 /\ a2 /\ (b1 /\ b2) /\ c: thm
```
