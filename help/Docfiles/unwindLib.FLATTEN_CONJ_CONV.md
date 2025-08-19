## `FLATTEN_CONJ_CONV`

``` hol4
unwindLib.FLATTEN_CONJ_CONV : conv
```

------------------------------------------------------------------------

Flattens a 'tree' of conjunctions.

`FLATTEN_CONJ_CONV "t1 /\ ... /\ tn"` returns a theorem of the form:

``` hol4
   |- t1 /\ ... /\ tn = u1 /\ ... /\ un
```

where the right-hand side of the equation is a flattened version of the
left-hand side.

### Failure

Never fails.

### Example

``` hol4
#FLATTEN_CONJ_CONV "(a /\ (b /\ c)) /\ ((d /\ e) /\ f)";;
|- (a /\ b /\ c) /\ (d /\ e) /\ f = a /\ b /\ c /\ d /\ e /\ f
```
