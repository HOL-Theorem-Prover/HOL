## `FORALL_CONJ_CONV`

``` hol4
unwindLib.FORALL_CONJ_CONV : conv
```

------------------------------------------------------------------------

Moves universal quantifiers down through a tree of conjunctions.

`FORALL_CONJ_CONV "!x1 ... xm. t1 /\ ... /\ tn"` returns the theorem:

``` hol4
   |- !x1 ... xm. t1 /\ ... /\ tn =
      (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)
```

where the original term can be an arbitrary tree of conjunctions. The
structure of the tree is retained in both sides of the equation.

### Failure

Never fails.

### Example

``` hol4
#FORALL_CONJ_CONV "!(x:*) (y:*) (z:*). (a /\ b) /\ c";;
|- (!x y z. (a /\ b) /\ c) = ((!x y z. a) /\ (!x y z. b)) /\ (!x y z. c)

#FORALL_CONJ_CONV "T";;
|- T = T

#FORALL_CONJ_CONV "!(x:*) (y:*) (z:*). T";;
|- (!x y z. T) = (!x y z. T)
```

### See also

[`unwindLib.CONJ_FORALL_CONV`](#unwindLib.CONJ_FORALL_CONV),
[`unwindLib.FORALL_CONJ_ONCE_CONV`](#unwindLib.FORALL_CONJ_ONCE_CONV),
[`unwindLib.CONJ_FORALL_ONCE_CONV`](#unwindLib.CONJ_FORALL_ONCE_CONV),
[`unwindLib.FORALL_CONJ_RIGHT_RULE`](#unwindLib.FORALL_CONJ_RIGHT_RULE),
[`unwindLib.CONJ_FORALL_RIGHT_RULE`](#unwindLib.CONJ_FORALL_RIGHT_RULE)
