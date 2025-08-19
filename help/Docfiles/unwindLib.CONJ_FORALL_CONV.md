## `CONJ_FORALL_CONV`

``` hol4
unwindLib.CONJ_FORALL_CONV : conv
```

------------------------------------------------------------------------

Moves universal quantifiers up through a tree of conjunctions.

`CONJ_FORALL_CONV "(!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn)"` returns
the following theorem:

``` hol4
   |- (!x1 ... xm. t1) /\ ... /\ (!x1 ... xm. tn) =
      !x1 ... xm. t1 /\ ... /\ tn
```

where the original term can be an arbitrary tree of conjunctions. The
structure of the tree is retained in both sides of the equation.

### Failure

Never fails.

### Example

``` hol4
#CONJ_FORALL_CONV "((!(x:*) (y:*) (z:*). a) /\ (!(x:*) (y:*) (z:*). b)) /\
#                  (!(x:*) (y:*) (z:*). c)";;
|- ((!x y z. a) /\ (!x y z. b)) /\ (!x y z. c) = (!x y z. (a /\ b) /\ c)

#CONJ_FORALL_CONV "T";;
|- T = T

#CONJ_FORALL_CONV "((!(x:*) (y:*) (z:*). a) /\ (!(x:*) (w:*) (z:*). b)) /\
#                  (!(x:*) (y:*) (z:*). c)";;
|- ((!x y z. a) /\ (!x w z. b)) /\ (!x y z. c) =
   (!x. ((!y z. a) /\ (!w z. b)) /\ (!y z. c))
```

### See also

[`unwindLib.FORALL_CONJ_CONV`](#unwindLib.FORALL_CONJ_CONV),
[`unwindLib.CONJ_FORALL_ONCE_CONV`](#unwindLib.CONJ_FORALL_ONCE_CONV),
[`unwindLib.FORALL_CONJ_ONCE_CONV`](#unwindLib.FORALL_CONJ_ONCE_CONV),
[`unwindLib.CONJ_FORALL_RIGHT_RULE`](#unwindLib.CONJ_FORALL_RIGHT_RULE),
[`unwindLib.FORALL_CONJ_RIGHT_RULE`](#unwindLib.FORALL_CONJ_RIGHT_RULE)
