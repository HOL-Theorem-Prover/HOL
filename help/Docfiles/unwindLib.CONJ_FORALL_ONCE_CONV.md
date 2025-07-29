## `CONJ_FORALL_ONCE_CONV`

``` hol4
unwindLib.CONJ_FORALL_ONCE_CONV : conv
```

------------------------------------------------------------------------

Moves a single universal quantifier up through a tree of conjunctions.

`CONJ_FORALL_ONCE_CONV "(!x. t1) /\ ... /\ (!x. tn)"` returns the
theorem:

``` hol4
   |- (!x. t1) /\ ... /\ (!x. tn) = !x. t1 /\ ... /\ tn
```

where the original term can be an arbitrary tree of conjunctions. The
structure of the tree is retained in both sides of the equation.

### Failure

Fails if the argument term is not of the required form. The term need
not be a conjunction, but if it is every conjunct must be universally
quantified with the same variable.

### Example

``` hol4
#CONJ_FORALL_ONCE_CONV "((!x. x \/ a) /\ (!x. x \/ b)) /\ (!x. x \/ c)";;
|- ((!x. x \/ a) /\ (!x. x \/ b)) /\ (!x. x \/ c) =
   (!x. ((x \/ a) /\ (x \/ b)) /\ (x \/ c))

#CONJ_FORALL_ONCE_CONV "!x. x \/ a";;
|- (!x. x \/ a) = (!x. x \/ a)

#CONJ_FORALL_ONCE_CONV "((!x. x \/ a) /\ (!y. y \/ b)) /\ (!x. x \/ c)";;
evaluation failed     CONJ_FORALL_ONCE_CONV
```

### See also

[`unwindLib.FORALL_CONJ_ONCE_CONV`](#unwindLib.FORALL_CONJ_ONCE_CONV),
[`unwindLib.CONJ_FORALL_CONV`](#unwindLib.CONJ_FORALL_CONV),
[`unwindLib.FORALL_CONJ_CONV`](#unwindLib.FORALL_CONJ_CONV),
[`unwindLib.CONJ_FORALL_RIGHT_RULE`](#unwindLib.CONJ_FORALL_RIGHT_RULE),
[`unwindLib.FORALL_CONJ_RIGHT_RULE`](#unwindLib.FORALL_CONJ_RIGHT_RULE)
