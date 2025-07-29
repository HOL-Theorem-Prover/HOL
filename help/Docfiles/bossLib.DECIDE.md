## `DECIDE`

``` hol4
bossLib.DECIDE : term -> thm
```

------------------------------------------------------------------------

Invoke decision procedure(s).

An application `DECIDE M`, where `M` is a boolean term, attempts to
prove `M` using a propositional tautology checker and a linear
arithmetic decision procedure.

### Failure

The invocation fails if `M` is not of boolean type. It also fails if `M`
is not a tautology or an instance of a theorem of linear arithmetic.

### Example

``` hol4
- DECIDE (Term `p /\ p /\ r ==> r`);
> val it = |- p /\ p /\ r ==> r : thm

- DECIDE (Term `x < 17 /\ y < 26 ==> x + y < 17 + 26`);
> val it = |- x < 17 /\ y < 26 ==> x + y < 17 + 26 : thm
```

### Comments

`DECIDE` is currently somewhat underpowered. Formerly it was implemented
by a cooperating decision procedure mechanism. However, most proofs
seemed to go somewhat smoother with simplification using the `arith_ss`
simpset, so we have adopted a simpler implementation. That should not be
taken as final, since cooperating decision procedures are an important
component in highly automated proof systems.

### See also

[`bossLib.RW_TAC`](#bossLib.RW_TAC),
[`bossLib.arith_ss`](#bossLib.arith_ss)
