## `measureInduct_on`

``` hol4
bossLib.measureInduct_on : term quotation -> tactic
```

------------------------------------------------------------------------

Perform complete induction with a supplied measure function.

If `q` parses into a well-typed term `M N`, an invocation
`measureInduct_on q` begins a proof by induction, using `M` to map `N`
into a number. The term `N` should occur free in the current goal.

### Failure

If `M N` does not parse into a term or if `N` does not occur free in the
current goal.

### Example

Suppose we wish to prove `P (APPEND l1 l2)` by induction on the length
of `l1`. Then `` measureInduct_on `LENGTH ll` `` yields the goal

``` hol4
   { !y. LENGTH y < LENGTH l1 ==> P (APPEND y l2) } ?- P (APPEND l1 l2)
```

### See also

[`bossLib.completeInduct_on`](#bossLib.completeInduct_on),
[`bossLib.Induct`](#bossLib.Induct),
[`bossLib.Induct_on`](#bossLib.Induct_on)
