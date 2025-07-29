## `completeInduct_on`

``` hol4
bossLib.completeInduct_on : term quotation -> tactic
```

------------------------------------------------------------------------

Perform complete induction.

If `q` parses into a well-typed term `M`, an invocation
`completeInduct_on q` begins a proof by complete (also known as
'course-of-values') induction on `M`. The term `M` should occur free in
the current goal.

### Failure

If `M` does not parse into a term or does not occur free in the current
goal.

### Example

Suppose we wish to prove that every number not equal to one has a prime
factor:

``` hol4
   !n. ~(n = 1) ==> ?p. prime p /\ p divides n
```

A natural way to prove this is by complete induction. Invoking
`` completeInduct_on `n` `` yields the goal

``` hol4
      { !m. m < n ==> ~(m = 1) ==> ?p. prime p /\ p divides m }
      ?-
      ~(n = 1) ==> ?p. prime p /\ p divides n
```

### See also

[`bossLib.measureInduct_on`](#bossLib.measureInduct_on),
[`bossLib.Induct`](#bossLib.Induct),
[`bossLib.Induct_on`](#bossLib.Induct_on)
