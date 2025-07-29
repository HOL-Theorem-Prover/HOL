## `compare`

``` hol4
Term.compare : term * term -> order
```

------------------------------------------------------------------------

Ordering on terms.

An invocation `compare (M,N)` will return one of
`{LESS, EQUAL, GREATER}`, according to an ordering on terms. The
ordering is transitive and total, and equates alpha-convertible terms.

### Failure

Never fails.

### Example

``` hol4
- compare (T,F);
> val it = GREATER : order

- compare (Term `\x y. x /\ y`, Term `\y z. y /\ z`);
> val it = EQUAL : order
```

### Comments

Used to build high performance datastructures for dealing with sets
having many terms.

### See also

[`Term.empty_tmset`](#Term.empty_tmset),
[`Term.var_compare`](#Term.var_compare)
