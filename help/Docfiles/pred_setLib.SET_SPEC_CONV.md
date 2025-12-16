## `SET_SPEC_CONV`

``` hol4
pred_setLib.SET_SPEC_CONV : conv
```

------------------------------------------------------------------------

Axiom-scheme of specification for set abstractions.

The conversion `SET_SPEC_CONV` expects its term argument to be an
assertion of the form `t IN {E | P}`. Given such a term, the conversion
returns a theorem that defines the condition under which this membership
assertion holds. When `E` is just a variable `v`, the conversion
returns:

``` hol4
   |- t IN {v | P} = P[t/v]
```

and when `E` is not a variable but some other expression, the theorem
returned is:

``` hol4
   |- t IN {E | P} = ?x1...xn. (t = E) /\ P
```

where `x1`, ..., `xn` are the variables that occur free both in the
expression `E` and in the proposition `P`.

### Example

``` hol4
- SET_SPEC_CONV ``12 IN {n | n > N}``;
|- 12 IN {n | n > N} = 12 > N

- SET_SPEC_CONV ``p IN {(n,m) | n < m}``;
|- p IN {(n,m) | n < m} = (?n m. (p = n,m) /\ n < m)
```

### Failure

Fails if applied to a term that is not of the form `t IN {E | P}`.
