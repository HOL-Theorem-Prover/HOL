## `match`

``` hol4
hol88Lib.match : term -> term -> (term * term) list * (hol_type * hol_type) list
```

------------------------------------------------------------------------

Finds instantiations to match one term to another.

When applied to two terms, `match_term` attempts to find a set of type
and term instantiations for the first term (only) to make it equal the
second. If it succeeds, it returns the instantiations in the form of a
pair containing a hol88 term substitution and a hol88 type substitution.
If the first term represents the conclusion of a theorem, the returned
instantiations are of the appropriate form to be passed to
`INST_TY_TERM`.

### Failure

Fails if the term cannot be matched by one-way instantiation.

### Comments

Note that `INST_TY_TERM` may still fail (when a variable that is
instantiated occurs free in the theorem's assumptions).

Superseded by `Term.match_term`.

### See also

[`Term.match_term`](#Term.match_term)
