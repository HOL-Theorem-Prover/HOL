## `all_vars`

``` hol4
Term.all_vars : term -> term list
```

------------------------------------------------------------------------

Returns the set of all variables in a term.

An invocation `all_vars tm` returns a list representing the set of all
bound and free term variables occurring in `tm`.

### Failure

Never fails.

### Example

``` hol4
- all_vars ``!x y. x /\ y /\ y ==> z``;
> val it = [``z``, ``y``, ``x``] : term list
```

### Comments

Code should not depend on how elements are arranged in the result of
`all_vars`.

### See also

[`Term.all_atoms`](#Term.all_atoms),
[`Term.all_varsl`](#Term.all_varsl), [`Term.free_vars`](#Term.free_vars)
