## `free_vars`

``` hol4
Term.free_vars : term -> term list
```

------------------------------------------------------------------------

Returns the set of free variables in a term.

An invocation `free_vars tm` returns a list representing the set of term
variables occurring in `tm`.

### Failure

Never fails.

### Example

``` hol4
- free_vars (Term `x /\ y /\ y ==> x`);
> val it = [`y`, `x`] : term list
```

### Comments

Code should not depend on how elements are arranged in the result of
`free_vars`.

`free_vars` is not efficient for large terms with many free variables.
Demanding applications should be coded with `FVL`.

### See also

[`Term.FVL`](#Term.FVL), [`Term.free_vars_lr`](#Term.free_vars_lr),
[`Term.free_varsl`](#Term.free_varsl),
[`Term.empty_varset`](#Term.empty_varset),
[`Type.type_vars`](#Type.type_vars)
