## `free_varsl`

``` hol4
Term.free_varsl : term list -> term list
```

------------------------------------------------------------------------

Returns the set of free variables in a list of terms.

An invocation `free_varsl [t1,...,tn]` returns a list representing the
set of free term variables occurring in `t1,...,tn`.

### Failure

Never fails.

### Example

``` hol4
- free_varsl [Term `x /\ y /\ y ==> x`,
              Term `!x. x ==> p ==> y`];
> val it = [`x`, `y`, `p`] : term list
```

### Comments

Code should not depend on how elements are arranged in the result of
`free_varsl`.

`free_varsl` is not efficient for large terms with many free variables.
Demanding applications should be coded with `FVL`.

### See also

[`Term.FVL`](#Term.FVL), [`Term.free_vars_lr`](#Term.free_vars_lr),
[`Term.free_vars`](#Term.free_vars),
[`Term.empty_varset`](#Term.empty_varset),
[`Type.type_vars`](#Type.type_vars)
