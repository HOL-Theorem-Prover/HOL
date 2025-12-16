## `all_varsl`

``` hol4
Term.all_varsl : term list -> term list
```

------------------------------------------------------------------------

Returns the set of all variables in a list of terms.

An invocation `all_varsl [t1,...,tn]` returns a list representing the
set of all term variables occurring in `t1,...,tn`.

### Failure

Never fails.

### Example

``` hol4
- all_varsl [Term `x /\ y /\ y ==> x`,
             Term `!a. a ==> p ==> y`];
> val it = [`x`, `y`, `p`, `a`] : term list
```

### Comments

Code should not depend on how elements are arranged in the result of
`all_varsl`.

### See also

[`Term.all_atoms`](#Term.all_atoms), [`Term.all_vars`](#Term.all_vars),
[`Term.empty_varset`](#Term.empty_varset),
[`Term.free_vars_lr`](#Term.free_vars_lr),
[`Term.free_vars`](#Term.free_vars),
[`Term.free_varsl`](#Term.free_varsl), [`Term.FVL`](#Term.FVL),
[`Type.type_vars`](#Type.type_vars)
