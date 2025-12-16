## `var_occurs`

``` hol4
Term.var_occurs : term -> term -> bool
```

------------------------------------------------------------------------

Check if a variable occurs in free in a term.

An invocation `var_occurs v M` returns `true` just in case `v` occurs
free in M.

### Failure

If the first argument is not a variable.

### Example

``` hol4
- var_occurs (Term`x:bool`) (Term `a /\ b ==> x`);
> val it = true : bool

- var_occurs (Term`x:bool`) (Term `!x. a /\ b ==> x`);
> val it = false : bool
```

### Comments

Identical to `free_in`, except for the requirement that the first
argument be a variable.

### See also

[`Term.free_vars`](#Term.free_vars), [`Term.free_in`](#Term.free_in)
