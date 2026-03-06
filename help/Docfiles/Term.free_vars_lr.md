## `free_vars_lr`

``` hol4
Term.free_vars_lr : term -> term list
```

------------------------------------------------------------------------

Returns the set of free variables in a term, in order.

An invocation `free_vars_lr ty` returns a list representing the set of
type variables occurring in `ty`. The list will be in order of variable
occurrence when scanning the parse tree of the term from left to right.
This is usually, but need not be, the textual order when the term is
printed.

### Failure

Never fails.

### Example

``` hol4
- free_vars_lr (Term `x /\ y /\ y ==> z`);
> val it = [`x`, `y`, `z`] : term list
```

### Comments

`free_vars_lr` is not efficient for large terms with many free
variables. More strenuous applications should use high performance set
implementations available in the Standard ML Basis Library.

`free_vars_lr` can be used to build pleasing quantifier prefixes.

### See also

[`Term.FVL`](#Term.FVL), [`Term.free_vars`](#Term.free_vars),
[`Term.empty_varset`](#Term.empty_varset),
[`Type.type_vars`](#Type.type_vars)
