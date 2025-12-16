## `op_arity`

``` hol4
Type.op_arity : {Thy:string, Tyop:string} -> int option
```

------------------------------------------------------------------------

Return the arity of a type operator.

An invocation `op_arity{Tyop,Thy}` returns `NONE` if the given record
does not identify a type operator in the current type signature.
Otherwise, it returns `SOME n`, where `n` identifies the number of
arguments the specified type operator takes.

### Failure

Never fails.

### Example

``` hol4
- op_arity{Tyop="fun", Thy="min"};
> val it = SOME 2 : int option

- op_arity{Tyop="foo", Thy="min"};
> val it = NONE : int option
```

### See also

[`Type.decls`](#Type.decls)
