## `decls`

``` hol4
Type.decls : string -> {Thy : string, Tyop : string} list
```

------------------------------------------------------------------------

Lists all theories a named type operator is declared in.

An invocation `Type.decls s` finds all theories in the ancestry of the
current theory with a type constant having the given name.

### Failure

Never fails.

### Example

``` hol4
- Type.decls "prod";
> val it = [{Thy = "pair", Tyop = "prod"}] : {Thy:string, Tyop:string} list
```

### Comments

There is also a function `Term.decls` that performs a similar operation
on term constants.

### See also

[`Theory.ancestry`](#Theory.ancestry), [`Term.decls`](#Term.decls),
[`Theory.constants`](#Theory.constants)
