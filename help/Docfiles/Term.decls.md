## `decls`

``` hol4
Term.decls : string -> term list
```

------------------------------------------------------------------------

Returns a list of constants having the same name.

An invocation `Term.decls s` returns a list of constants found in the
current theory having the name `s`. If there are no constants with name
`s`, then the empty list is returned.

### Failure

Never fails.

### Example

``` hol4
- decls "+";
> val it = [`$+`] : term list

- map dest_thy_const it;
> val it = [{Name = "+", Thy = "arithmetic", Ty = `:num -> num -> num`}] : ...
```

### Comments

Useful for untangling confusion arising from overloading and also the
possibility to declare two different constants with the same name in
different theories.

### See also

[`Type.decls`](#Type.decls),
[`Term.dest_thy_const`](#Term.dest_thy_const)
