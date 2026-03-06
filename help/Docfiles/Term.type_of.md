## `type_of`

``` hol4
Term.type_of : term -> hol_type
```

------------------------------------------------------------------------

Returns the type of a term.

### Failure

Never fails.

### Example

``` hol4
- type_of boolSyntax.universal;
> val it = `:('a -> bool) -> bool` : hol_type
```
