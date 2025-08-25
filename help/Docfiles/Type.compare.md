## `compare`

``` hol4
Type.compare : hol_type * hol_type -> order
```

------------------------------------------------------------------------

An ordering on HOL types.

An invocation `compare (ty1,ty2)` returns one of
`{LESS, EQUAL, GREATER}`. This is a total and transitive order.

### Failure

Never fails.

### Example

``` hol4
- Type.compare (bool, alpha --> alpha);
> val it = LESS : order
```

### Comments

One use of `compare` is to build efficient set or dictionary
datastructures involving HOL types in the keys.

There is also a `Term.compare`.

### See also

[`Term.compare`](#Term.compare)
