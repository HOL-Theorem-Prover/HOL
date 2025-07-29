## `lhand`

``` hol4
boolSyntax.lhand : term -> term
```

------------------------------------------------------------------------

Returns the left-hand argument of a binary application.

A call to `lhand t` returns `x` in those situations where `t` is of the
form ``` ``f x y`` ```.

### Failure

Fails if the argument is not of the required form.

### Example

``` hol4
- lhand ``3 + 2``;
> val it = ``3`` : term
```

### Comments

The name `lhand` is an abbreviation of "left-hand", but `rand` is
so-named as an abbreviation of "operand". Nonetheless, `rand` does
return the right-hand argument of a binary application.

### See also

[`Term.rand`](#Term.rand), [`Term.rator`](#Term.rator)
