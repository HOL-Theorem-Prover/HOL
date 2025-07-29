## `is_prenex`

``` hol4
Arith.is_prenex : (term -> bool)
```

------------------------------------------------------------------------

Determines whether a formula is in prenex normal form.

This function returns true if the term it is given as argument is in
prenex normal form. If the term is not a formula the result will be true
provided there are no nested Boolean expressions involving quantifiers.

### Failure

Never fails.

### Example

``` hol4
- is_prenex ``!x. ?y. x \/ y``;
> val it = true : bool

- is_prenex ``!x. x ==> (?y. x /\ y)``;
> val it = false : bool
```

Useful for determining whether it is necessary to apply a prenex
normaliser to a formula before passing it to a function which requires
the formula to be in prenex normal form.

### See also

[`Arith.PRENEX_CONV`](#Arith.PRENEX_CONV)
