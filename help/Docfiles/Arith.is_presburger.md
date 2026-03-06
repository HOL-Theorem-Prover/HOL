## `is_presburger`

``` hol4
Arith.is_presburger : (term -> bool)
```

------------------------------------------------------------------------

Determines whether a formula is in the Presburger subset of arithmetic.

This function returns true if the argument term is a formula in the
Presburger subset of natural number arithmetic. Presburger natural
arithmetic is the subset of arithmetic formulae made up from natural
number constants, numeric variables, addition, multiplication by a
constant, the natural number relations `<`, `<=`, `=`, `>=`, `>` and the
logical connectives `~`, `/\`, `\/`, `==>`, `=` (if-and-only-if), `!`
('forall') and `?` ('there exists').

Products of two expressions which both contain variables are not
included in the subset, but the function `SUC` which is not normally
included in a specification of Presburger arithmetic is allowed in this
HOL implementation. This function also considers subtraction and the
predecessor function, `PRE`, to be part of the subset.

### Failure

Never fails.

### Example

``` hol4
- is_presburger ``!m n p. m < (2 * n) /\ (n + n) <= p ==> m < SUC p``;
> val it = true : bool

- is_presburger ``!m n p q. m < (n * p) /\ (n * p) < q ==> m < q``;
> val it = false : bool

- is_presburger ``(m <= n) ==> !p. (m < SUC(n + p))``;
> val it = true : bool

- is_presburger ``(m + n) - m = n``;
> val it = true : bool
```

Useful for determining whether a decision procedure for Presburger
arithmetic is applicable to a term.

### See also

[`Arith.non_presburger_subterms`](#Arith.non_presburger_subterms),
[`Arith.FORALL_ARITH_CONV`](#Arith.FORALL_ARITH_CONV),
[`Arith.EXISTS_ARITH_CONV`](#Arith.EXISTS_ARITH_CONV),
[`Arith.is_prenex`](#Arith.is_prenex)
