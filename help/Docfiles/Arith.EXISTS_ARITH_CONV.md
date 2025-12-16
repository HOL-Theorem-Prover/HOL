## `EXISTS_ARITH_CONV`

``` hol4
Arith.EXISTS_ARITH_CONV : conv
```

------------------------------------------------------------------------

Partial decision procedure for non-universal Presburger natural
arithmetic.

`EXISTS_ARITH_CONV` is a partial decision procedure for formulae of
Presburger natural arithmetic which are in prenex normal form and have
all variables existentially quantified. Presburger natural arithmetic is
the subset of arithmetic formulae made up from natural number constants,
numeric variables, addition, multiplication by a constant, the relations
`<`, `<=`, `=`, `>=`, `>` and the logical connectives `~`, `/\`, `\/`,
`==>`, `=` (if-and-only-if), `!` ('forall') and `?` ('there exists').
Products of two expressions which both contain variables are not
included in the subset, but the function `SUC` which is not normally
included in a specification of Presburger arithmetic is allowed in this
HOL implementation.

Given a formula in the specified subset, the function attempts to prove
that it is equal to `T` (true). The procedure is incomplete; it is not
able to prove all formulae in the subset.

### Failure

The function can fail in two ways. It fails if the argument term is not
a formula in the specified subset, and it also fails if it is unable to
prove the formula. The failure strings are different in each case.

### Example

``` hol4
#EXISTS_ARITH_CONV "?m n. m < n";;
|- (?m n. m < n) = T

#EXISTS_ARITH_CONV "?m n. (2 * m) + (3 * n) = 10";;
|- (?m n. (2 * m) + (3 * n) = 10) = T
```

### See also

[`Arith.NEGATE_CONV`](#Arith.NEGATE_CONV),
[`Arith.FORALL_ARITH_CONV`](#Arith.FORALL_ARITH_CONV),
[`numLib.ARITH_CONV`](#numLib.ARITH_CONV)
