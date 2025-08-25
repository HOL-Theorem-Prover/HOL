## `FORALL_ARITH_CONV`

``` hol4
Arith.FORALL_ARITH_CONV : conv
```

------------------------------------------------------------------------

Partial decision procedure for non-existential Presburger natural
arithmetic.

`FORALL_ARITH_CONV` is a partial decision procedure for formulae of
Presburger natural arithmetic which are in prenex normal form and have
all variables either free or universally quantified. Presburger natural
arithmetic is the subset of arithmetic formulae made up from natural
number constants, numeric variables, addition, multiplication by a
constant, the relations `<`, `<=`, `=`, `>=`, `>` and the logical
connectives `~`, `/\`, `\/`, `==>`, `=` (if-and-only-if), `!` ('forall')
and `?` ('there exists'). Products of two expressions which both contain
variables are not included in the subset, but the function `SUC` which
is not normally included in a specification of Presburger arithmetic is
allowed in this HOL implementation.

Given a formula in the specified subset, the function attempts to prove
that it is equal to `T` (true). The procedure only works if the formula
would also be true of the non-negative rationals; it cannot prove
formulae whose truth depends on the integral properties of the natural
numbers.

### Failure

The function can fail in two ways. It fails if the argument term is not
a formula in the specified subset, and it also fails if it is unable to
prove the formula. The failure strings are different in each case.

### Example

``` hol4
#FORALL_ARITH_CONV "m < SUC m";;
|- m < (SUC m) = T

#FORALL_ARITH_CONV "!m n p q. m <= p /\ n <= q ==> (m + n) <= (p + q)";;
|- (!m n p q. m <= p /\ n <= q ==> (m + n) <= (p + q)) = T

#FORALL_ARITH_CONV "!m n. ~(SUC (2 * m) = 2 * n)";;
evaluation failed     FORALL_ARITH_CONV -- cannot prove formula
```

### See also

[`Arith.NEGATE_CONV`](#Arith.NEGATE_CONV),
[`Arith.EXISTS_ARITH_CONV`](#Arith.EXISTS_ARITH_CONV),
[`numLib.ARITH_CONV`](#numLib.ARITH_CONV),
[`Arith.ARITH_FORM_NORM_CONV`](#Arith.ARITH_FORM_NORM_CONV),
[`Arith.DISJ_INEQS_FALSE_CONV`](#Arith.DISJ_INEQS_FALSE_CONV)
