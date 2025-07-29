## `ARITH_CONV`

``` hol4
numLib.ARITH_CONV : conv
```

------------------------------------------------------------------------

Partial decision procedure for a subset of linear natural number
arithmetic.

`ARITH_CONV` is a partial decision procedure for Presburger natural
arithmetic. Presburger natural arithmetic is the subset of arithmetic
formulae made up from natural number constants, numeric variables,
addition, multiplication by a constant, the relations `<`, `<=`, `=`,
`>=`, `>` and the logical connectives `~`, `/\`, `\/`, `==>`, `=`
(if-and-only-if), `!` ('forall') and `?` ('there exists'). Products of
two expressions which both contain variables are not included in the
subset, but the functions `SUC` and `PRE` which are not normally
included in a specification of Presburger arithmetic are allowed in this
HOL implementation.

`ARITH_CONV` further restricts the subset as follows: when the formula
has been put in prenex normal form it must contain only one kind of
quantifier, that is the quantifiers must either all be universal
('forall') or all existential. Variables may appear free (unquantified)
provided any quantifiers that do appear in the prenex normal form are
universal; free variables are taken as being implicitly universally
quantified so mixing them with existential quantifiers would violate the
above restriction.

Given a formula in the permitted subset, `ARITH_CONV` attempts to prove
that it is equal to `T` (true). For universally quantified formulae the
procedure only works if the formula would also be true of the
non-negative rationals; it cannot prove formulae whose truth depends on
the integral properties of the natural numbers. The procedure is also
incomplete for existentially quantified formulae, but in this case there
is no rule-of-thumb for determining whether the procedure will work.

The function features a number of preprocessors which extend the
coverage beyond the subset specified above. In particular, natural
number subtraction and conditional statements are allowed. Another
permits substitution instances of universally quantified formulae to be
accepted. Note that Boolean-valued variables are not allowed.

### Failure

The function can fail in two ways. It fails if the argument term is not
a formula in the specified subset, and it also fails if it is unable to
prove the formula. The failure strings are different in each case.
However, the function may announce that it is unable to prove a formula
that one would expect it to reject as being outside the subset. This is
due to it looking for substitution instances; it has generalised the
formula so that the new formula is in the subset but is not valid.

### Example

A simple example containing a free variable:

``` hol4
   - ARITH_CONV ``m < SUC m``;
   > val it = |- m < (SUC m) = T : thm
```

A more complex example with subtraction and universal quantifiers, and
which is not initially in prenex normal form:

``` hol4
   - ARITH_CONV
     ``!m p. p < m ==> !q r. (m < (p + q) + r) ==> ((m - p) < q + r)``;
   > val it = |- (!m p. p < m ==> (!q r. m < ((p + q) + r) ==> (m - p) < (q + r))) = T
```

Two examples with existential quantifiers:

``` hol4
   - ARITH_CONV ``?m n. m < n``;
   > val it = |- (?m n. m < n) = T

   - ARITH_CONV ``?m n. (2 * m) + (3 * n) = 10``;
   > val it = |- (?m n. (2 * m) + (3 * n) = 10) = T
```

An instance of a universally quantified formula involving a conditional
statement and subtraction:

``` hol4
   - ARITH_CONV
     ``((p + 3) <= n) ==> (!m. ((m EXP 2 = 0) => (n - 1) | (n - 2)) > p)``;
   > val it = |- (p + 3) <= n ==> (!m. ((m EXP 2 = 0) => n - 1 | n - 2) > p) = T
```

Failure due to mixing quantifiers:

``` hol4
   - ARITH_CONV ``!m. ?n. m < n``;
   evaluation failed     ARITH_CONV -- formula not in the allowed subset
```

Failure because the truth of the formula relies on the fact that the
variables cannot have fractional values:

``` hol4
   - ARITH_CONV ``!m n. ~(SUC (2 * m) = 2 * n)``;
   evaluation failed     ARITH_CONV -- cannot prove formula
```

### See also

[`Arith.NEGATE_CONV`](#Arith.NEGATE_CONV),
[`Arith.EXISTS_ARITH_CONV`](#Arith.EXISTS_ARITH_CONV),
[`Arith.FORALL_ARITH_CONV`](#Arith.FORALL_ARITH_CONV),
[`Arith.INSTANCE_T_CONV`](#Arith.INSTANCE_T_CONV),
[`Arith.PRENEX_CONV`](#Arith.PRENEX_CONV),
[`Arith.SUB_AND_COND_ELIM_CONV`](#Arith.SUB_AND_COND_ELIM_CONV)
