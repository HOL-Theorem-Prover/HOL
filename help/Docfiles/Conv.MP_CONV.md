## `MP_CONV`

``` hol4
Conv.MP_CONV : conv -> conv
```

------------------------------------------------------------------------

Eliminate the antecedent of a theorem using a conversion/proof rule.

If `c` is a conversion that when applied to `P` returns the theorem
`|- P = T` or `|- P`, and `th` is a theorem of the general form
`|- P ==> Q`, then `MP_CONV c th` will return the theorem `|- Q`,
i.e. the antecedent of `th` is eliminated by the conversion `c`. This is
done by calling `MP` on `|- P ==> Q` and `|- P`.

### Failure

`MP_CONV c th` will fail if `th` is not of the form `|- P ==> Q` or if
`c` fails when applied to `P`.

### Example

``` hol4
- load "realLib"; open realTheory realLib;
- MP_CONV REAL_ARITH (Q.SPEC `1` REAL_DOWN);
> val it = |- ?y. 0 < y /\ y < 1: thm
```

### Comments

This conversion is ported from HOL-Light (`drule.ml`). `MP_CONV` is
useful when a universal theorem, after instantiating some of its
quantifiers, the antecedent becomes a tautology that can be eliminated
by a conversion.

### See also

[`Thm.MP`](#Thm.MP)
