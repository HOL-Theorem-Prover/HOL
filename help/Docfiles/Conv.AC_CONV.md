## `AC_CONV`

``` hol4
Conv.AC_CONV : (thm * thm) -> conv
```

------------------------------------------------------------------------

Proves equality of terms using associative and commutative laws.

Suppose `_` is a function, which is assumed to be infix in the following
syntax, and `ath` and `cth` are theorems expressing its associativity
and commutativity; they must be of the following form, except that any
free variables may have arbitrary names and may be universally
quantified:

``` hol4
   ath = |- m _ (n _ p) = (m _ n) _ p
   cth = |- m _ n = n _ m
```

Then the conversion `AC_CONV(ath,cth)` will prove equations whose left
and right sides can be made identical using these associative and
commutative laws.

### Failure

Fails if the associative or commutative law has an invalid form, or if
the term is not an equation between AC-equivalent terms.

### Example

Consider the terms `x + SUC t + ((3 + y) + z)` and
`3 + SUC t + x + y + z`. `AC_CONV` proves them equal.

``` hol4
   - AC_CONV(ADD_ASSOC,ADD_SYM)
       (Term `x + (SUC t) + ((3 + y) + z) = 3 + (SUC t) + x + y + z`);

   > val it =
     |- (x + ((SUC t) + ((3 + y) + z)) = 3 + ((SUC t) + (x + (y + z)))) = T
```

### Comments

Note that the preproved associative and commutative laws for the
operators `+`, `*`, `/\` and `\/` are already in the right form to give
to `AC_CONV`.

### See also

[`Conv.SYM_CONV`](#Conv.SYM_CONV)
