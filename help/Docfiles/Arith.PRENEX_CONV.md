## `PRENEX_CONV`

``` hol4
Arith.PRENEX_CONV : conv
```

------------------------------------------------------------------------

Puts a formula into prenex normal form.

This function puts a formula into prenex normal form, and in the process
splits any Boolean equalities (if-and-only-if) into two implications. If
there is a Boolean-valued subterm present as the condition of a
conditional, the subterm will be put in prenex normal form, but
quantifiers will not be moved out of the condition. Some renaming of
variables may take place.

### Failure

Never fails.

### Example

``` hol4
> PRENEX_CONV ``!m n. (m <= n) ==> !p. (m < SUC(n + p))``;
val it = |- (!m n. m <= n ==> (!p. m < (SUC(n + p)))) =
            (!m n p. m <= n ==> m < (SUC(n + p)))

> PRENEX_CONV ``!p. (!m. m >= p) = (p = 0)``;
val it = |- (!p. (!m. m >= p) = (p = 0)) =
            (!p m. ?m'. (m' >= p ==> (p = 0)) /\ ((p = 0) ==> m >= p))
```

Useful as a preprocessor to decision procedures which require their
argument formula to be in prenex normal form.

### See also

[`Arith.is_prenex`](#Arith.is_prenex)
