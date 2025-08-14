## `SUC_TO_NUMERAL_DEFN_CONV`

``` hol4
numLib.SUC_TO_NUMERAL_DEFN_CONV : conv
```

------------------------------------------------------------------------

Translates equations using `SUC n` to use numeral constructors instead.

This conversion modifies conjunctions of universally quantified
equations so that any argument terms of the form `SUC x` on the LHS of
the equations (with `x` one of the equation's universally quantified
variables), are translated to a form appropriate for rewriting when the
argument term is a numeral.

This procedure uses the following theorem:

``` hol4
  |- !f g. (!n. f (SUC n) = g n (SUC n)) =
           (!n. f (NUMERAL (BIT1 n)) =
                g (NUMERAL (BIT1 n)) (NUMERAL (BIT1 n) - 1)) /\
           (!n. f (NUMERAL (BIT2 n)) =
                g (NUMERAL (BIT2 n)) (NUMERAL (BIT1 n)))
```

### Example

``` hol4
- CONV_RULE SUC_TO_NUMERAL_DEFN_CONV arithmeticTheory.FACT;
> val it =
    |- (FACT 0 = 1) /\
       (!n.
          FACT (NUMERAL (BIT1 n)) =
            NUMERAL (BIT1 n) * FACT (NUMERAL (BIT1 n) - 1)) /\
       !n.
         FACT (NUMERAL (BIT2 n)) =
           NUMERAL (BIT2 n) * FACT (NUMERAL (BIT1 n)) : thm
```

### Failure

Fails if the input term is not the conjunction of universally quantified
equations, where there may be just one conjunct, and where equations may
have no quantification at all. Those conjuncts which don't involve terms
of the form `SUC x` are returned unchanged.

### Comments

Useful for translating definitions over numbers (which often involve
`SUC` terms), into a form that can be used to work with numerals easily.

### See also

[`numLib.num_CONV`](#numLib.num_CONV)
