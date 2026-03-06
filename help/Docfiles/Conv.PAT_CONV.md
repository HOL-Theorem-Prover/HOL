## `PAT_CONV`

``` hol4
Conv.PAT_CONV : term -> conv -> conv
```

------------------------------------------------------------------------

Applies a conversion at specific sub-terms, following a pattern

The call ``` PAT_CONV ``\x1 ... xn. t[x1,...,xn]`` cnv ``` returns a new
conversion that applies `cnv` to subterms of the target term
corresponding to the free instances of any `xi` in the pattern
`t[x1,...,xn]`. The fact that the pattern is a function has no logical
significance; it is just used as a convenient format for the pattern.

### Failure

Never fails until applied to a term, but then it may fail if the core
conversion does on the chosen subterms, or if the pattern doesn't match
the structure of the term.

### Example

Here we choose to evaluate just two subterms:

``` hol4
   > PAT_CONV ``\x. x + a + x`` numLib.REDUCE_CONV
              ``(1 + 2) + (3 + 4) + (5 + 6)``;
   val it : thm = |- 1 + 2 + (3 + 4) + (5 + 6) = 3 + (3 + 4) + 11
```

while here we swap two particular quantifiers in a long chain:

``` hol4
   > PAT_CONV ``\x. !x1 x2 x3 x4 x5. x`` SWAP_FORALL_CONV
              ``!a b c d e f g h. something``
   <<HOL message: inventing new type variable names: ...>>
   val it =
     |- (!a b c d e f g h. something) <=>
        !a b c d e g f h. something: thm
```

### Comments

Multiple bound variables will only be necessary if the conversion needs
to be applied to sub-terms of different types.

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV), [`Conv.COMB_CONV`](#Conv.COMB_CONV),
[`Conv.PATH_CONV`](#Conv.PATH_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV), [`Conv.SUB_CONV`](#Conv.SUB_CONV)
