## `EVERY_CONJ_CONV`

``` hol4
Conv.EVERY_CONJ_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to every top-level conjunct in a term.

The term `EVERY_CONJ_CONV c t` takes the conversion `c` and applies this
to every top-level conjunct within term `t`. A top-level conjunct is a
sub-term that can be reached from the root of the term by breaking apart
only conjunctions. The terms affected by `c` are those that would be
returned by a call to `strip_conj c`. In particular, if the term as a
whole is not a conjunction, then the conversion will be applied to the
whole term.

If the result of the application of the conversion to one of the
conjuncts is one of the constants true or false, then one of two
standard rewrites is applied, simplifying the resulting term. If one of
the conjuncts is converted to false, then the conversion will not be
applied to the remaining conjuncts (the conjuncts are worked on from
left to right), and the result of the whole application will simply be
false. Alternatively, conjuncts that are converted to true will not
appear in the final result at all.

### Failure

Fails if the conversion argument fails when applied to one of the
top-level conjuncts in a term.

### Example

``` hol4
- EVERY_CONJ_CONV BETA_CONV (Term`(\x. x /\ y) p`);
> val it = |- (\x. x /\ y) p = p /\ y : thm
- EVERY_CONJ_CONV BETA_CONV (Term`(\y. y /\ p) q /\ (\z. z) r`);
> val it = |- (\y. y /\ p) q /\ (\z. z) r = (q /\ p) /\ r : thm
```

Useful for applying a conversion to all of the "significant" sub-terms
within a term without having to worry about the exact structure of its
conjunctive skeleton.

### See also

[`Conv.EVERY_DISJ_CONV`](#Conv.EVERY_DISJ_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV), [`Conv.LAND_CONV`](#Conv.LAND_CONV)
