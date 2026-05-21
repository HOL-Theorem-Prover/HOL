## `EVERY_DISJ_CONV`

``` hol4
Conv.EVERY_DISJ_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to every top-level disjunct in a term.

The term `EVERY_DISJ_CONV c t` takes the conversion `c` and applies this
to every top-level disjunct within term `t`. A top-level disjunct is a
sub-term that can be reached from the root of the term by breaking apart
only disjunctions. The terms affected by `c` are those that would be
returned by a call to `strip_disj c`. In particular, if the term as a
whole is not a disjunction, then the conversion will be applied to the
whole term.

If the result of the application of the conversion to one of the
disjuncts is one of the constants true or false, then one of two
standard rewrites is applied, simplifying the resulting term. If one of
the disjuncts is converted to true, then the conversion will not be
applied to the remaining disjuncts (the disjuncts are worked on from
left to right), and the result of the whole application will simply be
true. Alternatively, disjuncts that are converted to false will not
appear in the final result at all.

### Failure

Fails if the conversion argument fails when applied to one of the
top-level disjuncts in the term.

### Example

``` hol4
- EVERY_DISJ_CONV BETA_CONV
    (Term`(\x. x /\ p) q \/ (\x. x) r \/ (\y. s /\ y) u`);
> val it =
    |- (\x. x /\ p) q \/ (\x. x) r \/ (\y. s /\ y) u = q /\ p \/ r \/ s /\ u
    : thm
- EVERY_DISJ_CONV REDUCE_CONV ``3 < x \/ 2 < 3 \/ 2 EXP 1000 < 10``;
> val it = |- 3 < x \/ 2 < 3 \/ 2 EXP 1000 < 10 = T : thm
```

Useful for applying a conversion to all of the "significant" sub-terms
within a term without having to worry about the exact structure of its
disjunctive skeleton.

### See also

[`Conv.EVERY_CONJ_CONV`](#Conv.EVERY_CONJ_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.LAND_CONV`](#Conv.LAND_CONV),
[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV)
