## `PEXISTS`

``` hol4
PairRules.PEXISTS : term * term -> thm -> thm
```

------------------------------------------------------------------------

Introduces paired existential quantification given a particular witness.

When applied to a pair of terms and a theorem, where the first term a
paired existentially quantified pattern indicating the desired form of
the result, and the second a witness whose substitution for the
quantified pair gives a term which is the same as the conclusion of the
theorem, `PEXISTS` gives the desired theorem.

``` hol4
    A |- t[q/p]
   -------------  EXISTS ("?p. t","q")
    A |- ?p. t
```

### Failure

Fails unless the substituted pattern is the same as the conclusion of
the theorem.

### Example

The following examples illustrate the various uses of `PEXISTS`:

``` hol4
   - PEXISTS (Term`?x. x + 2 = x + 2`, Term`1`) (REFL (Term`1 + 2`));
   > val it = |- ?x. x + 2 = x + 2 : thm

   - PEXISTS (Term`?y. 1 + y = 1 + y`, Term`2`) (REFL (Term`1 + 2`));
   > val it = |- ?y. 1 + y = 1 + y : thm

   - PEXISTS (Term`?(x,y). x + y = x + y`, Term`(1,2)`) (REFL (Term`1 + 2`));
   > val it = |- ?(x,y). x + y = x + y : thm

   - PEXISTS (Term`?(a:'a,b:'a). (a,b) = (a,b)`, Term`ab:'a#'a`)
             (REFL (Term `ab:'a#'a`));
   > val it = |- ?(a,b). (a,b) = (a,b) : thm
```

### See also

[`Thm.EXISTS`](#Thm.EXISTS), [`PairRules.PCHOOSE`](#PairRules.PCHOOSE),
[`PairRules.PEXISTS_TAC`](#PairRules.PEXISTS_TAC)
