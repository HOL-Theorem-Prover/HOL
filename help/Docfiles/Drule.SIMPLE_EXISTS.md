## `SIMPLE_EXISTS`

``` hol4
Drule.SIMPLE_EXISTS : term -> thm -> thm
```

------------------------------------------------------------------------

Introduces existential quantification using as witness a given free
variable.

When applied to a free variable term and a theorem, `SIMPLE_EXISTS`
gives the theorem made by existentially quantifying the conclusion of
the given theorem over the given free variable.

``` hol4
    A |- p
   -------------  SIMPLE_EXISTS ``x``
    A |- ?x. p
```

### Failure

Fails if the term argument is not a free variable.

### Comments

The free variable need not appear in the conclusion of the theorem, and
may appear in the hypotheses.

### Example

``` hol4
   - SIMPLE_EXISTS (Term `x`) (REFL (Term `x`));
   > val it = |- ?x. x = x : thm

   - SIMPLE_EXISTS (Term `x`) (REFL T);
   > val it = |- ?x. T = T : thm
```

### See also

[`Thm.EXISTS`](#Thm.EXISTS), [`Thm.CHOOSE`](#Thm.CHOOSE),
[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
