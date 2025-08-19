## `EXISTS`

``` hol4
Thm.EXISTS : term * term -> thm -> thm
```

------------------------------------------------------------------------

Introduces existential quantification given a particular witness.

When applied to a pair of terms and a theorem, the first term an
existentially quantified pattern indicating the desired form of the
result, and the second a witness whose substitution for the quantified
variable gives a term which is the same as the conclusion of the
theorem, `EXISTS` gives the desired theorem.

``` hol4
    A |- p[u/x]
   -------------  EXISTS (?x. p, u)
    A |- ?x. p
```

### Failure

Fails unless the substituted pattern is the same as the conclusion of
the theorem.

### Example

The following examples illustrate how it is possible to deduce different
things from the same theorem:

``` hol4
   - EXISTS (Term `?x. x=T`,T) (REFL T);
   > val it = |- ?x. x = T : thm

   - EXISTS (Term `?x:bool. x=x`,T) (REFL T);
   > val it = |- ?x. x = x : thm
```

### See also

[`Thm.CHOOSE`](#Thm.CHOOSE),
[`Drule.SIMPLE_EXISTS`](#Drule.SIMPLE_EXISTS),
[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
