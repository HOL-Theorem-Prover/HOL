## `non_presburger_subterms`

``` hol4
Arith.non_presburger_subterms : (term -> term list)
```

------------------------------------------------------------------------

Computes the subterms of a term that are not in the Presburger subset of
arithmetic.

This function computes a list of subterms of a term that are not in the
Presburger subset of natural number arithmetic. All numeric variables in
the term are included in the result. Presburger natural arithmetic is
the subset of arithmetic formulae made up from natural number constants,
numeric variables, addition, multiplication by a constant, the natural
number relations `<`, `<=`, `=`, `>=`, `>` and the logical connectives
`~`, `/\`, `\/`, `==>`, `=` (if-and-only-if), `!` ('forall') and `?`
('there exists').

Products of two expressions which both contain variables are not
included in the subset, so such products will appear in the result list.
However, the function `SUC` which is not normally included in a
specification of Presburger arithmetic is allowed in this HOL
implementation. This function also considers subtraction and the
predecessor function, `PRE`, to be part of the subset.

### Failure

Never fails.

### Example

``` hol4
#non_presburger_subterms "!m n p. m < (2 * n) /\ (n + n) <= p ==> m < SUC p";;
["m"; "n"; "p"] : term list

#non_presburger_subterms "!m n p q. m < (n * p) /\ (n * p) < q ==> m < q";;
["m"; "n * p"; "q"] : term list

#non_presburger_subterms "(m + n) - m = f n";;
["m"; "n"; "f n"] : term list
```

### See also

[`Arith.INSTANCE_T_CONV`](#Arith.INSTANCE_T_CONV),
[`Arith.is_presburger`](#Arith.is_presburger)
