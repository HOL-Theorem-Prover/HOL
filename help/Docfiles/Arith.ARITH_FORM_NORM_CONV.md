## `ARITH_FORM_NORM_CONV` {#Arith.ARITH_FORM_NORM_CONV}


```
ARITH_FORM_NORM_CONV : conv
```



Normalises an unquantified formula of linear natural number arithmetic.


`ARITH_FORM_NORM_CONV` converts a formula of natural number arithmetic into a
disjunction of conjunctions of less-than-or-equal-to inequalities. The
arithmetic expressions are only allowed to contain natural number constants,
numeric variables, addition, the `SUC` function, and multiplication by a
constant. The formula must not contain quantifiers, but may have disjunction,
conjunction, negation, implication, equality on Booleans (if-and-only-if), and
the natural number relations: `<`, `<=`, `=`, `>=`, `>`. The formula must not
contain products of two expressions which both contain variables.

The inequalities in the result are normalised so that each variable appears on
only one side of the inequality, and each side is a linear sum in which any
constant appears first followed by products of a constant and a variable. The
variables are ordered lexicographically, and if the coefficient of the
variable is `1`, the product of `1` and the variable appears in the term
rather than the variable on its own.

### Failure

The function fails if the argument term is not a formula in the specified
subset.

### Example

    
    #ARITH_FORM_NORM_CONV "m < n";;
    |- m < n = (1 + (1 * m)) <= (1 * n)
    
    #ARITH_FORM_NORM_CONV
    # "(n < 4) ==> ((n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3))";;
    |- n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3) =
       4 <= (1 * n) \/
       (1 * n) <= 0 /\ 0 <= (1 * n) \/
       (1 * n) <= 1 /\ 1 <= (1 * n) \/
       (1 * n) <= 2 /\ 2 <= (1 * n) \/
       (1 * n) <= 3 /\ 3 <= (1 * n)
    


Useful in constructing decision procedures for linear arithmetic.
