## `DISJ_INEQS_FALSE_CONV` {#Arith.DISJ_INEQS_FALSE_CONV}


```
DISJ_INEQS_FALSE_CONV : conv
```



Proves a disjunction of conjunctions of normalised inequalities is false,
provided each conjunction is unsatisfiable.


`DISJ_INEQS_FALSE_CONV` converts an unsatisfiable normalised arithmetic
formula to false. The formula must be a disjunction of conjunctions of
less-than-or-equal-to inequalities. The inequalities must have the following
form: Each variable must appear on only one side of the inequality and each
side must be a linear sum in which any constant appears first followed by
products of a constant and a variable. On each side the variables must be
ordered lexicographically, and if the coefficient of the variable is `1`, the
`1` must appear explicitly.

### Failure

Fails if the formula is not of the correct form or is satisfiable. The
function will also fail on certain unsatisfiable formulae due to
incompleteness of the procedure used.

### Example

    
    #DISJ_INEQS_FALSE_CONV
    # "(1 * n) <= ((1 * m) + (1 * p)) /\
    #  ((1 * m) + (1 * p)) <= (1 * n) /\
    #  (5 + (4 * n)) <= ((3 * m) + (1 * p)) \/
    #  2 <= 0";;
    |- (1 * n) <= ((1 * m) + (1 * p)) /\
       ((1 * m) + (1 * p)) <= (1 * n) /\
       (5 + (4 * n)) <= ((3 * m) + (1 * p)) \/
       2 <= 0 =
       F
    

### See also

[`Arith.ARITH_FORM_NORM_CONV`](#Arith.ARITH_FORM_NORM_CONV)

