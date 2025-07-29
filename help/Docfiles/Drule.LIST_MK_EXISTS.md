## `LIST_MK_EXISTS`

``` hol4
Drule.LIST_MK_EXISTS : (term list -> thm -> thm)
```

------------------------------------------------------------------------

Multiply existentially quantifies both sides of an equation using the
given variables.

When applied to a list of terms `[x1;...;xn]`, where the `xi` are all
variables, and a theorem `A |- t1 = t2`, the inference rule
`LIST_MK_EXISTS` existentially quantifies both sides of the equation
using the variables given, none of which should be free in the
assumption list.

``` hol4
                A |- t1 = t2
   --------------------------------------  LIST_MK_EXISTS ["x1";...;"xn"]
    A |- (?x1...xn. t1) = (?x1...xn. t2)
```

### Failure

Fails if any term in the list is not a variable or is free in the
assumption list, or if the theorem is not equational.

### See also

[`Drule.EXISTS_EQ`](#Drule.EXISTS_EQ),
[`Drule.MK_EXISTS`](#Drule.MK_EXISTS)
