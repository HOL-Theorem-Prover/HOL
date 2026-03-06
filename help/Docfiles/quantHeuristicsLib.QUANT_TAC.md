## `QUANT_TAC`

``` hol4
quantHeuristicsLib.QUANT_TAC : (string * Parse.term Lib.frag list * Parse.term Parse.frag list list) list -> tactic
```

------------------------------------------------------------------------

A tactic to instantiate quantifiers in a term using an explitly given
list of (partial) instantiations.

This tactic can be seen as a generalisation of `Q.EXISTS_TAC`. When
applied to a term fragment `u` and a goal `?x. t`, the tactic
`EXISTS_TAC` reduces the goal to `t[u/x]`. `QUANT_TAC` allows to perform
similar instantiations of quantifiers at subpositions, provided the
subposition occurs in a formula composed of standard operators that the
tactic can handle. It can - depending on negation level - instantiate
both existential and universal quantifiers. Moreover, it allows partial
instantiations and instantiating multiple variables at the same time.

`QUANT_TAC` gets a list of triples
`(var_name, instantiation, free_vars)` as an argument. `var_name` is the
name of the variable to be instantiated; `instantiation` is the term
this variable should be instantiated with. Finally, `free_vars` is a
list of free variables in `instantiation` that should remain quantified.

As this tactic adresses variables by their name, resulting proofs might
not be robust. Therefore, this tactic should be used carefully.

### Example

Given the goal

``` hol4
   !x. (!z. P x z) ==> ?a b.    Q a        b z
```

where `z` and `a` are natural numbers, the call
`` QUANT_TAC [("z", `0`, []), ("a", `SUC a'`, [`a'`])] `` instantiates
`z` with `0` and `a` with `SUC a'`, where `a'` is free. The variable `z`
is universally quantified, but in the antecedent of the implication.
Therefore, it can be safely instantiated. `a` is existentially
quantified. In this example we just want to say that `a` is not `0`,
therefore `a'` is considered as a free variable and thus remains
existentially quantified. The call results in the goal

``` hol4
   !x. (    P x 0) ==> ?  b a'. Q (SUC a') b z
```

### See also

[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
