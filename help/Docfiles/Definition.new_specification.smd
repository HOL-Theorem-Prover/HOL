## `new_specification`

``` hol4
Definition.new_specification : string * string list * thm -> thm
```

------------------------------------------------------------------------

Introduce a constant or constants satisfying a given property.

The ML function `new_specification` implements the primitive rule of
constant specification for the HOL logic. Evaluating:

``` hol4
   new_specification (name, ["c1",...,"cn"], |- ?x1...xn. t)
```

simultaneously introduces new constants named `c1`,...,`cn` satisfying
the property:

``` hol4
   |- t[c1,...,cn/x1,...,xn]
```

This theorem is stored, with name `name`, as a definition in the current
theory segment. It is also returned by the call to `new_specification`.

### Failure

`new_specification` fails if the theorem argument has assumptions or
free variables. It also fails if the supplied constant names `c1`, ...,
`cn` are not distinct. It also fails if the length of the existential
prefix of the theorem is not at least `n`. Finally, failure occurs if
some `ci` does not contain all the type variables that occur in the term
`?x1...xn. t`.

`new_specification` can be used to introduce constants that satisfy a
given property without having to make explicit equational constant
definitions for them. For example, the built-in constants `MOD` and
`DIV` are defined in the system by first proving the theorem:

``` hol4
   th |- ?MOD DIV.
           !n. 0 < n ==> !k. (k = (DIV k n * n) + MOD k n) /\ MOD k n < n
```

and then making the constant specification:

``` hol4
   new_specification ("DIVISION", ["MOD","DIV"], th)
```

This introduces the constants `MOD` and `DIV` with the defining property
shown above.

### Comments

The introduced constants have a prefix parsing status. To alter this,
use `set_fixity`. Typical fixity values are `Binder`, `Infixl n`,
`Infixr n`, `Prefix n`, `Suffix n`, or `Closefix`.

### See also

[`Definition.gen_new_specification`](#Definition.gen_new_specification),
[`Definition.new_definition`](#Definition.new_definition),
[`boolSyntax.new_binder_definition`](#boolSyntax.new_binder_definition),
[`boolSyntax.new_infixl_definition`](#boolSyntax.new_infixl_definition),
[`boolSyntax.new_infixr_definition`](#boolSyntax.new_infixr_definition),
[`TotalDefn.Define`](#TotalDefn.Define),
[`Parse.set_fixity`](#Parse.set_fixity)
