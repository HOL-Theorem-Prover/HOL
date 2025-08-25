## `new_binder_definition`

``` hol4
boolSyntax.new_binder_definition : string * term -> thm
```

------------------------------------------------------------------------

Defines a new constant, giving it the syntactic status of a binder.

The function `new_binder_definition` provides a facility for making
definitional extensions to the current theory by introducing a constant
definition. It takes a pair of arguments, consisting of the name under
which the resulting theorem will be saved in the current theory segment
and a term giving the desired definition. The value returned by
`new_binder_definition` is a theorem which states the definition
requested by the user.

Let `v1`, ..., `vn` be syntactically distinct tuples constructed from
the variables `x1,...,xm`. A binder is defined by evaluating

``` hol4
new_binder_definition (name, `b v1 ... vn = t`)
```

where `b` does not occur in `t`, all the free variables that occur in
`t` are a subset of `x1,...,xn`, and the type of `b` has the form
`(ty1->ty2)->ty3`. This declares `b` to be a new constant with the
syntactic status of a binder in the current theory, and with the
definitional theorem

``` hol4
   |- !x1...xn. b v1 ... vn = t
```

as its specification. This constant specification for `b` is saved in
the current theory under the name `name` and is returned as a theorem.

The equation supplied to `new_binder_definition` may optionally have any
of its free variables universally quantified at the outermost level. The
constant `b` has binder status only after the definition has been made.

### Failure

`new_binder_definition` fails if `t` contains free variables that are
not in any one of the variable structures `v1`, ..., `vn` or if any
variable occurs more than once in `v1, ..., v2`. Failure also occurs if
the type of `b` is not of the form appropriate for a binder, namely a
type of the form `(ty1->ty2)->ty3`. Finally, failure occurs if there is
a type variable in `v1`, ..., `vn` or `t` that does not occur in the
type of `b`.

### Example

The unique-existence quantifier `?!` is defined as follows.

``` hol4
- new_binder_definition
     (`EXISTS_UNIQUE_DEF`,
      Term`$?! = \P:(*->bool). ($? P) /\ (!x y. ((P x) /\ (P y)) ==> (x=y))`);

> val it = |- $?! = (\P. $? P /\ (!x y. P x /\ P y ==> (x = y))) : thm
```

### Comments

It is a common practice among HOL users to write a `$` before the
constant being defined as a binder to indicate that it will have a
special syntactic status after the definition is made:

``` hol4
new_binder_definition(name, Term `$b = ... `);
```

This use of `$` is not necessary; but after the definition has been made
`$` must, of course, be used if the syntactic status of `b` needs to be
suppressed.

### See also

[`Definition.new_definition`](#Definition.new_definition),
[`boolSyntax.new_infixl_definition`](#boolSyntax.new_infixl_definition),
[`boolSyntax.new_infixr_definition`](#boolSyntax.new_infixr_definition),
[`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition),
[`TotalDefn.Define`](#TotalDefn.Define)
