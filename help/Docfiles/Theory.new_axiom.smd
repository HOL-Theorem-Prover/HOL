## `new_axiom`

``` hol4
Theory.new_axiom : string * term -> thm
```

------------------------------------------------------------------------

Install a new axiom in the current theory.

If `M` is a term of type `bool`, a call `new_axiom(name,M)` creates a
theorem

``` hol4
   |- tm
```

and stores it away in the current theory segment under `name`.

### Failure

Fails if the given term does not have type `bool`.

### Example

``` hol4
- new_axiom("untrue", Term `!x. x = 1`);
> val it = |- !x. x = 1 : thm
```

### Comments

For most purposes, it is unnecessary to declare new axioms: all of
classical mathematics can be derived by definitional extension alone.
Proceeding by definition is not only more elegant, but also guarantees
the consistency of the deductions made. However, there are certain
entities which cannot be modelled in simple type theory without further
axioms, such as higher transfinite ordinals.

### See also

[`Thm.mk_thm`](#Thm.mk_thm),
[`Definition.new_definition`](#Definition.new_definition),
[`Definition.new_specification`](#Definition.new_specification)
