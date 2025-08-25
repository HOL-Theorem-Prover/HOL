## `LIST_REFINE_EXISTS_TAC`

``` hol4
Q.LIST_REFINE_EXISTS_TAC : term quotation list -> tactic
```

------------------------------------------------------------------------

Attacks existential goals, making existential variables more concrete.

`Q.LIST_REFINE_EXISTS_TAC` is similar to `Q.REFINE_EXISTS_TAC`, except
it accepts a list of quotations rather than a single one. It further
skips quotations of a single variable beginning with an underscore,
permitting straightforward refinement of nested existentials.

Note that quotations are parsed right-to-left, so earlier quotations are
parsed in the context of later ones.

### Failure

Fails if passed too many quotations for the current goal. Otherwise
fails similarly to `Q.REFINE_EXISTS_TAC`.

### Example

``` hol4
  - Q.LIST_REFINE_EXISTS_TAC [`_`,`SUC c`,`_`,`n + m`]
      ([``n = 2``,``c = 5``], ``∃a b c d. a + b = c + d``);
  > val it =
       ([([``n = 2``, ``c = 5``], ``∃a c' m. a + SUC c = c' + (n + m)``)], fn)
       : goal list * validation
```

Like `Q.REFINE_EXISTS_TAC`, `Q.LIST_REFINE_EXISTS_TAC` is useful if it
is clear that an existential goal can be solved by a term of particular
form, but it is not yet clear exactly what this term will be.

It is particularly useful when refining deeply-nested existentials, or
many existentials at once.

### Comments

This tactic is also available under the alias `bossLib.qrefinel`.

### See also

[`Q.REFINE_EXISTS_TAC`](#Q.REFINE_EXISTS_TAC),
[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
