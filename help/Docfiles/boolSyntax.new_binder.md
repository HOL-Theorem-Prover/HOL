## `new_binder`

``` hol4
boolSyntax.new_binder : string * hol_type -> unit
```

------------------------------------------------------------------------

Sets up a new binder in the current theory.

A call `new_binder(bnd,ty)` declares a new binder `bnd` in the current
theory. The type must be of the form `('a -> 'b) -> 'c`, because being a
binder, `bnd` will apply to an abstraction; for example

``` hol4
   !x:bool. (x=T) \/ (x=F)
```

is actually a prettyprinting of

``` hol4
   $! (\x. (x=T) \/ (x=F))
```

### Failure

Fails if the type does not correspond to the above pattern.

### Example

``` hol4
   - new_theory "anorak";
   > val it = () : unit

   - new_binder ("!!", (bool-->bool)-->bool);
   > val it = () : unit

   - Term `!!x. T`;
   > val it = `!! x. T` : term
```

### See also

[`Theory.constants`](#Theory.constants),
[`Theory.new_constant`](#Theory.new_constant),
[`boolSyntax.new_infix`](#boolSyntax.new_infix),
[`Definition.new_definition`](#Definition.new_definition),
[`boolSyntax.new_infixl_definition`](#boolSyntax.new_infixl_definition),
[`boolSyntax.new_infixr_definition`](#boolSyntax.new_infixr_definition),
[`boolSyntax.new_binder_definition`](#boolSyntax.new_binder_definition)
