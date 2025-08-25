## `new_type`

``` hol4
Theory.new_type : string * int -> unit
```

------------------------------------------------------------------------

Declares a new type or type constructor.

A call `new_type(t,n)` declares a new `n`-ary type constructor called
`t` in the current theory segment. If `n` is zero, this is just a new
base type.

### Failure

Never fails, but issues a warning if the name is not a valid type name.
It will overwrite an existing type operator with the same name in the
current theory.

### Example

A non-definitional version of ZF set theory might declare a new type
`set` and start using it as follows:

``` hol4
   - new_theory "ZF";
   <<HOL message: Created theory "ZF">>
   > val it = () : unit

   - new_type ("set", 0);
   > val it = () : unit

   - new_constant ("mem", Type`:set->set->bool`);
   > val it = () : unit

   - new_axiom ("EXT", Term`(!z. mem z x = mem z y) ==> (x = y)`);
   > val it = |- (!z. mem z x = mem z y) ==> (x = y) : thm
```

### See also

[`Theory.types`](#Theory.types),
[`Theory.new_constant`](#Theory.new_constant),
[`Theory.new_axiom`](#Theory.new_axiom)
