## `Hol_datatype`

``` hol4
bossLib.Hol_datatype : hol_type quotation -> unit
```

------------------------------------------------------------------------

Define a concrete datatype (deprecated syntax).

The `Hol_datatype` function provides exactly the same definitional power
as the `Datatype` function (which see), with a slightly different input
syntax, given below:

``` hol4
   spec    ::= [ <binding> ; ]* <binding>

   binding ::= <ident> = [ <clause> | ]* <clause>
            |  <ident> = <| [ <ident> : <type> ; ]* <ident> : <type> |>

   clause  ::= <ident>
            |  <ident> of [<type> => ]* <type>
```

### Example

For example, what with `Datatype` would be

``` hol4
   Datatype`btree = Leaf 'a | Node btree 'b btree
```

is

``` hol4
   Hol_datatype `btree = Leaf of 'a
                       | Node of btree => 'b => btree`
```

when using `Hol_datatype`.

The `=>` notation in the description highlights the fact that, in HOL,
constructors are by default curried.

### Comments

The `Datatype` function's syntax is easier to write and easier to
understand.

### See also

[`bossLib.Datatype`](#bossLib.Datatype)
