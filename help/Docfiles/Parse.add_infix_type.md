## `add_infix_type`

``` hol4
Parse.add_infix_type : {Assoc : associativity,
                  Name : string,
                  ParseName : string option,
                  Prec : int} ->
                 unit
```

------------------------------------------------------------------------

Adds a type infix.

A call to `add_infix_type` adds an infix type symbol to the type
grammar. The argument is a record of four values providing information
about the infix.

The `Assoc` field specifies the associativity of the symbol (possible
values: `LEFT`, `RIGHT` and `NONASSOC`). The standard HOL type infixes
(`+`, `#`, `->` and `|->`) are all right-associative. The `Name` field
specifies the name of the binary type operator that is being mapped to.
If the name of the type is not the same as the concrete syntax (as in
all the standard HOL examples above), the concrete syntax can be
provided in the `ParseName` field. The `Prec` field specifies the
binding precedence of the infix. This should be a number less than 100,
and probably greater than or equal to 50, where the function `->` symbol
lies. The greater the number, the more tightly the symbol attempts to
"grab" its arguments.

### Failure

Fails if the desired precedence level contains an existing infix with a
different associativity.

### Example

``` hol4
- Hol_datatype `atree = Nd of 'v => ('k # atree) list`;
<<HOL message: Defined type: "atree">>
> val it = () : unit

- add_infix_type { Assoc = LEFT, Name = "atree",
                   ParseName = SOME ">->", Prec = 65 };
> val it = () : unit

- type_of ``Nd``;
<<HOL message: inventing new type variable names: 'a, 'b>>
> val it = ``:'a -> ('b # ('b >-> 'a)) list -> 'b >-> 'a`` : hol_type
```
