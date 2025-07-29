## `datatype_theorems`

``` hol4
EmitTeX.datatype_theorems : string -> (string * thm) list
```

------------------------------------------------------------------------

All the datatype theorems stored in the named theory.

An invocation `datatype_theorems thy`, where `thy` is the name of a
currently loaded theory segment, will return a list of the datatype
theorems stored in that theory. Each theorem is paired with the name of
the datatype in the result. The string "-" may be used to denote the
current theory segment.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory
segment, the empty list is returned.

### Example

``` hol4
- new_theory "example";
<<HOL message: Created theory "example">>
> val it = () : unit
- val _ = Hol_datatype `example = First | Second`;
<<HOL message: Defined type: "example">>
- EmitTeX.datatype_theorems "example";
> val it = [("example", |- DATATYPE (example First Second))] :
  (string * thm) list
```

### See also

[`DB.theorems`](#DB.theorems),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype)
