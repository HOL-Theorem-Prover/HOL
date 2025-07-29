## `delete_binding`

``` hol4
Theory.delete_binding : string -> unit
```

------------------------------------------------------------------------

Remove a stored value from the current theory segment.

An invocation `delete_binding s` attempts to locate an axiom,
definition, or theorem that has been stored under name `s` in the
current theory segment. If such a binding can be found, it is deleted.

### Failure

Never fails. If the binding can't be found, then nothing is removed from
the current theory segment.

### Example

``` hol4
- Define `fact x = if x=0 then 1 else x * fact (x-1)`;
Equations stored under "fact_def".
Induction stored under "fact_ind".
> val it = |- fact x = (if x = 0 then 1 else x * fact (x - 1)) : thm

- current_theorems();
> val it =
    [("fact_def", |- fact x = (if x = 0 then 1 else x * fact (x - 1))),
     ("fact_ind", |- !P. (!x. (~(x = 0) ==> P (x - 1)) ==> P x) ==> !v. P v)]
  : (string * thm) list

- delete_binding "fact_ind";
> val it = () : unit

- current_theorems();
> val it =
    [("fact_def", |- fact x = (if x = 0 then 1 else x * fact (x - 1)))]
   : (string * thm) list
```

### Comments

Removing a definition binding does not remove the constant(s) it
introduced from the signature. Use `delete_const` for that.

Removing an axiom has the consequence that all theorems proved from it
become garbage.

### See also

[`Theory.scrub`](#Theory.scrub),
[`Theory.delete_type`](#Theory.delete_type),
[`Theory.delete_const`](#Theory.delete_const)
