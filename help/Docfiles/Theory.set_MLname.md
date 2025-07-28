## `set_MLname` {#Theory.set_MLname}


```
set_MLname : string -> string -> unit
```



Change the name attached to an element of the current theory.


It can happen that an axiom, definition, or theorem gets stored in the
current theory segment under a name that wouldn’t be a suitable ML
identifier. For example, some advanced definition mechanisms in HOL
automatically construct names to bind the results of making a
definition. In some cases, particularly when symbolic identifiers are
involved, a binding name can be generated that is not a valid ML
identifier.

In such cases, we don’t want to fail and lose the work done by the
definition mechanism. Instead, when `export_theory` is invoked,
all names binding axioms, definitions, and theorems are examined
to see if they are valid ML identifiers. If not, an informative
error message is generated, and it is up to the user to change the
names in the offending bindings. The function `set_MLname s1 s2` will
replace a binding with name `s1` by one with name `s2`.

### Failure

Never fails, although will give a warning if `s1` is not the name
of a binding in the current theory segment.

### Example

We inductively define a predicate telling if a number is odd in the
following. The name is admittedly obscure, however it illustrates our
point.
    
    - Hol_reln `(%% 1) /\ (!n. %% n ==> %% (n+2))`;
    > val it =
        (|- %% 1 /\ !n. %% n ==> %% (n + 2),
         |- !%%'. %%' 1 /\ (!n. %%' n ==> %%' (n + 2)) ==> !a0. %% a0 ==> %%' a0,
         |- !a0. %% a0 = (a0 = 1) \/ ?n. (a0 = n + 2) /\ %% n) : thm * thm * thm
    
    - export_theory();
    <<HOL message: The following ML binding names in the theory to be exported:
    "%%_rules", "%%_ind", "%%_cases"
     are not acceptable ML identifiers.
       Use `set_MLname <bad> <good>' to change each name.>>
    ! Uncaught exception:
    ! HOL_ERR
    
    - (set_MLname "%%_rules" "odd_rules";   (* OK, do what it says *)
       set_MLname "%%_ind"   "odd_ind";
       set_MLname "%%_cases" "odd_cases");
    > val it = () : unit
    
    - export_theory();
    Exporting theory "scratch" ... done.
    > val it = () : unit
    



### Comments

The definition principles that currently have the potential to make
problematic bindings are `Hol_datatype` and `Hol_reln`.

It is slightly awkward to have to repair the names in a post-hoc fashion.
It is probably simpler to proceed by using alphanumeric names when
defining constants, and to use overloading to get the desired name.

### See also

[`bossLib.Hol_reln`](#bossLib.Hol_reln), [`bossLib.Hol_datatype`](#bossLib.Hol_datatype), [`Theory.export_theory`](#Theory.export_theory), [`Theory.current_definitions`](#Theory.current_definitions), [`Theory.current_theorems`](#Theory.current_theorems), [`Theory.current_axioms`](#Theory.current_axioms), [`DB.thy`](#DB.thy), [`DB.dest_theory`](#DB.dest_theory)

