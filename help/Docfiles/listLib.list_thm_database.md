## `list_thm_database`

``` hol4
listLib.list_thm_database: unit -> {{Aux_thms: thm list, Fold_thms: thm list}}
```

------------------------------------------------------------------------

Returns the theorems known by `LIST_CONV`.

The conversion `LIST_CONV` uses a database of theorems relating to
system list constants. These theorems fall into two categories:
definitions of list operators in terms of `FOLDR` and `FOLDL`; and
auxiliary theorems about the base element and step functions in those
definitions. `list_thm_database` provides a means of inspecting the
database.

A call to `list_thm_database()` returns a pair of lists. The first
element of the pair contains the known fold definitions. The second
contains the known auxiliary theorems.

The following is an example of a fold definition in the database:

``` hol4
   |- !l. SUM l = FOLDR $+ 0 l
```

Here `$+` is the step function and 0 is the base element of the
definition. Definitions are initially held for the following system
operators: `APPEND`, `FLAT`, `LENGTH`, `NULL`, `REVERSE`, `MAP`,
`FILTER`, `ALL_EL`, `SUM`, `SOME_EL`, `IS_EL`, `AND_EL`, `OR_EL`,
`PREFIX`, `SUFFIX`, `SNOC` and `FLAT` combined with `REVERSE`.

The following is an example of an auxiliary theorem:

``` hol4
   |- MONOID $+ 0
```

Auxiliary theorems stored include monoid, commutativity, associativity,
binary function commutativity, left identity and right identity
theorems.

### Failure

Never fails.

### See also

[`listLib.LIST_CONV`](#listLib.LIST_CONV),
[`listLib.set_list_thm_database`](#listLib.set_list_thm_database),
[`listLib.X_LIST_CONV`](#listLib.X_LIST_CONV)
