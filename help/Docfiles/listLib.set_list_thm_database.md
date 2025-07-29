## `set_list_thm_database`

``` hol4
listLib.set_list_thm_database: {{Aux_thms: thm list, Fold_thms: thm list}} -> unit
```

------------------------------------------------------------------------

Modifies the database of theorems known by `LIST_CONV` and
`X_LIST_CONV`.

The conversions `LIST_CONV` and `X_LIST_CONV` use a database of theorems
relating to system list constants. These theorems fall into two
categories: definitions of list operators in terms of `FOLDR` and
`FOLDL`; and auxiliary theorems about the base elements and step
functions in those definitions. The database can be modified using
`set_list_thm_database`.

A call `set_list_thm_database{{Fold_thms=fold_thms,Aux_thms=aux_thms}}`
replaces the existing database with the theorems given as the arguments.
The `Fold_thms` field of the record contains the new fold definitions.
The `Aux_thms` field contains the new auxiliary theorems. Theorems which
do not have an appropriate form will be ignored.

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

The conversion `LIST_CONV` uses the theorems in the database to prove
theorems about list operators. Users are encouraged to define list
operators in terms of either `FOLDR` or `FOLDL` rather than recursively.
Then if the definition is passed to `LIST_CONV`, it will be able to
prove the recursive clauses for the definition. If auxilary properties
are proved about the step function and base element, and they are passed
to `LIST_CONV` then it may be able to prove other useful theorems.
Theorems can be passed either as arguments to `LIST_CONV` or they can be
added to the database using `set_list_thm_database`.

### Example

After the following call, `LIST_CONV` will only be able to prove a few
theorems about `SUM`.

``` hol4
   set_list_thm_database
     {{Fold_thms = [theorem "list" "SUM_FOLDR"],
      Aux_thms = [theorem "arithmetic" "MONOID_ADD_0"]}};
```

The following shows a new definition being added which multiplies the
elements of a list. `LIST_CONV` is then called to prove the recursive
clause.

``` hol4
   - val MULTL = new_definition("MULTL",“MULTL l = FOLDR $* 1 l”);
   val MULTL = |- !l. MULTL l = FOLDR $* 1 l : thm
   - let val {{Fold_thms = fold_thms, Aux_thms = aux_thms}} = list_thm_database()
   = in
   =   set_list_thm_database{{Fold_thms = MULTL::fold_thms,Aux_thms = aux_thms}}
   = end;
   val it = () : unit
   - LIST_CONV “MULTL (CONS x l)”;
   |- MULTL (CONS x l) = x * MULTL l
```

### Failure

Never fails.

### See also

[`listLib.LIST_CONV`](#listLib.LIST_CONV),
[`listLib.list_thm_database`](#listLib.list_thm_database),
[`listLib.X_LIST_CONV`](#listLib.X_LIST_CONV)
