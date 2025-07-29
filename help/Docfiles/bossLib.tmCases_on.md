## `tmCases_on`

``` hol4
bossLib.tmCases_on : term -> string list -> tactic
```

------------------------------------------------------------------------

Begins a "cases" proof on the provided term

A call to `tmCases_on t names` will do the equivalent of a
`FULL_STRUCT_CASES_TAC` on the term `t`, using the cases (or "nchotomy")
theorem stored in the `TypeBase` for `t`'s type. If the `names` list is
not empty, the names encoded there will be used to give names to any
existentially quantified names in the cases theorem. Each element of the
`names` list corresponds to the cases of the theorem, and, as
constructors may take multiple arguments, each corresponding to an
existentially quantified variable, the element is itself a list of
names, separated by spaces. For example, the cases theorem for lists
could be passed a string list of the form `["", "head tail"]`. If the
`names` is empty, then the system will choose names for the
existentially quantified variables.

As a convenience, if the term argument is a variable, and there are
variables of that name free in the goal, or bound by top-level universal
quantifiers in the goal's conclusion, then the type of the variable is
ignored and its name is used to generate the argument to the tactic. If
a goal has multiple variables of the same name (always a bad idea!) the
choice of variable is unspecified.

### Failure

Fails if the term is not of a type occurring in the `TypeBase`.

### Example

Note how in this example, the parser will give the argument `l` bare
type `“:α”`, but it still picks the appropriately instantiated list
cases theorem for the `l` that appears in the goal, which may have type
`“:num list”`, for example.

``` hol4
            ?- MAP f l = []
   =========================================   tmCases_on “l” ["", "e es"]
   ?- MAP f [] = []    ?- MAP f (e::es) = []
```

### See also

[`bossLib.Cases_on`](#bossLib.Cases_on),
[`Tactic.FULL_STRUCT_CASES_TAC`](#Tactic.FULL_STRUCT_CASES_TAC)
