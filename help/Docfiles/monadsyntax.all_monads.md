## `all_monads`

``` hol4
monadsyntax.all_monads :
  unit ->
  (string *
   {bind : term, unit : term, ignorebind : term option,
    choice : term option, fail : term option, guard : term option}) list
```

------------------------------------------------------------------------

Lists all declared monads

Returns a list of all declared monad types. These can be enabled with
calls to `enable_monad`.

### Failure

Never fails.

### Example

``` hol4
> all_monads();
val it =
   [("list",
     {bind = “LIST_BIND”, choice = SOME (“$++”), fail = SOME (“[]”),
      guard = SOME (“LIST_GUARD”), ignorebind = SOME (“LIST_IGNORE_BIND”),
      unit = “λx. [x]”}),
    ("option",
     {bind = “OPTION_BIND”, choice = SOME (“OPTION_CHOICE”),
      fail = SOME (“NONE”), guard = SOME (“OPTION_GUARD”),
      ignorebind = SOME (“OPTION_IGNORE_BIND”), unit = “SOME”})]:
   (string * monadinfo) list
```

### See also

[`monadsyntax.declare_monad`](#monadsyntax.declare_monad),
[`monadsyntax.enable_monad`](#monadsyntax.enable_monad)
