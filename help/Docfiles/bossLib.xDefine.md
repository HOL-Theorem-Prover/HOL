## `xDefine`

``` hol4
bossLib.xDefine : string -> term quotation -> thm
```

------------------------------------------------------------------------

General-purpose function definition facility.

`xDefine` behaves exactly like `Define`, except that it takes an
alphanumeric string which is used as a stem for building names with
which to store the definition, associated induction theorem (if there is
one), and any auxiliary definitions used to construct the specified
function (if there are any) in the current theory segment.

### Failure

`xDefine` allows the definition of symbolic identifiers, but `Define`
doesn't. In all other respects, `xDefine` and `Define` succeed and fail
in the same way.

### Example

The following example shows how `Define` fails when asked to define a
symbolic identifier.

``` hol4
    - set_fixity ("/", Infixl 600);    (* tell the parser about "/" *)
    > val it = () : unit

    - Define
       `x/y = if y=0 then NONE else
              if x<y then SOME 0
               else OPTION_MAP SUC ((x-y)/y)`;

    Definition failed! Can't make name for storing definition
    because there is no alphanumeric identifier in:

       "/".

    Try "xDefine <alphanumeric-stem> <eqns-quotation>" instead.
```

Next the same definition is attempted with `xDefine`, supplying the name
for binding the definition and the induction theorem with in the current
theory.

``` hol4
    - xDefine "div"
         `x/y = if y=0 then NONE else
                if x<y then SOME 0
                 else OPTION_MAP SUC ((x-y)/y)`;

    Equations stored under "div_def".
    Induction stored under "div_ind".

    > val it =
        |- x / y =
           (if y = 0 then NONE
            else
             (if x < y then SOME 0
                       else OPTION_MAP SUC ((x - y) / y))) : thm
```

### Comments

`Define` can be thought of as an application of `xDefine`, in which the
stem is taken to be the name of the function being defined.

`bossLib.xDefine` is most commonly used. `TotalDefn.xDefine` is
identical to `bossLib.xDefine`, except that the `TotalDefn` structure
comes with less baggage---it depends only on `numLib` and `pairLib`.

### See also

[`bossLib.Define`](#bossLib.Define)
