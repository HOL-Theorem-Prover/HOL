## `LIST_CONV`

``` hol4
listLib.LIST_CONV : conv
```

------------------------------------------------------------------------

Proves theorems about list constants applied to `NIL`, `CONS`, `SNOC`,
`APPEND`, `FLAT` and `REVERSE`.

`LIST_CONV` takes a term of the form:

``` hol4
   CONST1 ... (CONST2 ...) ...
```

where `CONST1` and `CONST2` are operators on lists and `CONST2` returns
a list result. It can be one of `NIL`, `CONS`, `SNOC`, `APPEND`, `FLAT`
or `REVERSE`. The form of the resulting theorem depends on `CONST1` and
`CONST2`. Some auxiliary information must be provided about `CONST1`.
`LIST_CONV` maintains a database of such auxiliary information. It
initially holds information about the constants in the system. However,
additional information can be supplied by the user as new constants are
defined. The main information that is needed is a theorem defining the
constant in terms of `FOLDR` or `FOLDL`. The definition should have the
form:

``` hol4
   |- CONST1 ...l... = fold f e l
```

where `fold` is either `FOLDR` or `FOLDL`, `f` is a function, `e` a base
element and `l` a list variable. For example, a suitable theorem for
`SUM` is

``` hol4
   |- SUM l = FOLDR $+ 0 l
```

Knowing this theorem and given the term `“SUM (CONS x l)”`, `LIST_CONV`
returns the theorem:

``` hol4
   |- SUM (CONS x l) = x + (SUM l)
```

Other auxiliary theorems that are needed concern the terms `f` and `e`
found in the definition with respect to `FOLDR` or `FOLDL`. For example,
knowing the theorem:

``` hol4
   |- MONOID $+ 0
```

and given the term `“SUM (APPEND l1 l2)”`, `LIST_CONV` returns the
theorem

``` hol4
   |- SUM (APPEND l1 l2) = (SUM l1) + (SUM l2)
```

The following table shows the form of the theorem returned and the
auxiliary theorems needed if `CONST1` is defined in terms of `FOLDR`.

``` hol4
    CONST2       |  side conditions               | tm2 in result |- tm1 = tm2
   ==============|================================|===========================
   []            | NONE                           | e
   [x]           | NONE                           | f x e
   CONS x l      | NONE                           | f x (CONST1 l)
   SNOC x l      | e is a list variable           | CONST1 (f x e) l
   APPEND l1 l2  | e is a list variable           | CONST1 (CONST1 l1) l2
   APPEND l1 l2  | |- FCOMM g f, |- LEFT_ID g e   | g (CONST1 l1) (CONST2 l2)
   FLAT l1       | |- FCOMM g f, |- LEFT_ID g e,  |
                 | |- CONST3 l = FOLDR g e l      | CONST3 (MAP CONST1 l)
   REVERSE l     | |- COMM f, |- ASSOC f          | CONST1 l
   REVERSE l     | f == (\x l. h (g x) l)         |
                 | |- COMM h, |- ASSOC h          | CONST1 l
```

The following table shows the form of the theorem returned and the
auxiliary theorems needed if `CONST1` is defined in terms of `FOLDL`.

``` hol4
    CONST2       |  side conditions               | tm2 in result |- tm1 = tm2
   ==============|================================|===========================
   []            | NONE                           | e
   [x]           | NONE                           | f x e
   SNOC x l      | NONE                           | f x (CONST1 l)
   CONS x l      | e is a list variable           | CONST1 (f x e) l
   APPEND l1 l2  | e is a list variable           | CONST1 (CONST1 l1) l2
   APPEND l1 l2  | |- FCOMM f g, |- RIGHT_ID g e  | g (CONST1 l1) (CONST2 l2)
   FLAT l1       | |- FCOMM f g, |- RIGHT_ID g e, |
                 | |- CONST3 l = FOLDR g e l      | CONST3 (MAP CONST1 l)
   REVERSE l     | |- COMM f, |- ASSOC f          | CONST1 l
   REVERSE l     | f == (\l x. h l (g x))         |
                 | |- COMM h, |- ASSOC h          | CONST1 l
```

`|- MONOID f e` can be used instead of `|- FCOMM f f`, `|- LEFT_ID f` or
`|- RIGHT_ID f`. `|- ASSOC f` can also be used in place of
`|- FCOMM f f`.

Auxiliary theorems are held in a user-updatable database. In particular,
definitions of constants in terms of `FOLDR` and `FOLDL`, and monoid,
commutativity, associativity, left identity, right identity and binary
function commutativity theorems are stored. The database can be updated
by the user to allow `LIST_CONV` to prove theorems about new constants.
This is done by calling `set_list_thm_database`. The database can be
inspected by calling `list_thm_database`. The database initially holds
`FOLDR/L` theorems for the following system constants: `APPEND`, `FLAT`,
`LENGTH`, `NULL`, `REVERSE`, `MAP`, `FILTER`, `ALL_EL`, `SUM`,
`SOME_EL`, `IS_EL`, `AND_EL`, `OR_EL`, `PREFIX`, `SUFFIX`, `SNOC` and
`FLAT` combined with `REVERSE`. It also holds auxiliary theorems about
their step functions and base elements.

### Example

``` hol4
- LIST_CONV “LENGTH ([]:'a list)”;
|- LENGTH [] = 0


- LIST_CONV “APPEND (CONS h t) (l1:'a list)”;
|- APPEND (CONS h t) l1 = CONS h (APPEND t l1)


- LIST_CONV “APPEND (l1:'a list) (CONS h t)”;
|- APPEND l1 (CONS h t) = APPEND (SNOC h l1) t


- LIST_CONV “MAP (P:'a list -> 'a) (SNOC h t)”;
|- MAP P (SNOC h t) = SNOC (P h) (MAP P t)


- LIST_CONV “SUM (FLAT l)”;
|- SUM (FLAT l) = SUM (MAP SUM l)


- LIST_CONV “NULL (REVERSE (l:bool list))”;
|- NULL (REVERSE l) = NULL l
```

### Failure

`LIST_CONV tm` fails if `tm` is not of the form described above. It also
fails if no fold definition for `CONST1` is held in the databases, or if
the required auxiliary theorems, as described above, are not held in the
databases.

### See also

[`listLib.list_thm_database`](#listLib.list_thm_database),
[`listLib.PURE_LIST_CONV`](#listLib.PURE_LIST_CONV),
[`listLib.set_list_thm_database`](#listLib.set_list_thm_database),
[`listLib.X_LIST_CONV`](#listLib.X_LIST_CONV)
