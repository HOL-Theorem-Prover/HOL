## `PURE_LIST_CONV` {#listLib.PURE_LIST_CONV}


```
PURE_LIST_CONV : {{Aux_thms: thm list, Fold_thms: thm list}} -> conv
```



Proves theorems about list constants applied to `NIL`, `CONS`, `SNOC`,
`APPEND`, `FLAT` and `REVERSE`.


`PURE_LIST_CONV` takes a term of the form:
    
       CONST1 ... (CONST2 ...) ...
    
where `CONST1` and `CONST2` are operators on lists and `CONST2`
returns a list result. It can be one of `NIL`, `CONS`, `SNOC`, `APPEND`,
`FLAT` or `REVERSE`. The form of the resulting theorem depends on `CONST1` and
`CONST2`. Some auxiliary theorems must be provided about `CONST1`.
`PURE_LIST_CONV`. These are passed as a record argument.
The `Fold_thms` field of the record should hold a theorem defining the constant
in terms of `FOLDR` or `FOLDL`. The definition should have the form:
    
       |- CONST1 ...l... = fold f e l
    
where `fold` is either `FOLDR` or `FOLDL`, `f` is a function, `e` a
base element and `l` a list variable. For example, a suitable theorem for
`SUM` is
    
       |- SUM l = FOLDR $+ 0 l
    
Given this theorem, no auxiliary theorems and the term
`“SUM (CONS x l)”`, a call to `PURE_LIST_CONV` returns the theorem:
    
       |- SUM (CONS x l) = x + (SUM l)
    
The `Aux_thms` field of the record argument to `PURE_LIST_CONV` provides
auxiliary theorems concerning the terms `f` and `e` found in the definition
with respect to `FOLDR` or `FOLDL`. For example, given the theorem:
    
       |- MONOID $+ 0
    
and given the term `“SUM (APPEND l1 l2)”`, a call to
`PURE_LIST_CONV` returns the theorem
    
       |- SUM (APPEND l1 l2) = (SUM l1) + (SUM l2)
    
The following table shows the form of the theorem returned and the
auxiliary theorems needed if `CONST1` is defined in terms of `FOLDR`.
    
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
    
The following table shows the form of the theorem returned and the
auxiliary theorems needed if `CONST1` is defined in terms of `FOLDL`.
    
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
    
`|- MONOID f e` can be used instead of  `|- FCOMM f f`,
`|- LEFT_ID f` or `|- RIGHT_ID f`. `|- ASSOC f` can also be used in place of
`|- FCOMM f f`.

### Example

    
    - val SUM_FOLDR = theorem "list" "SUM_FOLDR";
    val SUM_FOLDR = |- !l. SUM l = FOLDR $+ 0 l
    - PURE_LIST_CONV
    =    {{Fold_thms = [SUM_FOLDR], Aux_thms = []}} “SUM (CONS h t)”;
    |- SUM (CONS h t) = h + SUM t
    
    
    - val SUM_FOLDL = theorem "list" "SUM_FOLDL";
    val SUM_FOLDL = |- !l. SUM l = FOLDL $+ 0 l
    - PURE_LIST_CONV
    =    {{Fold_thms = [SUM_FOLDL], Aux_thms = []}} “SUM (SNOC h t)”;
    |- SUM (SNOC h t) = SUM t + h
    
    
    - val MONOID_ADD_0 = theorem "arithmetic" "MONOID_ADD_0";
    val MONOID_ADD_0 = |- MONOID $+ 0
    - PURE_LIST_CONV
    =    {{Fold_thms = [SUM_FOLDR], Aux_thms = [MONOID_ADD_0]}}
    =    “SUM (APPEND l1 l2)”;
    |- SUM (APPEND l1 l2) = SUM l1 + SUM l2
    
    
    - PURE_LIST_CONV
    =    {{Fold_thms = [SUM_FOLDR], Aux_thms = [MONOID_ADD_0]}} “SUM (FLAT l)”;
    |- SUM (FLAT l) = SUM (MAP SUM l)
    

### Failure

`PURE_LIST_CONV tm` fails if `tm` is not of the form described above. It also
fails if no suitable fold definition for `CONST1` is supplied, or if the
required auxiliary theorems as described above are not supplied.

### See also

[`listLib.LIST_CONV`](#listLib.LIST_CONV), [`listLib.X_LIST_CONV`](#listLib.X_LIST_CONV)

