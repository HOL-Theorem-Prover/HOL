## `AND_EL_CONV`

``` hol4
listLib.AND_EL_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of taking the conjunction of the
elements of a boolean list.

For any object language list of the form `“[x1;x2;...;xn]”`, where `x1`,
`x2`, ..., `xn` are boolean expressions, the result of evaluating

``` hol4
   AND_EL_CONV “AND_EL [x1;x2;...;xn]”
```

is the theorem

``` hol4
   |- AND_EL [x1;x2;...;xn] = b
```

where `b` is either the boolean constant that denotes the conjunction of
the elements of the list, or a conjunction of those `xi` that are not
boolean constants.

### Example

``` hol4
- AND_EL_CONV “AND_EL [T;F;F;T]”;
|- AND_EL [T;F;F;T] = F


- AND_EL_CONV “AND_EL [T;T;T]”;
|- AND_EL [T;T;T] = T


- AND_EL_CONV “AND_EL [T;x;y]”;
|- AND_EL [T; x; y] = x /\ y


- AND_EL_CONV “AND_EL [x;F;y]”;
|- AND_EL [x; F; y] = F
```

### Failure

`AND_EL_CONV tm` fails if `tm` is not of the form described above.
