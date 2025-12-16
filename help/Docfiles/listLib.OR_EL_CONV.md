## `OR_EL_CONV`

``` hol4
listLib.OR_EL_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of taking the disjunction of the
elements of a boolean list.

For any object language list of the form `“[x1;x2;...;xn]”`, where `x1`,
`x2`, ..., `xn` are boolean expressions, the result of evaluating

``` hol4
   OR_EL_CONV “OR_EL [x1;x2;...;xn]”
```

is the theorem

``` hol4
   |- OR_EL [x1;x2;...;xn] = b
```

where `b` is either the boolean constant that denotes the disjunction of
the elements of the list, or a disjunction of those `xi` that are not
boolean constants.

### Example

``` hol4
- OR_EL_CONV “OR_EL [T;F;F;T]”;
|- OR_EL [T;F;F;T] = T


- OR_EL_CONV “OR_EL [F;F;F]”;
|- OR_EL [F;F;F] = F


- OR_EL_CONV “OR_EL [F;x;y]”;
|- OR_EL [F; x; y] = x \/ y


- OR_EL_CONV “OR_EL [x;T;y]”;
|- OR_EL [x; T; y] = T
```

### Failure

`OR_EL_CONV tm` fails if `tm` is not of the form described above.
