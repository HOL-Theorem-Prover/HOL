## `ty_antiq` {#Parse.ty_antiq}


```
ty_antiq : hol_type -> term
```



Make a variable named `ty_antiq`.


Given a type `ty`, the ML invocation `ty_antiq ty` returns the HOL variable
`ty_antiq : ty`. This provides a way to antiquote types into terms,
which is necessary because the HOL term parser only allows terms to
be antiquoted. The use of `ty_antiq` promotes a type to a term variable
which can be antiquoted. The HOL parser detects occurrences of
`ty_antiq ty` and inserts `ty` as a constraint.

### Example

Suppose we want to constrain a term to have type `num list`, which is
bound to ML value `ty`. Attempting to antiquote ty directly into the
term won’t work:
    
    val ty = ``:num list``;
    > val ty = `:num list` : hol_type
    
    - ``x : ^ty``;
    ! Toplevel input:
    ! Term `x : ^ty`;
    !            ^^
    ! Type clash: expression of type
    !   hol_type
    ! cannot have type
    !   term
    
Use of `ty_antiq` solves the problem:
    
    - ``x : ^(ty_antiq ty)``;
    > val it = `x` : term
    
    - type_of it;
    > val it = `:num list` : hol_type
    

### See also

[`Parse.Term`](#Parse.Term)

