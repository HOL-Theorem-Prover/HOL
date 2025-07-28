## `free_in` {#Term.free_in}


```
free_in : term -> term -> bool
```



Tests if one term is free in another.


When applied to two terms `t1` and `t2`, the function `free_in` returns
`true` if `t1` is free in `t2`, and `false` otherwise. It is not necessary
that `t1` be simply a variable. A term `M` occurs free in `N` when there
is some occurrence of `M` in `N` such that each free variable of `M` in
that occurrence is not bound by a binder in `N`.

### Failure

Never fails.

### Example

In the following example `free_in` returns `false` because the `x` in `SUC x`
in the second term is bound:
    
       - free_in ``SUC x`` ``!x. SUC x = x + 1``;
       > val it = false : bool
    
whereas the following call returns `true` because the first instance
of `x` in the second term is free, even though there is also a bound instance:
    
       - free_in ``x:bool`` ``!y. x /\ ?x. x = y``;
       > val it = true : bool
    



### See also

[`Term.free_vars`](#Term.free_vars), [`Term.FVL`](#Term.FVL)

