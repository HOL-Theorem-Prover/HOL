## `op_insert` {#Lib.op_insert}


```
op_insert ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
```



Add an element to a list if it is not already there.


If there exists an element `y` in `list`, such that `eq x y`,
then `insert eq x list` equals `list`. Otherwise, `x` is added to `list`.

### Failure

Never fails.

### Example

    
    - op_insert (fn x => fn y => x = y mod 2) 1 [3,2];
    > val it = [3, 2] : int list
    
    - op_insert aconv (Term `\x. x /\ y`)
                      [T, Term `\z. z /\ y`, F];
    > val it = [`T`, `\z. z /\ y`, `F`] : term list
    
    - op_insert aconv (Term `\x. x /\ y`)
                      [T, Term `\z. z /\ a`, F];
    > val it = [`\x. x /\ y`, `T`, `\z. z /\ a`, `F`] : term list
    



### Comments

There is no requirement that `eq` be recognizable as a kind of
equality (it could be implemented by an order relation, for example).

One should not write code that depends on the arrangement of elements in
the result.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

### See also

[`Lib.insert`](#Lib.insert), [`Lib.op_mem`](#Lib.op_mem), [`Lib.op_union`](#Lib.op_union), [`Lib.op_mk_set`](#Lib.op_mk_set), [`Lib.op_U`](#Lib.op_U), [`Lib.op_intersect`](#Lib.op_intersect), [`Lib.op_set_diff`](#Lib.op_set_diff)

