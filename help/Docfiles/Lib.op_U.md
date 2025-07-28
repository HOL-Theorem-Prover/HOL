## `op_U` {#Lib.op_U}


```
op_U : ('a -> 'a -> bool) -> 'a list list -> 'a list
```



Takes the union of a list of sets, modulo the supplied relation.


An application `op_U eq [l1, ..., ln]` is equivalent to
`op_union eq l1 (... (op_union eq ln-1, ln)...)`. Thus,
every element that occurs in one of the lists will appear in the
result. However, if there are two elements `x` and `y` from different lists
such that `eq x y`, then only one of `x` and `y` will appear in the result.

### Failure

If an application of `eq` fails when applied to two elements from the lists.



### Example

    
    - op_U (fn x => fn y => x mod 2 = y mod 2)
           [[1,2,3], [4,5,6], [2,4,6,8,10]];
    > val it = [5, 2, 4, 6, 8, 10] : int list
    



### Comments

The order in which the elements occur in the resulting list should
not be depended upon.

A high-performance implementation of finite sets may be found in
structure `HOLset`.

There is no requirement that `eq` be recognizable as a kind of
equality (it could be implemented by an order relation, for example).

### See also

[`Lib.U`](#Lib.U), [`Lib.op_mem`](#Lib.op_mem), [`Lib.op_insert`](#Lib.op_insert), [`Lib.op_union`](#Lib.op_union), [`Lib.op_mk_set`](#Lib.op_mk_set), [`Lib.op_intersect`](#Lib.op_intersect), [`Lib.op_set_diff`](#Lib.op_set_diff)

