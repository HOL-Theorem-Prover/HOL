## `topsort` {#Lib.topsort}


```
topsort : ('a -> 'a -> bool) -> 'a list -> 'a list
```



Topologically sorts a list using a given partial order relation.


The call `topsort opr list` where `opr` is a curried partial order
on the elements of `list`, will topologically sort the list, i.e.,
will permute it such that if `x opr y` then `x` will occur to the left
of `y` in the resulting list.

### Failure

If `opr` fails when applied to `x` and `y` in `list`. Also, `topsort`
will fail if there is a chain of elements `x1,...,xn`, all in `list`, such
that `opr x_1 x_2`, ..., `opr xn x1`. This displays a cyclic dependency.

### Example

The following call arranges a list of terms in subterm order:
    
       - fun is_subterm x y = Lib.can (find_term (aconv x)) y;
       > val is_subterm = fn : term -> term -> bool
    
       - topsort is_subterm
         [``x+1``, ``x:num``, ``y + (x + 1)``, ``y + x``, ``y + x + z``, ``y:num``];
       > val it = [``y``, ``x``, ``x + 1``, ``y + x``, ``y + x + z``, ``y + (x + 1)``] : term list
    

### See also

[`Lib.sort`](#Lib.sort)

