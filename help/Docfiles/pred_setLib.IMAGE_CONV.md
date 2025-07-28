## `IMAGE_CONV` {#pred_setLib.IMAGE_CONV}


```
IMAGE_CONV : conv -> conv -> conv
```



Compute the image of a function on a finite set.


The function `IMAGE_CONV` is a parameterized conversion for computing the image
of a function `f:ty1->ty2` on a finite set `{t1;...;tn}` of type
`ty1->bool`.  The first argument to `IMAGE_CONV` is expected to be a conversion
that computes the result of applying the function `f` to each element of this
set. When applied to a term `f ti`, this conversion should return a theorem
of the form `|- (f ti) = ri`, where `ri` is the result of applying the function
`f` to the element `ti`.  This conversion is used by `IMAGE_CONV` to compute a
theorem of the form
    
       |- IMAGE f {t1;...;tn} = {r1;...;rn}
    
The second argument to `IMAGE_CONV` is used (optionally) to simplify
the resulting image set `{r1;...;rn}` by removing redundant occurrences of
values.  This conversion expected to decide equality of values of the result
type `ty2`; given an equation `e1 = e2`, where `e1` and `e2` are terms of
type `ty2`, the conversion should return either `|- (e1 = e2) = T` or
`|- (e1 = e2) = F`, as appropriate.

Given appropriate conversions `conv1` and `conv2`, the function `IMAGE_CONV`
returns a conversion that maps a term of the form `IMAGE f {t1;...;tn}` to
the theorem
    
       |- IMAGE f {t1;...;tn} = {rj;...;rk}
    
where `conv1` proves a theorem of the form `|- (f ti) = ri` for each
element `ti` of the set `{t1;...;tn}`, and where the set `{rj;...;rk}` is
the smallest subset of `{r1;...;rn}` such no two elements are
alpha-equivalent and `conv2` does not map `rl = rm` to the theorem
`|- (rl = rm) = T` for any pair of values `rl` and `rm` in `{rj;...;rk}`.
That is, `{rj;...;rk}` is the set obtained by removing multiple occurrences
of values from the set `{r1;...;rn}`, where the equality conversion `conv2`
(or alpha-equivalence) is used to determine which pairs of terms in
`{r1;...;rn}` are equal.

### Example

The following is a very simple example in which `REFL` is used to construct the
result of applying the function `f` to each element of the set `{1; 2; 1; 4}`,
and `NO_CONV` is the supplied ‘equality conversion’.
    
       - IMAGE_CONV REFL NO_CONV ``IMAGE (f:num->num) {1; 2; 1; 4}``;
       > val it = |- IMAGE f {1; 2; 1; 4} = {f 2; f 1; f 4} : thm
    
The result contains only one occurrence of `f 1`, even though
`NO_CONV` always fails, since `IMAGE_CONV` simplifies the resulting set by
removing elements that are redundant up to alpha-equivalence.

For the next example, we construct a conversion that maps `SUC n` for any
numeral `n` to the numeral standing for the successor of `n`.
    
       - fun SUC_CONV tm =
          let open numLib Arbnum
              val n = dest_numeral (rand tm)
              val sucn = mk_numeral (n + one)
          in
            SYM (num_CONV sucn)
          end;
    
       > val SUC_CONV = fn : term -> thm
    
The result is a conversion that inverts `num_CONV`:
    
       - numLib.num_CONV ``4``;
       > val it = |- 4 = SUC 3 : thm
    
       - SUC_CONV ``SUC 3``;
       > val it = |- SUC 3 = 4 : thm
    
The conversion `SUC_CONV` can then be used to compute the image
of the successor function on a finite set:
    
       - IMAGE_CONV SUC_CONV NO_CONV ``IMAGE SUC {1; 2; 1; 4}``;
       > val it = |- IMAGE SUC {1; 2; 1; 4} = {3; 2; 5} : thm
    
Note that `2` (= `SUC 1`) appears only once in the resulting set.

Finally, here is an example of using `IMAGE_CONV` to compute the image of a
paired addition function on a set of pairs of numbers:
    
       - IMAGE_CONV (pairLib.PAIRED_BETA_CONV THENC reduceLib.ADD_CONV)
                    numLib.REDUCE_CONV
                ``IMAGE (\(n,m).n+m) {{(1,2), (3,4), (0,3), (1,3)}}``;
       > val it = |- IMAGE (\(n,m). n + m) {(1,2); (3,4); (0,3); (1,3)} = {7; 3; 4}
    

### Failure

`IMAGE_CONV conv1 conv2` fails if applied to a term not of the form
`IMAGE f {t1;...;tn}`.  An application of `IMAGE_CONV conv1 conv2` to
a term `IMAGE f {t1;...;tn}` fails unless for all `ti` in the set
`{t1;...;tn}`, evaluating ``` conv1 ``f ti`` ``` returns `|- (f ti) = ri`
for some `ri`.
