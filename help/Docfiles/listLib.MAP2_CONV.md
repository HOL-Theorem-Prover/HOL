## `MAP2_CONV`

``` hol4
listLib.MAP2_CONV : conv -> conv
```

------------------------------------------------------------------------

Compute the result of mapping a binary function down two lists.

The function `MAP2_CONV` is a conversion for computing the result of
mapping a binary function `f:ty1->ty2->ty3` down two lists
`“[l11;...;l1n]”` whose elements are of type `ty1` and `“[l21;...;l2n]”`
whose elements are of type `ty2`. The lengths of the two lists must be
identical. The first argument to `MAP2_CONV` is expected to be a
conversion that computes the result of applying the function `f` to a
pair of corresponding elements of these lists. When applied to a term
`“f l1i l2i”`, this conversion should return a theorem of the form
`|- (f l1i l2i) = ri`, where `ri` is the result of applying the function
`f` to the elements `l1i` and `l2i`.

Given an appropriate `conv`, the conversion `MAP2_CONV conv` takes a
term of the form `“MAP2 f [l11;...;dl2tn] [l21;...;l2n]”` and returns
the theorem

``` hol4
   |- MAP2 f [l11;...;l1n] [l21;...;l2n] = [r1;...;rn]
```

where `conv “f l1i l2i”` returns `|- (f l1i l2i) = ri` for `i` from `1`
to `n`.

### Example

The following is a very simple example in which the corresponding
elements from the two lists are summed to form the resulting list:

``` hol4
   - load_library_in_place num_lib;
   - MAP2_CONV Num_lib.ADD_CONV “MAP2 $+ [1;2;3] [1;2;3]”;
   |- MAP2 $+ [1;2;3] [1;2;3] = [2;4;6]
```

### Failure

`MAP2_CONV conv` fails if applied to a term not of the form described
above. An application of `MAP2_CONV conv` to a term
`“MAP2 f [l11;...;l1n] [l21;...;l2n]”` fails unless for all `i` where
`1<=i<=n` evaluating `conv “f l1i l2i”` returns `|- (f l1i l2i) = ri`
for some `ri`.

### See also

[`listLib.MAP_CONV`](#listLib.MAP_CONV)
