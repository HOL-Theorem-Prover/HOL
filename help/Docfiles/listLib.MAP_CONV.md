## `MAP_CONV`

``` hol4
listLib.MAP_CONV : conv -> conv
```

------------------------------------------------------------------------

Compute the result of mapping a function down a list.

The function `MAP_CONV` is a parameterized conversion for computing the
result of mapping a function `f:ty1->ty2` down a list `“[t1;...;tn]”` of
elements of type `ty1`. The first argument to `MAP_CONV` is expected to
be a conversion that computes the result of applying the function `f` to
an element of this list. When applied to a term `“f ti”`, this
conversion should return a theorem of the form `|- (f ti) = ri`, where
`ri` is the result of applying the function `f` to the element `ti`.

Given an appropriate `conv`, the conversion `MAP_CONV conv` takes a term
of the form `“MAP f [t1;...;tn]”` to the theorem

``` hol4
   |- MAP f [t1;...;tn] = [r1;...;rn]
```

where `conv “f ti”` returns `|- (f ti) = ri` for `i` from `1` to `n`.

### Example

The following is a very simple example in which no computation is done
for applications of the function being mapped down a list:

``` hol4
   - MAP_CONV ALL_CONV “MAP SUC [1;2;1;4]”;
   |- MAP SUC[1;2;1;4] = [SUC 1;SUC 2;SUC 1;SUC 4]
```

The result just contains applications of `SUC`, since the supplied
conversion `ALL_CONV` does no evaulation.

We now construct a conversion that maps `SUC n` for any numeral `n` to
the numeral standing for the successor of `n`:

``` hol4
   - fun SUC_CONV tm =
        let val n = string_to_int(#Name(dest_const(rand tm)))
            val sucn = mk_const{{Name =int_to_string(n+1), Ty=(==`:num`==)}}
         in
            SYM (num_CONV sucn)
         end;
   SUC_CONV = - : conv
```

The result is a conversion that inverts `num_CONV`:

``` hol4
   - num_CONV “4”;
   |- 4 = SUC 3

   - SUC_CONV “SUC 3”;
   |- SUC 3 = 4
```

The conversion `SUC_CONV` can then be used to compute the result of
mapping the successor function down a list of numerals:

``` hol4
   - MAP_CONV SUC_CONV “MAP SUC [1;2;1;4]”;
   |- MAP SUC[1;2;1;4] = [2;3;2;5]
```

### Failure

`MAP_CONV conv` fails if applied to a term not of the form
`“MAP f [t1;...;tn]”`. An application of `MAP_CONV conv` to a term
`“MAP f [t1;...;tn]”` fails unless for all `ti` in the list
`[t1;...;tn]`, evaluating `conv “f ti”` returns `|- (f ti) = ri` for
some `ri`.
