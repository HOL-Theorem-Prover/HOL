## `PSKOLEM_CONV`

``` hol4
PairRules.PSKOLEM_CONV : conv
```

------------------------------------------------------------------------

Proves the existence of a pair of Skolem functions.

When applied to an argument of the form `!p1...pn. ?q. tm`, the
conversion `PSKOLEM_CONV` returns the theorem:

``` hol4
   |- (!p1...pn. ?q. tm) = (?q'. !p1...pn. tm[q' p1 ... pn/yq)
```

where `q'` is a primed variant of the pair `q` not free in the input
term.

### Failure

`PSKOLEM_CONV tm` fails if `tm` is not a term of the form
`!p1...pn. ?q. tm`.

### Example

Both `q` and any `pi` may be a paired structure of variables:

``` hol4
   - PSKOLEM_CONV
      (Term `!(x11:'a,x12:'a) (x21:'a,x22:'a).
             ?(y1:'a,y2:'a). tm x11 x12 x21 x21 y1 y2`);

   > val it =
    |- (!(x11,x12) (x21,x22). ?(y1,y2). tm x11 x12 x21 x21 y1 y2) =
       ?(y1,y2).
         !(x11,x12) (x21,x22).
           tm x11 x12 x21 x21 (y1 (x11,x12) (x21,x22)) (y2 (x11,x12) (x21,x22))
     : thm
```

### See also

[`Conv.SKOLEM_CONV`](#Conv.SKOLEM_CONV),
[`PairRules.P_PSKOLEM_CONV`](#PairRules.P_PSKOLEM_CONV)
