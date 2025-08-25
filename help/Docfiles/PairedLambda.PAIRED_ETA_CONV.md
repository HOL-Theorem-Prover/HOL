## `PAIRED_ETA_CONV`

``` hol4
PairedLambda.PAIRED_ETA_CONV : conv
```

------------------------------------------------------------------------

Performs generalized eta conversion for tupled eta-redexes.

The conversion `PAIRED_ETA_CONV` generalizes `ETA_CONV` to eta-redexes
with tupled abstractions.

``` hol4
   PAIRED_ETA_CONV   \(v1..(..)..vn). f (v1..(..)..vn)
    = |- \(v1..(..)..vn). f (v1..(..)..vn) = f
```

### Failure

Fails unless the given term is a paired eta-redex as illustrated above.

### Comments

Note that this result cannot be achieved by ordinary eta-reduction
because the tupled abstraction is a surface syntax for a term which does
not correspond to a normal pattern for eta reduction. Taking the term
apart reveals the true form of a paired eta redex:

``` hol4
   - dest_comb (Term `\(x:num,y:num). FST (x,y)`)
   > val it = (`UNCURRY`, `\x y. FST (x,y)`) : term * term
```

### Example

The following is a typical use of the conversion:

``` hol4
   val SELECT_PAIR_EQ = Q.prove
    (`(@(x:'a,y:'b). (a,b) = (x,y)) = (a,b)`,
     CONV_TAC (ONCE_DEPTH_CONV PairedLambda.PAIRED_ETA_CONV) THEN
     ACCEPT_TAC (SYM (MATCH_MP SELECT_AX (REFL (Term `(a:'a,b:'b)`)))));
```

### See also

[`Drule.ETA_CONV`](#Drule.ETA_CONV)
