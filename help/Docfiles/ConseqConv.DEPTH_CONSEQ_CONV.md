## `DEPTH_CONSEQ_CONV`

``` hol4
ConseqConv.DEPTH_CONSEQ_CONV : directed_conseq_conv -> directed_conseq_conv
```

------------------------------------------------------------------------

Applies a consequence conversion repeatedly to all the sub-terms of a
term, in top-down order.

`DEPTH_CONSEQ_CONV c tm` tries to apply the given conversion at
toplevel. If this fails, it breaks the term `tm` down into boolean
subterms. It can break up the following operators: `/\`, `\/`, `~`,
`==>` and quantification. Then it applies the directed consequence
conversion `c` to terms and iterates. Finally, it puts everything
together again.

Notice that some operators switch the direction that is passed to `c`,
e.g. to strengthen a term `~t`, `DEPTH_CONSEQ_CONV` tries to weaken `t`.

### Example

Consider the expression `FEVERY P (f |+ (x1, y1) |+ (x2,y2))`. It states
that all elements of the finite map `f |+ (x1, y1) |+ (x2, y2)` satisfy
the predicate `P`. However, the definition of `x1` and `x2` possible
hide definitions of these keys inside `f` or in case `x1 = x2` the
middle update is void. You easily get into a lot of aliasing problems
while proving thus a statement. However, the following theorem holds:

``` hol4
   |- !f x y. FEVERY P (f |+ (x,y)) /\ P (x,y) ==> FEVERY P (f |+ (x,y))
```

Given a directed consequence conversion `c` that instantiates this
theorem, DEPTH_CONSEQ_CONV can be used to apply it repeatedly and at
substructures as well:

``` hol4
  DEPTH_CONSEQ_CONV c CONSEQ_CONV_STRENGTHEN_direction
     ``!y2. FEVERY P (f |+ (x1, y1) |+ (x2,y2)) /\ Q z`` =


  |- (!y2. FEVERY P f /\ P (x1, y1) /\ P (x2,y2) /\ Q z) ==>
     (!y2. FEVERY P (f |+ (x1, y1) |+ (x2,y2)) /\ Q z)
```

### See also

[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV),
[`ConseqConv.ONCE_DEPTH_CONSEQ_CONV`](#ConseqConv.ONCE_DEPTH_CONSEQ_CONV),
[`ConseqConv.NUM_DEPTH_CONSEQ_CONV`](#ConseqConv.NUM_DEPTH_CONSEQ_CONV),
[`ConseqConv.DEPTH_STRENGTHEN_CONSEQ_CONV`](#ConseqConv.DEPTH_STRENGTHEN_CONSEQ_CONV),
[`ConseqConv.REDEPTH_CONSEQ_CONV`](#ConseqConv.REDEPTH_CONSEQ_CONV)
